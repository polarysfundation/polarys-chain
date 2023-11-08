package zephyria

import (
	"bytes"
	"context"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"math"
	"math/big"
	mrand "math/rand"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/ethereum/go-ethereum"
	"github.com/ethereum/go-ethereum/accounts"
	"github.com/ethereum/go-ethereum/accounts/abi"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/gopool"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/misc/eip1559"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/forkid"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/systemcontracts"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/internal/ethapi"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/rpc"
	"github.com/ethereum/go-ethereum/trie"
	lru "github.com/hashicorp/golang-lru"
	"golang.org/x/crypto/sha3"
)

const (
	inMemorySnapshots  = 128  // Number of recent snapshots to keep in memory
	inMemorySignatures = 4096 // Number of recent block signatures to keep in memory

	checkpointInterval = 1024          // Number of blocks after which to save the snapshot to the database
	defaultEpochLength = uint64(30000) // Default number of blocks of checkpoint to update validatorSet from contract

	extraVanity      = 32 // Fixed number of extra-data prefix bytes reserved for signer vanity
	extraSeal        = 65 // Fixed number of extra-data suffix bytes reserved for signer seal
	nextForkHashSize = 4  // Fixed number of extra-data suffix bytes reserved for nextForkHash.

	validatorBytesLength = common.AddressLength
	wiggleTime           = uint64(1) // second, Random delay (per signer) to allow concurrent signers
	initialBackOffTime   = uint64(1) // second
	processBackOffTime   = uint64(1) // second
	systemRewardPercent  = 4
)

var (
	maxSystemBalance  = new(big.Int).Mul(big.NewInt(100), big.NewInt(params.Ether))
	ForkedBlockReward = big.NewInt(1.e+17)
	uncleHash         = types.CalcUncleHash(nil) // Always Keccak256(RLP([])) as uncles are meaningless outside ocommon
	diffInTurn        = big.NewInt(2)            // Block difficulty for in-turn signatures
	diffNoTurn        = big.NewInt(1)            // Block difficulty for out-of-turn signatures

	systemContracts = map[common.Address]bool{
		common.HexToAddress(systemcontracts.ValidatorController):  true,
		common.HexToAddress(systemcontracts.SlashContract):        true,
		common.HexToAddress(systemcontracts.SystemRewardContract): true,
		common.HexToAddress(systemcontracts.PolarysLightclient):   true,
		common.HexToAddress(systemcontracts.RelayerHubContract):   true,
		common.HexToAddress(systemcontracts.ValidatorHub):         true,
		common.HexToAddress(systemcontracts.GovHubContract):       true,
		common.HexToAddress(systemcontracts.StakingSystem):        true,
		common.HexToAddress(systemcontracts.StakingDelegator):     true,
		common.HexToAddress(systemcontracts.FsPRY):                true,
	}
)

var (
	// errUnknownBlock is returned when the list of validators is requested for a block
	// that is not part of the local blockchain.
	errUnknownBlock = errors.New("unknown block")

	// errMissingVanity is returned if a block's extra-data section is shorter than
	// 32 bytes, which is required to store the signer vanity.
	errMissingVanity = errors.New("extra-data 32 byte vanity prefix missing")

	// errMissingSignature is returned if a block's extra-data section doesn't seem
	// to contain a 65 byte secp256k1 signature.
	errMissingSignature = errors.New("extra-data 65 byte signature suffix missing")

	// errExtraValidators is returned if non-sprint-end block contain validator data in
	// their extra-data fields.
	errExtraValidators = errors.New("non-sprint-end block contains extra validator list")

	// errInvalidSpanValidators is returned if a block contains an
	// invalid list of validators (i.e. non divisible by 20 bytes).
	errInvalidSpanValidators = errors.New("invalid validator list on sprint end block")

	// errInvalidMixDigest is returned if a block's mix digest is non-zero.
	errInvalidMixDigest = errors.New("non-zero mix digest")

	// errInvalidUncleHash is returned if a block contains an non-empty uncle list.
	errInvalidUncleHash = errors.New("non empty uncle hash")

	// errMismatchingEpochValidators is returned if a sprint block contains a
	// list of validators different than the one the local node calculated.
	errMismatchingEpochValidators = errors.New("mismatching validator list on epoch block")

	// errInvalidDifficulty is returned if the difficulty of a block is missing.
	errInvalidDifficulty = errors.New("invalid difficulty")

	// errWrongDifficulty is returned if the difficulty of a block doesn't match the
	// turn of the signer.
	errWrongDifficulty = errors.New("wrong difficulty")

	// errOutOfRangeChain is returned if an authorization list is attempted to
	// be modified via out-of-range or non-contiguous headers.
	errOutOfRangeChain = errors.New("out of range or non-contiguous chain")

	// errBlockHashInconsistent is returned if an authorization list is attempted to
	// insert an inconsistent block.
	errBlockHashInconsistent = errors.New("the block hash is inconsistent")

	// errUnauthorizedValidator is returned if a header is signed by a non-authorized entity.
	errUnauthorizedValidator = func(val string) error {
		return errors.New("unauthorized validator: " + val)
	}
	// errCoinBaseMisMatch is returned if a header's coinbase do not match with signature
	errCoinBaseMisMatch = errors.New("coinbase do not match with signature")

	// errRecentlySigned is returned if a header is signed by an authorized entity
	// that already signed a header recently, thus is temporarily not allowed to.
	errRecentlySigned = errors.New("recently signed")
)

// SignerFn is a signer callback function to request a header to be signed by a
// backing account.
type SignerFn func(accounts.Account, string, []byte) ([]byte, error)
type SignerTxFn func(accounts.Account, *types.Transaction, *big.Int) (*types.Transaction, error)

func isToSystemContract(to common.Address) bool {
	return systemContracts[to]
}

// ecrecover extracts the Ethereum account address from a signed header.
func ecrecover(header *types.Header, sigCache *lru.ARCCache, chainId *big.Int) (common.Address, error) {
	// If the signature's already cached, return that
	hash := header.Hash()
	if address, known := sigCache.Get(hash); known {
		return address.(common.Address), nil
	}
	// Retrieve the signature from the header extra-data
	if len(header.Extra) < extraSeal {
		return common.Address{}, errMissingSignature
	}
	signature := header.Extra[len(header.Extra)-extraSeal:]

	// Recover the public key and the Ethereum address
	pubkey, err := crypto.Ecrecover(SealHash(header, chainId).Bytes(), signature)
	if err != nil {
		return common.Address{}, err
	}
	var signer common.Address
	copy(signer[:], crypto.Keccak256(pubkey[1:])[12:])

	sigCache.Add(hash, signer)
	return signer, nil
}

func ZephyriaRLP(header *types.Header, chainId *big.Int) []byte {
	b := new(bytes.Buffer)
	encodeSigHeader(b, header, chainId)
	return b.Bytes()
}

type Zephyria struct {
	chainConfig *params.ChainConfig
	config      *params.ZephyriaConfig
	genesisHash common.Hash
	db          ethdb.Database

	recentSnaps *lru.ARCCache
	signatures  *lru.ARCCache

	signer types.Signer

	val      common.Address
	signFn   SignerFn
	signTxFn SignerTxFn

	lock sync.RWMutex // Protects the signer fields

	ethAPI                 *ethapi.BlockChainAPI
	validatorControllerABI abi.ABI
	validatorHubABI        abi.ABI
	slashABI               abi.ABI
	stakingDelegatorABI    abi.ABI

	// The fields below are for testing only
	fakeDiff bool // Skip difficulty verifications

}

func New(
	chainConfig *params.ChainConfig,
	db ethdb.Database,
	ethAPI *ethapi.BlockChainAPI,
	genesisHash common.Hash,
) *Zephyria {

	zephyriaConfig := chainConfig.Zephyria

	// Set any missing consensus parameters to their defaults
	if zephyriaConfig != nil && zephyriaConfig.Epoch == 0 {
		zephyriaConfig.Epoch = defaultEpochLength
	}

	// Allocate the snapshot caches and create the engine
	recentSnaps, err := lru.NewARC(inMemorySnapshots)
	if err != nil {
		panic(err)
	}
	signatures, err := lru.NewARC(inMemorySignatures)
	if err != nil {
		panic(err)
	}

	vController, err := abi.JSON(strings.NewReader(validatorControllerABI))
	if err != nil {
		panic(err)
	}

	vHubABI, err := abi.JSON(strings.NewReader(validatorHubABI))
	if err != nil {
		panic(err)
	}
	sABI, err := abi.JSON(strings.NewReader(slashABI))
	if err != nil {
		panic(err)
	}
	pABI, err := abi.JSON(strings.NewReader(stakingDelegatorABI))
	if err != nil {
		panic(err)
	}

	c := &Zephyria{
		chainConfig:            chainConfig,
		config:                 zephyriaConfig,
		genesisHash:            genesisHash,
		db:                     db,
		ethAPI:                 ethAPI,
		recentSnaps:            recentSnaps,
		signatures:             signatures,
		validatorControllerABI: vController,
		validatorHubABI:        vHubABI,
		slashABI:               sABI,
		stakingDelegatorABI:    pABI,
		signer:                 types.LatestSigner(chainConfig),
	}

	return c

}

func (p *Zephyria) IsSystemTransaction(tx *types.Transaction, header *types.Header) (bool, error) {
	// deploy a contract
	if tx.To() == nil {
		return false, nil
	}
	sender, err := types.Sender(p.signer, tx)
	if err != nil {
		return false, errors.New("UnAuthorized transaction")
	}
	if sender == header.Coinbase && isToSystemContract(*tx.To()) && tx.GasPrice().Cmp(big.NewInt(0)) == 0 {
		return true, nil
	}
	return false, nil
}

func (p *Zephyria) IsSystemContract(to *common.Address) bool {
	if to == nil {
		return false
	}
	return isToSystemContract(*to)
}

func (p *Zephyria) Author(header *types.Header) (common.Address, error) {
	return header.Coinbase, nil
}

func (p *Zephyria) VerifyHeader(chain consensus.ChainHeaderReader, header *types.Header) error {
	return p.verifyHeader(chain, header, nil)
}

// VerifyHeaders es similar a VerifyHeader, pero verifica un lote de encabezados. El método devuelve un canal de salida para abortar las operaciones y un canal de resultados para recuperar las verificaciones asincrónicas (el orden es el mismo que en la lista de entrada).
func (p *Zephyria) VerifyHeaders(chain consensus.ChainHeaderReader, headers []*types.Header) (chan<- struct{}, <-chan error) {
	// Crear un canal para abortar las operaciones
	abort := make(chan struct{})
	// Crear un canal de resultados para almacenar los errores de verificación
	results := make(chan error, len(headers))

	// Utilizar una goroutine para realizar las verificaciones en paralelo
	gopool.Submit(func() {
		for i, header := range headers {
			// Verificar el encabezado actual con la lista de encabezados anteriores
			err := p.verifyHeader(chain, header, headers[:i])

			select {
			// Si se recibe una señal de abortar, salir de la goroutine
			case <-abort:
				return
			// Almacenar el resultado de la verificación en el canal de resultados
			case results <- err:
			}
		}
	})

	// Devolver los canales de aborto y resultados
	return abort, results
}

// getParent returns the parent of a given block.
func (p *Zephyria) getParent(chain consensus.ChainHeaderReader, header *types.Header, parents []*types.Header) (*types.Header, error) {
	var parent *types.Header
	number := header.Number.Uint64()
	if len(parents) > 0 {
		parent = parents[len(parents)-1]
	} else {
		parent = chain.GetHeader(header.ParentHash, number-1)
	}

	if parent == nil || parent.Number.Uint64() != number-1 || parent.Hash() != header.ParentHash {
		return nil, consensus.ErrUnknownAncestor
	}
	return parent, nil
}

func (p *Zephyria) verifyHeader(chain consensus.ChainHeaderReader, header *types.Header, parents []*types.Header) error {
	// Verify the header fields
	if header.Number == nil {
		return errUnknownBlock
	}
	number := header.Number.Uint64()

	// Don't waste time checking blocks from the future
	if header.Time > uint64(time.Now().Unix()) {
		return consensus.ErrFutureBlock
	}

	// Check that the extra-data contains the vanity, validators and signature.
	if len(header.Extra) < extraVanity {
		return errMissingVanity
	}
	if len(header.Extra) < extraVanity+extraSeal {
		return errMissingSignature
	}

	// check extra data
	isEpoch := number%p.config.Epoch == 0

	// Ensure that the extra-data contains a signer list on checkpoint, but none otherwise
	signersBytes := len(header.Extra) - extraVanity - extraSeal
	if !isEpoch && signersBytes != 0 {
		return errExtraValidators
	}

	if isEpoch && signersBytes%validatorBytesLength != 0 {
		return errInvalidSpanValidators
	}

	// Ensure that the mix digest is zero as we don't have fork protection currently
	if header.MixDigest != (common.Hash{}) {
		return errInvalidMixDigest
	}
	// Ensure that the block doesn't contain any uncles which are meaningless in PoA
	if header.UncleHash != uncleHash {
		return errInvalidUncleHash
	}
	// Ensure that the block's difficulty is meaningful (may not be correct at this point)
	if number > 0 {
		if header.Difficulty == nil {
			return errInvalidDifficulty
		}
	}

	parent, err := p.getParent(chain, header, parents)
	if err != nil {
		return err
	}

	// Verify the block's gas usage and (if applicable) verify the base fee.
	if !chain.Config().IsLondon(header.Number) {
		// Verify BaseFee not present before EIP-1559 fork.
		if header.BaseFee != nil {
			return fmt.Errorf("invalid baseFee before fork: have %d, expected 'nil'", header.BaseFee)
		}
	} else if err := eip1559.VerifyEIP1559Header(chain.Config(), parent, header); err != nil {
		// Verify the header's EIP-1559 attributes.
		return err
	}

	// Verify existence / non-existence of withdrawalsHash.
	if header.WithdrawalsHash != nil {
		return fmt.Errorf("invalid withdrawalsHash: have %x, expected nil", header.WithdrawalsHash)
	}

	// All basic checks passed, verify cascading fields
	return p.verifyCascadingFields(chain, header, parents)
}

func (p *Zephyria) verifyCascadingFields(chain consensus.ChainHeaderReader, header *types.Header, parents []*types.Header) error {
	// The genesis block is the always valid dead-end
	number := header.Number.Uint64()
	if number == 0 {
		return nil
	}

	parent, err := p.getParent(chain, header, parents)
	if err != nil {
		return err
	}

	snap, err := p.snapshot(chain, number-1, header.ParentHash, parents)
	if err != nil {
		return err
	}

	//Blocktime verify
	if header.Time < parent.Time+p.config.Period+p.backOffTime(snap, header.Coinbase) {
		return consensus.ErrFutureBlock
	}

	// Verify that the gas limit is <= 2^63-1
	capacity := uint64(0x7fffffffffffffff)
	if header.GasLimit > capacity {
		return fmt.Errorf("invalid gasLimit: have %v, max %v", header.GasLimit, capacity)
	}

	// Verify that the gasUsed is <= gasLimit
	if header.GasUsed > header.GasLimit {
		return fmt.Errorf("invalid gasUsed: have %d, gasLimit %d", header.GasUsed, header.GasLimit)
	}

	// Verify that the gas limit remains within allowed bounds
	diff := int64(parent.GasLimit) - int64(header.GasLimit)
	if diff < 0 {
		diff *= -1
	}
	limit := parent.GasLimit / params.GasLimitBoundDivisor

	if uint64(diff) >= limit || header.GasLimit < params.MinGasLimit {
		return fmt.Errorf("invalid gas limit: have %d, want %d += %d", header.GasLimit, parent.GasLimit, limit)
	}

	// All basic checks passed, verify the seal and return
	return p.verifySeal(chain, header, parents)

}

// snapshot recupera la instantánea de autorización en un punto específico en el tiempo.
func (p *Zephyria) snapshot(chain consensus.ChainHeaderReader, number uint64, hash common.Hash, parents []*types.Header) (*Snapshot, error) {
	// Buscar una instantánea en la memoria o en disco para puntos de control
	var (
		headers []*types.Header
		snap    *Snapshot
	)

	for snap == nil {
		// Si se encuentra una instantánea en la memoria, úsala
		if s, ok := p.recentSnaps.Get(hash); ok {
			snap = s.(*Snapshot)
			break
		}

		// Si se puede encontrar una instantánea de punto de control en disco
		if number%checkpointInterval == 0 {
			if s, err := loadSnapshot(p.config, p.signatures, p.db, hash, p.ethAPI); err == nil {
				log.Trace("Loaded snapshot from disk", "number", number, "hash", hash)
				snap = s
				break
			}
		}

		// Si estamos en el bloque génesis, crea una instantánea del estado inicial.
		// Alternativamente, si hemos acumulado más encabezados de los permitidos para ser reorganizados,
		// considera el punto de control como confiable y crea una instantánea.
		if number == 0 || (number%p.config.Epoch == 0 && (len(headers) > params.FullImmutabilityThreshold)) {
			checkpoint := chain.GetHeaderByNumber(number)
			if checkpoint != nil {
				// Obtén los datos del punto de control
				hash := checkpoint.Hash()

				if len(checkpoint.Extra) <= extraVanity+extraSeal {
					return nil, errors.New("invalid extra-data for genesis block, check the genesis.json file")
				}
				validatorBytes := checkpoint.Extra[extraVanity : len(checkpoint.Extra)-extraSeal]
				// Obtén los validadores a partir de los encabezados
				validators, err := ParseValidators(validatorBytes)
				if err != nil {
					return nil, err
				}

				// Nueva instantánea
				snap = newSnapshot(p.config, p.signatures, number, hash, validators, p.ethAPI)
				if err := snap.store(p.db); err != nil {
					return nil, err
				}
				log.Info("Stored checkpoint snapshot to disk", "number", number, "hash", hash)
				break
			}
		}

		// No se encontró una instantánea para este encabezado, recopila el encabezado y retrocede en el tiempo
		var header *types.Header
		if len(parents) > 0 {
			// Si tenemos padres explícitos, selecciona uno (obligatorio)
			header = parents[len(parents)-1]
			if header.Hash() != hash || header.Number.Uint64() != number {
				return nil, consensus.ErrUnknownAncestor
			}
			parents = parents[:len(parents)-1]
		} else {
			// Sin padres explícitos (o no quedan), consulta la base de datos
			header = chain.GetHeader(hash, number)
			if header == nil {
				return nil, consensus.ErrUnknownAncestor
			}
		}
		headers = append(headers, header)
		number, hash = number-1, header.ParentHash
	}

	// Comprueba si la instantánea es nula
	if snap == nil {
		return nil, fmt.Errorf("unknown error while retrieving snapshot at block number %v", number)
	}

	// Se encontró una instantánea anterior, aplica los encabezados pendientes a la misma
	for i := 0; i < len(headers)/2; i++ {
		headers[i], headers[len(headers)-1-i] = headers[len(headers)-1-i], headers[i]
	}

	snap, err := snap.apply(headers, chain, parents, p.chainConfig.ChainID)
	if err != nil {
		return nil, err
	}
	p.recentSnaps.Add(snap.Hash, snap)

	// Si se ha generado una nueva instantánea de punto de control, guárdala en disco
	if snap.Number%checkpointInterval == 0 && len(headers) > 0 {
		if err = snap.store(p.db); err != nil {
			return nil, err
		}
		log.Trace("Stored snapshot to disk", "number", snap.Number, "hash", snap.Hash)
	}
	return snap, err
}

// VerifyUncles implements consensus.Engine, always returning an error for any
// uncles as this consensus mechanism doesn't permit uncles.
func (p *Zephyria) VerifyUncles(chain consensus.ChainReader, block *types.Block) error {
	if len(block.Uncles()) > 0 {
		return errors.New("uncles not allowed")
	}
	return nil
}

// VerifySeal implements consensus.Engine, checking whether the signature contained
// in the header satisfies the consensus protocol requirements.
func (p *Zephyria) VerifySeal(chain consensus.ChainReader, header *types.Header) error {
	return p.verifySeal(chain, header, nil)
}

// verifySeal verifica si la firma contenida en el encabezado satisface los
// requisitos del protocolo de consenso. El método acepta una lista opcional de
// encabezados padres que aún no forman parte de la cadena local para generar las
// instantáneas a partir de ellos.
func (p *Zephyria) verifySeal(chain consensus.ChainHeaderReader, header *types.Header, parents []*types.Header) error {
	// Verificar el bloque génesis no está soportado
	number := header.Number.Uint64()
	if number == 0 {
		return errUnknownBlock
	}

	// Recuperar la instantánea necesaria para verificar este encabezado y cachearla
	snap, err := p.snapshot(chain, number-1, header.ParentHash, parents)
	if err != nil {
		return err
	}

	// Resolver la clave de autorización y verificarla contra los validadores
	signer, err := ecrecover(header, p.signatures, p.chainConfig.ChainID)
	if err != nil {
		return err
	}

	// Comprobar si el firmante coincide con el valor de header.Coinbase
	if signer != header.Coinbase {
		return errCoinBaseMisMatch
	}

	// Verificar si el firmante está en la lista de validadores de la instantánea
	if _, ok := snap.Validators[signer]; !ok {
		return errUnauthorizedValidator(signer.String())
	}

	// Comprobar si el firmante ha firmado recientemente otros bloques
	if snap.SignRecently(signer) {
		return errRecentlySigned
	}

	// Asegurarse de que la dificultad corresponde a la "turnicidad" del firmante
	if !p.fakeDiff {
		inturn := snap.inturn(signer)
		if inturn && header.Difficulty.Cmp(diffInTurn) != 0 {
			return errWrongDifficulty
		}
		if !inturn && header.Difficulty.Cmp(diffNoTurn) != 0 {
			return errWrongDifficulty
		}
	}

	return nil
}

// Prepare implementa consensus.Engine, preparando todos los campos de consenso del encabezado
// para ejecutar las transacciones en la parte superior.
func (p *Zephyria) Prepare(chain consensus.ChainHeaderReader, header *types.Header) error {
	// Establece el valor de 'Coinbase' en el validador actual (p.val).
	header.Coinbase = p.val

	// Restablece el valor de 'Nonce' a un valor de bloque vacío.
	header.Nonce = types.BlockNonce{}

	// Obtiene el número del bloque actual.
	number := header.Number.Uint64()

	// Obtiene una instantánea (snapshot) del estado del bloque anterior.
	snap, err := p.snapshot(chain, number-1, header.ParentHash, nil)
	if err != nil {
		return err
	}

	// Establece la dificultad correcta para el bloque actual utilizando la función 'CalcDifficulty'.
	header.Difficulty = CalcDifficulty(snap, p.val)

	// Asegura que los datos adicionales ('Extra') tengan todos sus componentes.
	if len(header.Extra) < extraVanity-nextForkHashSize {
		header.Extra = append(header.Extra, bytes.Repeat([]byte{0x00}, extraVanity-nextForkHashSize-len(header.Extra))...)
	}

	// Asegura que la marca de tiempo ('timestamp') tenga el retraso correcto.
	// Esto implica calcular la marca de tiempo basada en el bloque anterior y las reglas del consenso.
	parent := chain.GetHeader(header.ParentHash, number-1)
	if parent == nil {
		return consensus.ErrUnknownAncestor
	}
	header.Time = parent.Time + p.config.Period + p.backOffTime(snap, p.val)

	// Si la marca de tiempo calculada es anterior al tiempo actual, se ajusta al tiempo actual.
	if header.Time < uint64(time.Now().Unix()) {
		header.Time = uint64(time.Now().Unix())
	}

	// Actualiza la parte de 'Extra' relacionada con la próxima marca de tiempo del bloque.
	nextForkHash := forkid.NewID(p.chainConfig, p.genesisHash, number, header.Time).Hash
	header.Extra = header.Extra[:extraVanity-nextForkHashSize]
	header.Extra = append(header.Extra, nextForkHash[:]...)

	// Prepara los validadores en el encabezado.
	if number%p.config.Epoch == 0 {
		newValidators, err := p.getCurrentValidators(header.ParentHash)
		if err != nil {
			return err
		}
		// sort validator by address
		sort.Sort(validatorsAscending(newValidators))
		for _, validator := range newValidators {
			header.Extra = append(header.Extra, validator.Bytes()...)
		}
	}

	// Agrega espacio adicional para el sello ('seal') en 'Extra'.
	header.Extra = append(header.Extra, make([]byte, extraSeal)...)

	// El valor del 'MixDigest' se reserva por ahora y se establece como vacío.
	header.MixDigest = common.Hash{}

	return nil
}

/* func (p *Zephyria) BeforeValidateTx(chain consensus.ChainHeaderReader, header *types.Header, state *state.StateDB, txs *[]*types.Transaction,
	uncles []*types.Header, receipts *[]*types.Receipt, systemTxs *[]*types.Transaction, usedGas *uint64) error {
	cx := chainContext{Chain: chain, zephyria: p}
	if header.Number.Uint64()%p.config.Epoch == 0 {
		err := p.setNewRound(state, header, cx, txs, receipts, systemTxs, usedGas, false)
		if err != nil {
			return err
		}

		err = p.distributeDelegatorReward(chain, state, header, cx, txs, receipts, systemTxs, usedGas, false)
		if err != nil {
			return err
		}
	}
	return nil
}

func (p *Zephyria) BeforePackTx(chain consensus.ChainHeaderReader, header *types.Header, state *state.StateDB,
	txs *[]*types.Transaction, uncles []*types.Header, receipts *[]*types.Receipt) error {
	cx := chainContext{Chain: chain, zephyria: p}
	// If the block is the last one in a round, execute turn round to update the validator set.
	if header.Number.Uint64()%p.config.Epoch == 0 {
		err := p.setNewRound(state, header, cx, txs, receipts, nil, &header.GasUsed, true)
		if err != nil {
			return err
		}

		err = p.distributeDelegatorReward(chain, state, header, cx, txs, receipts, nil, &header.GasUsed, true)
		if err != nil {
			return err
		}
	}
	return nil
} */

// Finalize implements consensus.Engine, ensuring no uncles are set, nor block
// rewards given.
func (p *Zephyria) Finalize(chain consensus.ChainHeaderReader, header *types.Header, state *state.StateDB, txs *[]*types.Transaction,
	uncles []*types.Header, _ []*types.Withdrawal, receipts *[]*types.Receipt, systemTxs *[]*types.Transaction, usedGas *uint64) error {
	// La función Finalize es una implementación del motor de consenso.
	// Su objetivo es finalizar un bloque y asegurarse de que no se establezcan tíos
	// (uncles) y que no se otorguen recompensas por bloques.

	// Verificar si el bloque está en la mayoría del fork
	number := header.Number.Uint64()
	snap, err := p.snapshot(chain, number-1, header.ParentHash, nil)
	if err != nil {
		return err
	}

	nextForkHash := forkid.NewID(p.chainConfig, p.genesisHash, number, header.Time).Hash
	if !snap.isMajorityFork(hex.EncodeToString(nextForkHash[:])) {
		log.Debug("there is a possible fork, and your client is not the majority. Please check...", "nextForkHash", hex.EncodeToString(nextForkHash[:]))
	}

	// Si el bloque es un bloque de final de época, verifica la lista de validadores.
	if header.Number.Uint64()%p.config.Epoch == 0 {
		newValidators, err := p.getCurrentValidators(header.ParentHash)
		if err != nil {
			log.Error("error aqui getCurrentValidators")
			return err
		}
		// Ordena los validadores por dirección.
		sort.Sort(validatorsAscending(newValidators))
		validatorsBytes := make([]byte, len(newValidators)*validatorBytesLength)
		for i, validator := range newValidators {
			copy(validatorsBytes[i*validatorBytesLength:], validator.Bytes())
		}

		extraSuffix := len(header.Extra) - extraSeal
		// Verifica que los bytes extra del encabezado coincidan con la lista de validadores.
		if !bytes.Equal(header.Extra[extraVanity:extraSuffix], validatorsBytes) {
			return errMismatchingEpochValidators
		}
	}

	// No hay recompensas por bloques en PoA, por lo que el estado permanece igual y los tíos se descartan.
	cx := chainContext{Chain: chain, zephyria: p}

	// Inicializar el contrato si el número de bloque es igual a 1.
	if header.Number.Cmp(common.Big1) == 0 {
		err := p.initContract(state, header, cx, txs, receipts, systemTxs, usedGas, false)
		if err != nil {
			log.Error("init contract failed")
		}
	}

	// Verificar si el valor del encabezado coincide con la dificultad en turno (diffInTurn).
	if header.Difficulty.Cmp(diffInTurn) != 0 {
		spoiledVal := snap.supposeValidator()
		signedRecently := false
		if p.chainConfig.IsMontanas(header.Number) {
			signedRecently = snap.SignRecently(spoiledVal)
		} else {
			for _, recent := range snap.Recents {
				if recent == spoiledVal {
					signedRecently = true
					break
				}
			}
		}

		if !signedRecently {
			log.Trace("slash validator", "block hash", header.Hash(), "address", spoiledVal)
			err = p.slash(spoiledVal, state, header, cx, txs, receipts, systemTxs, usedGas, false)
			if err != nil {
				// Es posible que la función "slash" haya fallado porque el canal de castigo está deshabilitado.
				log.Error("slash validator failed", "block hash", header.Hash(), "address", spoiledVal)
			}
		}
	}

	// Distribuir las recompensas entrantes al validador del bloque.
	val := header.Coinbase
	err = p.distributeIncoming(val, state, header, cx, txs, receipts, systemTxs, usedGas, false)
	if err != nil {
		return err
	}

	// Verificar si la longitud de las transacciones del sistema coincide.
	if len(*systemTxs) > 0 {
		return errors.New("the length of systemTxs do not match")
	}

	// Devuelve un error nulo para indicar que la finalización se realizó con éxito.
	return nil
}

// FinalizeAndAssemble implementa consensus.Engine, asegurando que no se establezcan tíos (uncles),
// ni se otorguen recompensas de bloque, y devuelve el bloque final.
func (p *Zephyria) FinalizeAndAssemble(chain consensus.ChainHeaderReader, header *types.Header, state *state.StateDB,
	txs []*types.Transaction, uncles []*types.Header, receipts []*types.Receipt, _ []*types.Withdrawal) (*types.Block, []*types.Receipt, error) {
	// No hay recompensas de bloque en PoA, por lo que el estado permanece igual y los tíos se descartan.
	cx := chainContext{Chain: chain, zephyria: p}

	// Inicializa las listas de transacciones y recibos si están vacías.
	if txs == nil {
		txs = make([]*types.Transaction, 0)
	}
	if receipts == nil {
		receipts = make([]*types.Receipt, 0)
	}

	// Si el número de bloque es 1, inicializa los contratos.
	if header.Number.Cmp(common.Big1) == 0 {
		err := p.initContract(state, header, cx, &txs, &receipts, nil, &header.GasUsed, true)
		if err != nil {
			log.Error("init contract failed")
		}
	}

	// Verifica si el nivel de dificultad es diferente de diffInTurn.
	if header.Difficulty.Cmp(diffInTurn) != 0 {
		number := header.Number.Uint64()
		snap, err := p.snapshot(chain, number-1, header.ParentHash, nil)
		if err != nil {
			return nil, nil, err
		}
		spoiledVal := snap.supposeValidator()
		signedRecently := false

		// Comprueba si el bloque está en la época de Plato.
		if p.chainConfig.IsMontanas(header.Number) {
			signedRecently = snap.SignRecently(spoiledVal)
		} else {
			for _, recent := range snap.Recents {
				if recent == spoiledVal {
					signedRecently = true
					break
				}
			}
		}

		// Si no ha firmado recientemente, realiza un "slash" del validador.
		if !signedRecently {
			err = p.slash(spoiledVal, state, header, cx, &txs, &receipts, nil, &header.GasUsed, true)
			if err != nil {
				// Es posible que el "slash" del validador haya fallado debido a que el canal de "slash" está desactivado.
				log.Error("slash validator failed", "block hash", header.Hash(), "address", spoiledVal)
			}
		}
	}

	err := p.distributeIncoming(p.val, state, header, cx, &txs, &receipts, nil, &header.GasUsed, true)
	if err != nil {
		return nil, nil, err
	}

	// No debería suceder. En caso de que ocurra, es mejor detener el nodo que difundir el bloque.
	if header.GasLimit < header.GasUsed {
		return nil, nil, errors.New("gas consumption of system txs exceed the gas limit")
	}

	// Calcula el hash de los tíos (uncles).
	header.UncleHash = types.CalcUncleHash(nil)
	var blk *types.Block
	var rootHash common.Hash
	wg := sync.WaitGroup{}
	wg.Add(2)
	go func() {
		rootHash = state.IntermediateRoot(chain.Config().IsEIP158(header.Number))
		wg.Done()
	}()
	go func() {
		blk = types.NewBlock(header, txs, nil, receipts, trie.NewStackTrie(nil))
		wg.Done()
	}()
	wg.Wait()
	blk.SetRoot(rootHash)

	// Ensambla y devuelve el bloque final listo para ser sellado.
	return blk, receipts, nil
}

// Authorize injects a private key into the consensus engine to mint new blocks
// with.
func (p *Zephyria) Authorize(val common.Address, signFn SignerFn, signTxFn SignerTxFn) {
	p.lock.Lock()
	defer p.lock.Unlock()

	p.val = val
	p.signFn = signFn
	p.signTxFn = signTxFn
}

// Argument leftOver is the time reserved for block finalize(calculate root, distribute income...)
func (p *Zephyria) Delay(chain consensus.ChainReader, header *types.Header, leftOver *time.Duration) *time.Duration {
	delay := time.Until(time.Unix(int64(header.Time), 0))

	if *leftOver >= time.Duration(p.config.Period)*time.Second {
		// ignore invalid leftOver
		log.Error("Delay invalid argument", "leftOver", leftOver.String(), "Period", p.config.Period)
	} else if *leftOver >= delay {
		delay = time.Duration(0)
		return &delay
	} else {
		delay = delay - *leftOver
	}

	// The blocking time should be no more than half of period
	half := time.Duration(p.config.Period) * time.Second / 2
	if delay > half {
		delay = half
	}
	return &delay
}

// Seal implementa consensus.Engine, intentando crear un bloque sellado utilizando
// las credenciales locales de firma.
func (p *Zephyria) Seal(chain consensus.ChainHeaderReader, block *types.Block, results chan<- *types.Block, stop <-chan struct{}) error {
	header := block.Header()

	// No se admite sellar el bloque génesis.
	number := header.Number.Uint64()
	if number == 0 {
		return errUnknownBlock
	}

	// Para cadenas de periodo 0, se rechazan los bloques vacíos (sin recompensa, pero se sellarían sin transacciones).
	if p.config.Period == 0 && len(block.Transactions()) == 0 {
		log.Info("Sealing paused, waiting for transactions")
		return nil
	}

	// No mantenga los campos 'val' durante todo el procedimiento de sellado.
	p.lock.RLock()
	val, signFn := p.val, p.signFn
	p.lock.RUnlock()

	// Obtener una instantánea (snapshot) del estado del bloque anterior.
	snap, err := p.snapshot(chain, number-1, header.ParentHash, nil)
	if err != nil {
		return err
	}

	// Salir si no tenemos autorización para sellar un bloque.
	if _, authorized := snap.Validators[val]; !authorized {
		return errUnauthorizedValidator(val.String())
	}

	// Si estamos entre los firmantes recientes, esperar al siguiente bloque.
	if snap.SignRecently(val) {
		log.Info("Signed recently, must wait for others")
		return nil
	}

	// Bien, el protocolo nos permite sellar el bloque, esperar nuestro turno.
	delay := time.Until(time.Unix(int64(header.Time), 0))

	log.Info("Sealing block with", "number", number, "delay", delay, "headerDifficulty", header.Difficulty, "val", val.Hex())

	// ¡Firmar todo!
	sig, err := signFn(accounts.Account{Address: val}, accounts.MimetypeZephyria, ZephyriaRLP(header, p.chainConfig.ChainID))
	if err != nil {
		log.Error("Sign for the block header failed when sealing", "err", err)
		return err
	}
	copy(header.Extra[len(header.Extra)-extraSeal:], sig)

	// Esperar hasta que se termine el sellado o se alcance el tiempo de retraso.
	log.Trace("Waiting for slot to sign and propagate", "delay", common.PrettyDuration(delay))
	go func() {
		select {
		case <-stop:
			return
		case <-time.After(delay):
		}
		if p.shouldWaitForCurrentBlockProcess(chain, header, snap) {
			log.Info("Esperando el procesamiento del bloque que se recibió en su turno")
			select {
			case <-stop:
				log.Info("Proceso de bloque recibido finalizado, abortar sellado del bloque")
				return
			case <-time.After(time.Duration(processBackOffTime) * time.Second):
				if chain.CurrentHeader().Number.Uint64() >= header.Number.Uint64() {
					log.Info("Tiempo de espera de proceso agotado y el encabezado actual se ha actualizado para abortar este sellado")
					return
				}
				log.Info("Tiempo de espera de proceso agotado, comienza a sellar el bloque")
			}
		}

		select {
		case results <- block.WithSeal(header):
		default:
			log.Warn("El resultado del sellado no es leído por el minero", "hash del sello", SealHash(header, p.chainConfig.ChainID))
		}
	}()

	return nil
}

func (p *Zephyria) shouldWaitForCurrentBlockProcess(chain consensus.ChainHeaderReader, header *types.Header, snap *Snapshot) bool {
	if header.Difficulty.Cmp(diffInTurn) == 0 {
		return false
	}

	highestVerifiedHeader := chain.GetHighestVerifiedHeader()
	if highestVerifiedHeader == nil {
		return false
	}

	if header.ParentHash == highestVerifiedHeader.ParentHash {
		return true
	}
	return false
}

func (p *Zephyria) EnoughDistance(chain consensus.ChainReader, header *types.Header) bool {
	snap, err := p.snapshot(chain, header.Number.Uint64()-1, header.ParentHash, nil)
	if err != nil {
		return true
	}
	return snap.enoughDistance(p.val, header)
}

func (p *Zephyria) IsLocalBlock(header *types.Header) bool {
	return p.val == header.Coinbase
}

func (p *Zephyria) SignRecently(chain consensus.ChainReader, parent *types.Block) (bool, error) {
	snap, err := p.snapshot(chain, parent.NumberU64(), parent.Hash(), nil)
	if err != nil {
		return true, err
	}

	// Bail out if we're unauthorized to sign a block
	if _, authorized := snap.Validators[p.val]; !authorized {
		return true, errUnauthorizedValidator(p.val.String())
	}

	return snap.SignRecently(p.val), nil
}

// CalcDifficulty es el algoritmo de ajuste de dificultad. Devuelve la dificultad
// que un nuevo bloque debe tener en función de los bloques anteriores en la cadena y el
// firmante actual.
func (p *Zephyria) CalcDifficulty(chain consensus.ChainHeaderReader, time uint64, parent *types.Header) *big.Int {
	// Obtener una instantánea del estado actual para el bloque padre
	snap, err := p.snapshot(chain, parent.Number.Uint64(), parent.Hash(), nil)
	if err != nil {
		return nil
	}
	// Calcular la dificultad utilizando la función CalcDifficulty y el validador actual
	return CalcDifficulty(snap, p.val)
}

// CalcDifficulty es el algoritmo de ajuste de dificultad. Devuelve la dificultad
// que un nuevo bloque debe tener en función de los bloques anteriores en la cadena y el
// firmante actual.
func CalcDifficulty(snap *Snapshot, signer common.Address) *big.Int {
	// Verificar si el firmante está en su "turno"
	if snap.inturn(signer) {
		// Si está en su "turno", establecer la dificultad como diffInTurn
		return new(big.Int).Set(diffInTurn)
	}
	// Si no está en su "turno", establecer la dificultad como diffNoTurn
	return new(big.Int).Set(diffNoTurn)
}

func (p *Zephyria) SealHash(header *types.Header) (hash common.Hash) {
	return SealHash(header, p.chainConfig.ChainID)
}

func (p *Zephyria) APIs(chain consensus.ChainHeaderReader) []rpc.API {
	return []rpc.API{{
		Namespace: "zephyria",
		Version:   "1.0",
		Service:   &API{chain: chain, zephyria: p},
		Public:    false,
	}}
}

// Close implements consensus.Engine. It's a noop for zephyria as there are no background threads.
func (p *Zephyria) Close() error {
	// La función Close es una implementación del motor de consenso.
	// Para el motor de consenso "Zephyria," esta función no realiza ninguna operación
	// especial ya que no hay hilos en segundo plano u operaciones pendientes que necesiten
	// ser gestionadas al cerrar el motor.

	// Devuelve un error nulo para indicar que el cierre se realizó con éxito.
	return nil
}

// ==========================  interaction with contract/account =========

// getCurrentValidators obtiene los validadores actuales.
func (p *Zephyria) getCurrentValidators(blockHash common.Hash) ([]common.Address, error) {
	// Obtiene el número de bloque para el bloque especificado por su hash.
	blockNr := rpc.BlockNumberOrHashWithHash(blockHash, false)

	// Define el método a ser llamado en el contrato.
	method := "getValidators"

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel() // Cancela cuando hemos terminado de consumir enteros.

	// Empaqueta la llamada al método en formato de datos para la transacción.
	data, err := p.validatorControllerABI.Pack(method)
	if err != nil {
		log.Error("Unable to pack tx for getValidators", "error", err)
		return nil, err
	}

	fmt.Println(data)

	// Realiza la llamada al contrato utilizando la API de Ethereum.
	msgData := (hexutil.Bytes)(data)
	toAddress := common.HexToAddress(systemcontracts.ValidatorController)
	gas := (hexutil.Uint64)(uint64(math.MaxUint64 / 2))

	// Fix error by passing blockNr by pointer
	result, err := p.ethAPI.Call(ctx, ethapi.TransactionArgs{
		Gas:  &gas,
		To:   &toAddress,
		Data: &msgData,
	}, blockNr, nil, nil)
	if err != nil {
		return nil, err
	}

	var (
		ret0 = new([]common.Address)
	)
	out := ret0

	if err := p.validatorControllerABI.UnpackIntoInterface(out, method, result); err != nil {
		return nil, err
	}

	valz := make([]common.Address, len(*ret0))
	// nolint: gosimple
	for i, a := range *ret0 {
		valz[i] = a
	}
	return valz, nil
}

// Distribuir a los validadores y al contrato de recompensa del sistema
func (p *Zephyria) distributeIncoming(val common.Address, state *state.StateDB, header *types.Header, chain core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {
	coinbase := header.Coinbase
	balance := state.GetBalance(consensus.SystemAddress)

	// Verificar si el saldo del contrato del sistema es mayor que cero.
	if balance.Cmp(common.Big0) <= 0 {
		return nil
	}

	// Establecer el saldo del contrato del sistema a cero.
	state.SetBalance(consensus.SystemAddress, big.NewInt(0))

	// Agregar el saldo al coinbase (validador actual).
	state.AddBalance(coinbase, balance)

	// Verificar si es necesario distribuir recompensas del sistema.
	doDistributeSysReward := state.GetBalance(common.HexToAddress(systemcontracts.SystemRewardContract)).Cmp(maxSystemBalance) < 0
	if doDistributeSysReward {
		rewards := new(big.Int)
		rewards = rewards.Rsh(balance, systemRewardPercent)

		// Si las recompensas son mayores que cero, distribuirlas al contrato de recompensa del sistema.
		if rewards.Cmp(common.Big0) > 0 {
			err := p.distributeToSystem(rewards, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
			if err != nil {
				return err
			}
			log.Trace("distribute to system reward pool", "block hash", header.Hash(), "amount", rewards)
			balance = balance.Sub(balance, rewards)
		}
	}

	// Distribuir el saldo restante al contrato del validador.
	log.Trace("distribute to validator contract", "block hash", header.Hash(), "amount", balance)
	return p.distributeToValidator(balance, val, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
}

// Realiza una operación de "slashing" en la blockchain para sancionar a un validador que ha incumplido las reglas.
func (p *Zephyria) slash(spoiledVal common.Address, state *state.StateDB, header *types.Header, chain core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {
	// Método a llamar en el contrato de "slashing"
	method := "slash"

	// Empaquetar los datos del método para la operación de "slashing"
	data, err := p.slashABI.Pack(method, spoiledVal)
	if err != nil {
		log.Error("Unable to pack tx for slash", "error", err)
		return err
	}

	// Crear un mensaje del sistema para la operación de "slashing"
	msg := p.getSystemMessage(header.Coinbase, common.HexToAddress(systemcontracts.SlashContract), data, common.Big0)

	// Aplicar el mensaje en el estado, lo que representa llevar a cabo la operación de "slashing" en la blockchain
	return p.applyTransaction(msg, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
}

// initContract inicializa contratos específicos en la cadena.
func (p *Zephyria) initContract(state *state.StateDB, header *types.Header, chain core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {
	// Método a ser llamado en los contratos.
	method := "init"

	// Lista de contratos que se inicializarán.
	contracts := []string{
		systemcontracts.ValidatorController,
		systemcontracts.SlashContract,
		systemcontracts.SystemRewardContract,
		systemcontracts.PolarysLightclient,
		systemcontracts.RelayerHubContract,
		systemcontracts.ValidatorHub,
		systemcontracts.GovHubContract,
		systemcontracts.StakingSystem,
		systemcontracts.StakingDelegator,
		systemcontracts.FsPRY,
	}

	// Obtiene los datos empaquetados para la llamada al método.
	data, err := p.validatorControllerABI.Pack(method)
	if err != nil {
		log.Error("Unable to pack tx for init validator set", "error", err)
		return err
	}

	// Itera sobre los contratos y aplica la inicialización a cada uno de ellos.
	for _, c := range contracts {
		// Crea un mensaje para la inicialización del contrato.
		msg := p.getSystemMessage(header.Coinbase, common.HexToAddress(c), data, common.Big0)

		// Aplica el mensaje para inicializar el contrato.
		log.Trace("init contract", "block hash", header.Hash(), "contract", c)
		err = p.applyTransaction(msg, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
		if err != nil {
			return err
		}
	}

	return nil
}

func (p *Zephyria) distributeToSystem(amount *big.Int, state *state.StateDB, header *types.Header, chain core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {
	// get system message
	msg := p.getSystemMessage(header.Coinbase, common.HexToAddress(systemcontracts.SystemRewardContract), nil, amount)
	// apply message
	return p.applyTransaction(msg, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
}

// Realizar una operación de depósito en el contrato del validador
func (p *Zephyria) distributeToValidator(amount *big.Int, validator common.Address,
	state *state.StateDB, header *types.Header, chain core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {
	// Método a llamar en el contrato del validador
	method := "deposit"

	// Empaquetar los datos del método para el contrato del validador
	data, err := p.validatorControllerABI.Pack(method, validator)
	if err != nil {
		log.Error("Unable to pack tx for deposit", "error", err)
		return err
	}

	// Crear un mensaje del sistema para la operación de depósito
	msg := p.getSystemMessage(header.Coinbase, common.HexToAddress(systemcontracts.ValidatorController), data, amount)

	// Aplicar el mensaje en el estado, lo que representa realizar el depósito en el contrato del validador
	return p.applyTransaction(msg, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
}

func (p *Zephyria) distributeDelegatorReward(chain consensus.ChainHeaderReader, state *state.StateDB, header *types.Header, cx core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {

	snap, err := p.snapshot(chain, header.Number.Uint64()-1, header.ParentHash, nil)
	if err != nil {
		return err
	}

	validators := snap.validators()

	method := "distributeReward"

	data, err := p.stakingDelegatorABI.Pack(method, validators)
	if err != nil {
		log.Error("Unable to pack tx for distributeReward", "error", err)
	}

	msg := p.getSystemMessage(header.Coinbase, common.HexToAddress(systemcontracts.StakingDelegator), data, common.Big0)

	return p.applyTransaction(msg, state, header, cx, txs, receipts, receivedTxs, usedGas, mining)
}

func (p *Zephyria) updateValidators(state *state.StateDB, header *types.Header, chain core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {
	method := "updateValidators"

	data, err := p.validatorHubABI.Pack(method)
	if err != nil {
		log.Error("Unable to pack tx for updateValidators", "error", err)
	}

	msg := p.getSystemMessage(header.Coinbase, common.HexToAddress(systemcontracts.ValidatorHub), data, common.Big0)

	return p.applyTransaction(msg, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
}

func (p *Zephyria) setNewRound(state *state.StateDB, header *types.Header, chain core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {
	method := "setNewRound"

	data, err := p.stakingDelegatorABI.Pack(method)
	if err != nil {
		log.Error("Unable to pack tx for setNewRound", "error", err)
	}

	msg := p.getSystemMessage(header.Coinbase, common.HexToAddress(systemcontracts.StakingDelegator), data, common.Big0)

	return p.applyTransaction(msg, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
}

func (p *Zephyria) emitWithdrawals(state *state.StateDB, header *types.Header, chain core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt, receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool) error {

	method := "emitWithdrawals"

	data, err := p.validatorHubABI.Pack(method)
	if err != nil {
		log.Error("Unable to pack tx for emitWithdrawals", "error", err)
		return err
	}

	msg := p.getSystemMessage(header.Coinbase, common.HexToAddress(systemcontracts.ValidatorHub), data, common.Big0)

	return p.applyTransaction(msg, state, header, chain, txs, receipts, receivedTxs, usedGas, mining)
}

// get system message
func (p *Zephyria) getSystemMessage(from, toAddress common.Address, data []byte, value *big.Int) callmsg {
	return callmsg{
		ethereum.CallMsg{
			From:     from,
			Gas:      math.MaxUint64 / 2,
			GasPrice: big.NewInt(0),
			Value:    value,
			To:       &toAddress,
			Data:     data,
		},
	}
}

func (p *Zephyria) applyTransaction(
	msg callmsg,
	state *state.StateDB,
	header *types.Header,
	chainContext core.ChainContext,
	txs *[]*types.Transaction, receipts *[]*types.Receipt,
	receivedTxs *[]*types.Transaction, usedGas *uint64, mining bool,
) (err error) {
	nonce := state.GetNonce(msg.From())
	expectedTx := types.NewTransaction(nonce, *msg.To(), msg.Value(), msg.Gas(), msg.GasPrice(), msg.Data())
	expectedHash := p.signer.Hash(expectedTx)

	if msg.From() == p.val && mining {
		expectedTx, err = p.signTxFn(accounts.Account{Address: msg.From()}, expectedTx, p.chainConfig.ChainID)
		if err != nil {
			return err
		}
	} else {
		if receivedTxs == nil || len(*receivedTxs) == 0 || (*receivedTxs)[0] == nil {
			return errors.New("supposed to get a actual transaction, but get none")
		}
		actualTx := (*receivedTxs)[0]
		if !bytes.Equal(p.signer.Hash(actualTx).Bytes(), expectedHash.Bytes()) {
			return fmt.Errorf("expected tx hash %v, get %v, nonce %d, to %s, value %s, gas %d, gasPrice %s, data %s", expectedHash.String(), actualTx.Hash().String(),
				expectedTx.Nonce(),
				expectedTx.To().String(),
				expectedTx.Value().String(),
				expectedTx.Gas(),
				expectedTx.GasPrice().String(),
				hex.EncodeToString(expectedTx.Data()),
			)
		}
		expectedTx = actualTx
		// move to next
		*receivedTxs = (*receivedTxs)[1:]
	}
	state.SetTxContext(expectedTx.Hash(), len(*txs))
	gasUsed, err := applyMessage(msg, state, header, p.chainConfig, chainContext)
	if err != nil {
		return err
	}
	*txs = append(*txs, expectedTx)
	var root []byte
	if p.chainConfig.IsByzantium(header.Number) {
		state.Finalise(true)
	} else {
		root = state.IntermediateRoot(p.chainConfig.IsEIP158(header.Number)).Bytes()
	}
	*usedGas += gasUsed
	receipt := types.NewReceipt(root, false, *usedGas)
	receipt.TxHash = expectedTx.Hash()
	receipt.GasUsed = gasUsed

	// Set the receipt logs and create a bloom for filtering
	receipt.Logs = state.GetLogs(expectedTx.Hash(), header.Number.Uint64(), header.Hash())
	receipt.Bloom = types.CreateBloom(types.Receipts{receipt})
	receipt.BlockHash = header.Hash()
	receipt.BlockNumber = header.Number
	receipt.TransactionIndex = uint(state.TxIndex())
	*receipts = append(*receipts, receipt)
	state.SetNonce(msg.From(), nonce+1)
	return nil
}

func (p *Zephyria) GetSafeBlock(chain consensus.ChainReader, currentHeader *types.Header) (uint64, error) {
	snap, err := p.snapshot(chain, currentHeader.Number.Uint64()-1, currentHeader.ParentHash, nil)
	if err != nil {
		return 0, err
	}
	return snap.GetSafeBlock(currentHeader, p.val), nil
}

func (p *Zephyria) ComprobeLastBlock(chain consensus.ChainHeaderReader, currentHeader *types.Header) *types.Header {
	snap, err := p.snapshot(chain, currentHeader.Number.Uint64()-1, currentHeader.ParentHash, nil)
	if err != nil {
		return nil
	}

	ok := snap.IsLastBlockInSnapshot(currentHeader.ParentHash)

	if ok {
		return currentHeader
	} else {
		return nil
	}
}

func (p *Zephyria) AllowLightProcess(chain consensus.ChainReader, currentHeader *types.Header) bool {
	snap, err := p.snapshot(chain, currentHeader.Number.Uint64()-1, currentHeader.ParentHash, nil)
	if err != nil {
		return true
	}

	idx := snap.indexOfVal(p.val)
	// validator is not allowed to diff sync
	return idx < 0
}

// ===========================     utility function        ==========================

// SealHash returns the hash of a block prior to it being sealed.
func SealHash(header *types.Header, chainId *big.Int) (hash common.Hash) {
	hasher := sha3.NewLegacyKeccak256()
	encodeSigHeader(hasher, header, chainId)
	hasher.Sum(hash[:0])
	return hash
}

func encodeSigHeader(w io.Writer, header *types.Header, chainId *big.Int) {
	enc := []interface{}{
		chainId,
		header.ParentHash,
		header.UncleHash,
		header.Coinbase,
		header.Root,
		header.TxHash,
		header.ReceiptHash,
		header.Bloom,
		header.Difficulty,
		header.Number,
		header.GasLimit,
		header.GasUsed,
		header.Time,
		header.Extra[:len(header.Extra)-extraSeal], // Yes, this will panic if extra is too short
		header.MixDigest,
		header.Nonce,
	}
	if err := rlp.Encode(w, enc); err != nil {
		panic("can't encode: " + err.Error())
	}
}

func (p *Zephyria) backOffTime(snap *Snapshot, val common.Address) uint64 {
	if snap.inturn(val) {
		return 0
	}

	delay := initialBackOffTime
	validators := snap.validators()

	// get the index of the current validator
	idx := -1
	for index, itemAddr := range validators {
		if val == itemAddr {
			idx = index
			break
		}
	}

	if idx < 0 {
		log.Info("The validator is not authorized", "addr", val)
		return 0
	}

	s := mrand.NewSource(int64(snap.Number))
	r := mrand.New(s)
	n := len(validators)
	backOffSteps := make([]uint64, 0, n)

	for i := uint64(0); i < uint64(n); i++ {
		backOffSteps = append(backOffSteps, i)
	}

	r.Shuffle(n, func(i, j int) {
		backOffSteps[i], backOffSteps[j] = backOffSteps[j], backOffSteps[i]
	})

	delay += backOffSteps[idx] * wiggleTime
	return delay
}

// chain context
type chainContext struct {
	Chain    consensus.ChainHeaderReader
	zephyria consensus.Engine
}

func (c chainContext) Engine() consensus.Engine {
	return c.zephyria
}

func (c chainContext) GetHeader(hash common.Hash, number uint64) *types.Header {
	return c.Chain.GetHeader(hash, number)
}

// callmsg implements core.Message to allow passing it as a transaction simulator.
type callmsg struct {
	ethereum.CallMsg
}

func (m callmsg) From() common.Address { return m.CallMsg.From }
func (m callmsg) Nonce() uint64        { return 0 }
func (m callmsg) CheckNonce() bool     { return false }
func (m callmsg) To() *common.Address  { return m.CallMsg.To }
func (m callmsg) GasPrice() *big.Int   { return m.CallMsg.GasPrice }
func (m callmsg) Gas() uint64          { return m.CallMsg.Gas }
func (m callmsg) Value() *big.Int      { return m.CallMsg.Value }
func (m callmsg) Data() []byte         { return m.CallMsg.Data }

func applyMessage(
	msg callmsg,
	state *state.StateDB,
	header *types.Header,
	chainConfig *params.ChainConfig,
	chainContext core.ChainContext,
) (uint64, error) {
	// TODO(Nathan): state.Prepare should be called here, now accessList related EIP not affect systemtxs
	// 		 EIP1153 may cause a critical issue in the future
	// Create a new context to be used in the EVM environment
	context := core.NewEVMBlockContext(header, chainContext, nil)
	// Create a new environment which holds all relevant information
	// about the transaction and calling mechanisms.
	vmenv := vm.NewEVM(context, vm.TxContext{Origin: msg.From(), GasPrice: big.NewInt(0)}, state, chainConfig, vm.Config{})
	// Apply the transaction to the current state (included in the env)
	ret, returnGas, err := vmenv.Call(
		vm.AccountRef(msg.From()),
		*msg.To(),
		msg.Data(),
		msg.Gas(),
		msg.Value(),
	)
	if err != nil {
		log.Error("apply message failed", "msg", string(ret), "err", err)
	}
	return msg.Gas() - returnGas, err
}
