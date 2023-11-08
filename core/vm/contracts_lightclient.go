package vm

import (
	"encoding/binary"
	"errors"
	"fmt"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	/* 	"github.com/polarysfundation/plightclient/astrum" */)

const (
	uint64TypeLength                      uint64 = 8
	precompileContractInputMetaDataLength uint64 = 64
)

type AstrumPLightClient struct{}

type InputData struct {
	Height uint64
	Hash   common.Hash
}

type AstrumHeader struct {
	ParentHash common.Hash
	UncleHash  common.Hash
	Coinbase   common.Address
	Difficulty *big.Int
	Number     *big.Int
	GasLimit   uint64
	GasUsed    uint64
	Timestamp  uint64
	Nonce      types.BlockNonce
}

func (a *AstrumPLightClient) Verify(input []byte, chain consensus.ChainHeaderReader) (b []byte, err error) {
	data, err := a.DecodeInput(input)
	if err != nil {
		return b, err
	}

	b, err = a.EncodeHeader(chain, data.Height)
	if err != nil {
		return b, err
	}

	return b, nil

}

func (a *AstrumPLightClient) EncodeHeader(chain consensus.ChainHeaderReader, height uint64) (result []byte, err error) {
	header := chain.GetHeaderByNumber(height)

	astrumHeader := &AstrumHeader{
		ParentHash: header.ParentHash,
		UncleHash:  header.UncleHash,
		Coinbase:   header.Coinbase,
		Difficulty: header.Difficulty,
		Number:     header.Number,
		GasLimit:   header.GasLimit,
		GasUsed:    header.GasUsed,
		Timestamp:  header.Time,
		Nonce:      header.Nonce,
	}
	copy(result[0:32], astrumHeader.ParentHash[:])
	copy(result[32:64], astrumHeader.UncleHash[:])
	copy(result[64:96], astrumHeader.Coinbase[12:])
	binary.BigEndian.PutUint64(result[96:128], astrumHeader.Difficulty.Uint64())
	binary.BigEndian.PutUint64(result[128:160], astrumHeader.Number.Uint64())
	binary.BigEndian.PutUint64(result[160:192], astrumHeader.GasLimit)
	binary.BigEndian.PutUint64(result[192:224], astrumHeader.GasUsed)
	binary.BigEndian.PutUint64(result[224:256], astrumHeader.Timestamp)
	copy(result[256:288], astrumHeader.Nonce[:])

	return result, nil
}

func (a *AstrumPLightClient) DecodeInput(input []byte) (result InputData, err error) {

	if len(input) != 64 {
		return result, errors.New("invalid input length")
	}

	result.Height = binary.BigEndian.Uint64(input[0:32])
	copy(result.Hash[:], input[32:64])

	return result, nil
}


type pLightClient struct{}

func (c *pLightClient) RequiredGas(input []byte) uint64 {
	return params.PLightClientHeaderValidateGas
}

func (c *pLightClient) Run(input []byte) (result []byte, err error){
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("internal error: %v\n", r)
		}
	}()

	var chain consensus.ChainHeaderReader

	if uint64(len(input)) <= precompileContractInputMetaDataLength {
		return nil, fmt.Errorf("invalid input")
	}

	payloadLength := binary.BigEndian.Uint64(input[precompileContractInputMetaDataLength-uint64TypeLength : precompileContractInputMetaDataLength])
	if uint64(len(input)) != payloadLength+precompileContractInputMetaDataLength {
		return nil, fmt.Errorf("invalid input: input size should be %d, actual size is %d", payloadLength+precompileContractInputMetaDataLength, len(input))
	}

	var lightClient AstrumPLightClient
	data, err := lightClient.Verify(input, chain)
	if err != nil{
		return nil, err
	}

	return data, nil
}