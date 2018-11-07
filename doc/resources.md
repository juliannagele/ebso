
* [Solidity Assembly Doc](https://solidity.readthedocs.io/en/develop/assembly.html#)

* Lem/Isabelle Formalization Rep

  * [Repo](https://github.com/pirapira/eth-isab1elle/)

  * [CPP Paper](http://doi.org/10.1145/3167084)

* [Ethereum Virtual Machine (EVM) Awesome List](https://github.com/ethereum/wiki/wiki/Ethereum-Virtual-Machine-(EVM)-Awesome-List)
  
* possible reasons for unknown opcodes:
  * 0xfe is designated to be invalid:
    [EIP 141](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-141.md)
  * 0xfd is REVERT:
    [EIP 140](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-140.md)
  * 0xfa is STATICCALL: [EIP 214](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-214.md)
  * 0x1b, 0x1c, 0x1d are SHL, SHR, SAR:
    [EIP 145](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-145.md)
  * 0x3f is EXTCODEHASH:
    [EIP 1052](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1052.md)
  * 0xb0 to 0xb9 are "Subroutines and Static Jumps":
    [EIP 615](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-615.md)
  * 0xf5 is CREATE2:
    [EIP 1014](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1014.md)
  * solc adds metadata to the end of the deployed bytecode:
    `0xa1 0x65 'b' 'z' 'z' 'r' '0' 0x58 0x20 <32 bytes swarm hash> 0x00 0x29`, see
    [solidity doc](https://solidity.readthedocs.io/en/develop/metadata.html#encoding-of-the-metadata-hash-in-the-bytecode)
    and [manticore issue](https://github.com/trailofbits/manticore/issues/527)
  * contracts might store data after the code, see
    [stackexchange](https://ethereum.stackexchange.com/questions/15050/extra-byte-in-the-thedao-v1-bytecode/15289#15289)
    and [go-ethereum issue](https://github.com/ethereum/go-ethereum/issues/14376)

* Related Work
  * [Under-Optimized Smart Contracts Devour Your Money](https://arxiv.org/pdf/1703.03994.pdf)
  * [Towards saving money in using smart contracts](https://dl.acm.org/citation.cfm?id=3183420&dl=ACM&coll=DL)
  * [Vandal: A Scalable Security Analysis Framework for Smart Contracts](https://arxiv.org/abs/1809.03981)

