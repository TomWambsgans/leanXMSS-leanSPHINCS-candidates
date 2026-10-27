# sphincs.art

Exploring leanSphincs: an hash based stateless signature scheme for Post-Quantum Ethereum.

- [Website](https://sphincs.art/)
- [Note (PDF)](https://github.com/TomWambsgans/sphincs.art/releases/download/doc-latest/leanSPHINCS.pdf)
- [Security proofs in Lean 4](formal/sphincs/README.md)

## Credits

- [leanVM](https://github.com/leanEthereum/leanVM): the `sphincs` crate and the Lean security proof are adapted from it.
- Conduition: [hypertree pruning](https://conduition.io/cryptography/hypertree-pruning/).
- Jonas Nick: the WOTS forest, from his
  [sig.golf submission](https://github.com/Layr-Labs/sig.golf/commit/3321b777a511a6b454aad7ab721e8ab1af21c4d0).
- [Riva Labs](https://www.riva.xyz/): preparing FTS instances before the message, for hardware wallets
  and threshold signing.
