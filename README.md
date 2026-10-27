[leanSPHINCS website](https://sphincs.art/)

[leanSPHINCS.pdf](https://github.com/TomWambsgans/sphincs.art/releases/download/doc-latest/leanSPHINCS.pdf)

[leanSPHINCS security proofs in Lean 4](formal/sphincs/README.md)

## Credits

Parts are adapted from [leanVM](https://github.com/leanEthereum/leanVM) (MIT OR Apache-2.0, see
[licenses/](licenses)): the `sphincs` crate, and the Lean proof `formal/sphincs/LeanForest`, which
builds on leanVM's security proof of its three-layer scheme at commit `b7a107256` (in this
repository's history at commit `7269bd3`). The two-level WOTS forest is
inspired by Jonas Nick's [sig.golf submission](https://github.com/Layr-Labs/sig.golf/commit/3321b777a511a6b454aad7ab721e8ab1af21c4d0). The idea of preparing FTS instances ahead of the message and grinding onto them comes from
[Riva Labs](https://www.riva.xyz/), for the hardware wallet (whose host grinds and proves it with a
STARK) and for the threshold signers (who MPC-generate the instance during preprocessing).
