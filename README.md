[leanSPHINCS website](https://tomwambsgans.github.io/leanXMSS-leanSPHINCS-candidates/sphincs/)

[leanXMSS website](https://tomwambsgans.github.io/leanXMSS-leanSPHINCS-candidates/xmss/)

[leanSPHINCS.pdf](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/releases/download/doc-latest/leanSPHINCS.pdf)

[leanXMSS.pdf](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/releases/download/doc-latest/leanXMSS.pdf)

[leanSPHINCS security proofs in Lean 4](formal/sphincs/README.md)

## License and credits

The code of this repository is licensed under either of [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your
option.

Parts are adapted from [leanVM](https://github.com/leanEthereum/leanVM) (MIT OR Apache-2.0, see
[licenses/](licenses)): the `blake2s` and `sphincs` crates, and the Lean library `formal/sphincs/SphincsSecurity`,
which is leanVM's security proof of its three-layer scheme at commit `b7a107256`. The adder gadgets of `crates/mpc`
are adapted from [flock](https://github.com/succinctlabs/flock). The two-level WOTS forest of the spicy variant is
inspired by Jonas Nick's [sig.golf submission](https://github.com/Layr-Labs/sig.golf/commit/3321b777a511a6b454aad7ab721e8ab1af21c4d0).
