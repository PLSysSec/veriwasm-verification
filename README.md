# VeriWasm Verification

This repository contains the Coq proofs for [VeriWasm](https://github.com/PLSysSec/veriwasm), our verifier for SFI safety for native-compiled Wasm.

Our central proof of SFI safety is in `Safety.v` (`verified_program`).

### Third-party Coq code

We use code from
* [coq-lattice](https://github.com/jwiegley/coq-lattice)
* [Compcert](https://github.com/AbsInt/CompCert)
* [Adam Chlipala's tactics from CPDT](http://adam.chlipala.net/cpdt/repo/)
* [coq-record-update](https://github.com/tchajed/coq-record-update)
