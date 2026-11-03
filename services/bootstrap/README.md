# Parity's JAM bootstrap service, as a second test service

`jam-bootstrap-service.jam` is the PVM blob of Parity's JAM bootstrap service, crate
[`jam-bootstrap-service`](https://crates.io/crates/jam-bootstrap-service) 0.1.29 (source in
`paritytech/polkajam`). It was built unmodified from the crate's published source with
`cargo jam-build` 0.1.29, using rustc 1.97.0:

```
sha256 abfbb971675d4feeadf25c6c516b0c546fea255f6bfb25bc95151ca08af23816  jam-bootstrap-service.jam
```

It is here as a second service for the proof tooling, built with the same SDK as witness
(`jam-pvm-common` 0.1.29). Its refine decodes the payload as `Instructions` (a list of
instructions, then a 32-octet salt) and returns them as `BootstrapWorkOutput`. Its accumulate
runs the instructions: storage, service creation, transfers and so on.

The blob is © Parity Technologies, licensed under the Apache License 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Only the build output is vendored; no source
is copied into this repository.
