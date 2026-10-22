# Focused portability diagnostics

Normal bootstrap CI blocks on portability contracts. To collect native Linux LLVM evidence while those contracts are being repaired, manually dispatch `rust-bootstrap-multiplatform.yml` with `native_lane=linux-llvm` and `defer_portability_verdict=true`.

This is an explicit diagnostic workaround, tagged `WORKAROUND_DEFER_PORTABILITY_VERDICT`. The option defaults to false and has no effect on pushes, pull requests, the full matrix, or the Cranelift lane. Other build and verification failures remain blocking.

A failed portability step records its failure and source revision in `build/bootstrap/portability-diagnostic.env`. Collected binary artifacts carry the `unadmitted-` prefix and include that record. The final native step always enforces the failed portability verdict, so the workflow remains failed even if compiler construction succeeds.

Use these artifacts only for provisional diagnosis with exact producer/source/runtime identity and real Hello qualification. Internal receipts do not establish full admission while the portability gate fails. Do not deploy, publish a release, or promote these artifacts. Restore and pass normal contracts before full admission; diagnostic collection never converts missing inputs, failed checks, or zero executed tests into PASS.
