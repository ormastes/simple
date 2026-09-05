# VHDL manifest verification is blocked by a bootstrap-seed runtime

- **Status:** OPEN
- **Severity:** high — compiler backend provenance changes cannot obtain
  self-hosted test evidence from the repository runtime.
- **Component:** `bin/simple`, release-runtime deployment/provenance
- **Detected:** 2026-08-12

## Evidence

The required exact command for
`test/01_unit/compiler/backend/vhdl_artifact_manifest_spec.spl` was invoked
from `/home/ormastes/dev/pub/simple` through
`bin/release/x86_64-unknown-linux-gnu/simple`.  The executable reported:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it
as the normal tool. Build and use the pure-Simple bin/simple instead.
```

Its diagnostics resolved sources below `/mnt/data/worktrees/simple-main`, so
its result cannot attest to the active workspace's compiler/VHDL provenance
boundary.  `readlink -f bin/simple` also resolves to that same release binary;
there is no distinct deployed pure-Simple runtime at this checkout.

## Impact

The historical Group C run recorded 18 examples with 9 failures for the VHDL
manifest spec.  The current source and spec are clean, but that result cannot
be reclassified as PASS or fixed from an untrusted seed-runner result.

## Required correction / unblock condition

Deploy a verified pure-Simple executable for this checkout so `bin/simple
test test/01_unit/compiler/backend/vhdl_artifact_manifest_spec.spl` executes
the active workspace sources and emits a normal `SPEC FILE VERDICT`.  Then run
that exact spec once and either fix any remaining provenance failure in
`src/compiler/80.driver/driver_vhdl_artifacts.spl` (and, for write-boundary
failures, `driver_riscv_gen2_product.spl`) or record its concrete failing
assertion and expected/actual values.
