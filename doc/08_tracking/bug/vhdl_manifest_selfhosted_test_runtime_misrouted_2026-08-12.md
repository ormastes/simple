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

## Addendum 2026-11-11 — P3 boot15 lane triage (worktree simple-p3-boot15-20261111, base f7640d20a458)

**Verdict: BLOCKED — kept OPEN.** The misrouting configuration itself is not present
at this tip: this worktree's `bin/simple.exe` is a TRACKED in-worktree fresh seed
(build-commit `46fe8f6b6def`, seedfix A+B), not a symlink resolving to an outside
release binary, so sources resolve under this checkout. What remains is the record's
unblock condition — a deployed verified pure-Simple runtime — which is a bootstrap
deployment action (Stage 3/4 admission, currently blocked by the OPEN
`stage3_*`/`stage4_full_cli_unlinkable_579_*` records) and cannot be produced on the
Windows lane host.

Current-state seed-smoke evidence (untrusted runner, recorded per this record's own
rule — classifies nothing): `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe
bin/simple.exe test test/01_unit/compiler/backend/vhdl_artifact_manifest_spec.spl
--mode=interpreter --no-cache` -> `SPEC FILE VERDICT ... outcome=ERROR declared>=21
executed=21 passed=15 failed=6` (full log retained at
`build/review/p3fix-boot15-vhdl-seed-smoke.log`). The historical Group C reading was
18 examples / 9 failures; the spec has since grown to 21. All 6 current failures are
in the Gen2 assurance-policy/provenance family ("requires a canonical critical
assurance-policy snapshot ...", route/graph-SHA/capability/decoder-closure
mismatches). Whether they are real `driver_vhdl_artifacts.spl` defects or artifacts
of known live seed divergences (e.g. text char/byte drift changing a hashed
serialization) CANNOT be decided from a seed run — that is precisely this record's
provenance point. No source edit was made; the visibility warnings in the log are the
known live seed private-fn-import divergence, routed.

**Grant (non-Windows host with an admitted self-hosted Stage 3/4 binary):** deploy the
pure-Simple executable as `bin/simple` for the checkout, then run the exact command
`bin/simple test test/01_unit/compiler/backend/vhdl_artifact_manifest_spec.spl` once.
If the 6 Gen2 provenance failures persist under the pure-Simple runtime, fix them per
the "Required correction" section (`src/compiler/80.driver/driver_vhdl_artifacts.spl`,
plus `driver_riscv_gen2_product.spl` for write-boundary failures) and record concrete
expected/actual per assertion.
