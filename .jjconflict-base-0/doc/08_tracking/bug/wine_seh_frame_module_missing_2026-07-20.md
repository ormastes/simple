# wine_seh_frame_spec.spl: `common.wine_seh_frame` module does not exist anywhere in src

**Status:** Open
**Category:** GENUINE-BUG (missing implementation, not a stale rename)
**Discovered:** 2026-07-20 (whole-suite triage campaign, shard meas_01u_03)

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/common/wine_seh_frame_spec.spl --no-session-daemon
```

```
error: semantic: Cannot resolve module: common.wine_seh_frame

error: test-runner: no examples executed

Passed: 0
Failed: 1
FAIL test/01_unit/lib/common/wine_seh_frame_spec.spl
```

## Minimal repro

`test/01_unit/lib/common/wine_seh_frame_spec.spl`:
```
use common.wine_seh_frame.{wine_seh_dispatch_fault, wine_seh_frame_new}
use common.wine_vm_adapter.{WineVmFault}

describe "Wine SEH frame-chain planner":
    it "plans SEH dispatch when a thread frame and mapped handler exist":
        val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
        val frame = wine_seh_frame_new(77, 12, 0x701000, 0x403000, 0x700000, 0x710000)
        val result = wine_seh_dispatch_fault(fault, [frame], 0x400000, 0x5000)
        expect(result.ok).to_equal(true)
        ...
```
(3 `it` blocks total, all exercising `wine_seh_dispatch_fault`/`wine_seh_frame_new`.)

## Root cause

`common.wine_vm_adapter` resolves fine (`src/lib/common/wine_vm_adapter.spl`
exists and exports `WineVmFault`), but **no file named `wine_seh_frame.spl`
exists anywhere under `src/`**, and none of the symbols the spec imports
(`wine_seh_dispatch_fault`, `wine_seh_frame_new`) or references
(`seh-dispatch-planned`, `seh-handler-mapped`, `seh-frame-chain-present`,
`seh-handler-unmapped`, `seh-dispatch-blocked`, `seh-policy:`) appear
anywhere else in the source tree (`grep -rl` for both the module filename
pattern `*seh*.spl` and the string constants returns nothing relevant).

This is not a rename/migration — the feature (a "Wine SEH frame-chain
planner": given a fault + candidate stack frames + an image base/size, decide
whether a Windows SEH handler dispatch can be planned, validating the
handler address falls inside the mapped image and that the fault policy is
`deliver-seh`) was apparently never implemented. The spec was likely authored
ahead of (or orphaned from) the implementation, alongside the sibling
`wine_vm_adapter` module which DOES exist.

## Why not classified STALE-TEST

There is no current API to migrate the spec onto — the entire module,
including the return-value shape (`result.ok`, `result.status`,
`result.handler_address`, `result.frame_count`, `result.evidence`,
`result.error`), is absent. Implementing `src/lib/common/wine_seh_frame.spl`
from scratch is out of scope for this triage pass (src/** edits are
restricted to unambiguous one-line import/rename fixes only).

## Suggested fix

Implement `src/lib/common/wine_seh_frame.spl` exporting `wine_seh_frame_new`
(constructor taking `process_id, thread_id, frame_addr, handler_addr,
stack_base, stack_limit` per the call sites) and `wine_seh_dispatch_fault`
(taking `fault: WineVmFault`, `frames: [WineSehFrame]`, `image_base: i64,
image_size: i64`) returning a result struct with `ok: bool, status: string,
handler_address: i64, frame_count: i64, evidence: [string], error: string`
per the three `it` blocks' expectations. Alternatively, if the feature was
deliberately dropped, delete the orphaned spec (requires user approval per
project rules — do not delete without explicit sign-off).

## Affected specs

- `test/01_unit/lib/common/wine_seh_frame_spec.spl` (sole affected spec in this shard)
