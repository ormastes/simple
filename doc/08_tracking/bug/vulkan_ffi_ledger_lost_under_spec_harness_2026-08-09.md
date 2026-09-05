# `VulkanFfi` rejection ledger never accumulates under the spec harness (works under `bin/simple run`)

**Filed:** 2026-08-09 (stream F4)
**Subject:** `src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl`
**Status:** root cause NOT isolated. Two candidate factors narrowed, both
common suspects eliminated. Recorded with a reproducer rather than a guess.

## Summary

`VulkanFfi` documents an "honest rejection ledger": in Dynamic mode every
operation that the raw `call0..call4(i64...)` FFI cannot marshal must return
false/0 **and** be counted, via `rejected_op_count()` / `last_rejection()`.

That ledger works under `bin/simple run` and is **completely inert under the
spec harness** (`bin/simple test`). Same binary, same source, same host.

| step | `bin/simple run` | `bin/simple test` |
|---|---|---|
| fresh | `count=0 last=[]` | `count=0 last=[]` |
| after `init()` | `count=1 last=[init]` | **`count=0 last=[]`** |
| after `shutdown()` | `count=2 last=[shutdown]` | **`count=0 last=[]`** |
| after `select_device(0)` | `count=3 last=[select_device]` | **`count=0 last=[]`** |

The mutation is silently dropped. Nothing warns.

## Why this matters beyond one class

A spec asserting this contract does not fail loudly with a wrong number — it
sees the *initial* state forever. A spec written to assert "count stays 0"
would pass while testing nothing, which is exactly the tautology-shell
failure mode catalogued in
`gated_specs_are_tautology_shells_2026-08-09.md`. Any `me`-method state
accumulation asserted under the harness is suspect until this is understood.

## What was eliminated

Both obvious hypotheses were tested under the spec harness and **behave
correctly**, so neither is the cause:

1. **Plain minimal class with a `me` mutator** — a local `class Ledger` with
   `me record(op)` incrementing an `i64` and assigning a `text` field:
   `count=2 last=[shutdown]`. Correct.
2. **Mutator defined inside a trait impl block** — `VulkanFfi`'s
   `_dyn_reject_bool` lives inside `impl FfiDispatchBase for VulkanFfi`,
   which is unusual. A minimal class reproducing that exact shape
   (mutator + readers in the trait impl, entry point in the plain impl):
   `count=2 last=[shutdown]`. Correct.

Also eliminated: whether the return value is consumed. Discarding it
(`ffi.init()`), binding it (`val r = ffi.init()`), and consuming it
(`expect(ffi.init())`) all give `count=0` under the harness.

## Remaining candidate factors (untested)

- The `_dyn_lib: DynLib?` field — an optional foreign handle. The minimal
  repros had no such field. A class holding a foreign resource may be
  copied rather than referenced on method dispatch.
- `match self._mode` enum dispatch inside the mutating method. Compare the
  known-bad `match` on enum lowering noted elsewhere in the tracker.

Whoever picks this up should bisect by adding a `DynLib?` field to the
minimal repro first — that is the cheapest discriminator.

## Reproduce

```bash
cat > test/01_unit/lib/gpu/engine2d/f4_repro_spec.spl <<'EOF'
use std.spec.{describe, it, expect}
use std.nogc_sync_mut.gpu.engine2d.ffi_vulkan.{VulkanFfi}

describe "repro":
    it "traces the ledger":
        val ffi = VulkanFfi.create_dynamic()
        if ffi == nil:
            print("nil\n"); return
        print("s0 count={ffi.rejected_op_count()} last=[{ffi.last_rejection()}]\n")
        val a = ffi.init()
        print("s1 count={ffi.rejected_op_count()} last=[{ffi.last_rejection()}]\n")
        val b = ffi.shutdown()
        print("s2 count={ffi.rejected_op_count()} last=[{ffi.last_rejection()}]\n")
        expect(1).to_equal(1)
EOF
SIMPLE_MODULE_LIMIT=4000 SIMPLE_TIMEOUT_SECONDS=3600 SIMPLE_GPU_TEST=1 \
  bin/simple test test/01_unit/lib/gpu/engine2d/f4_repro_spec.spl
```

Then compare against the same sequence in a `fn main()` run with
`bin/simple run`.

## Spec status — deliberately RED

`test/01_unit/lib/gpu/engine2d/ffi_vulkan_spec.spl` case
*"starts empty, then counts and names each rejected operation"* is **left
failing** (`expected  to equal shutdown`). Per the F4 brief, a real test
that uncovers a real defect stays RED; trimming the assertion until it
passes is how this class of problem started. The other three cases in that
file pass and were sabotage-proven.

Verbatim:

```
SPEC FILE VERDICT: test/01_unit/lib/gpu/engine2d/ffi_vulkan_spec.spl declared>=4 executed=4 passed=3 failed=1 dropped=0
```

## Harness note discovered alongside

The harness prints only **one** failure line per `it`, and it is the *last*
failed assertion, not the first. The run above reported only
`expected  to equal shutdown` although the two preceding count assertions
had failed too. Reading a single failure message as "only one assertion
failed" is a mistake.
