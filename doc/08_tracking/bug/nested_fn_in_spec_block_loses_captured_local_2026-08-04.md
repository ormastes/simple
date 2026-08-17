# BUG: a nested `fn` declared inside a spec `it` block does not capture the block's locals — silently reads zero, or dies with "variable not found"

**Status:** OPEN

**Re-confirmed 2026-08-09:** independently re-verified rather than assuming the
sibling's family-match. Ran a fresh minimal repro (nested `fn r8` capturing an
`it`-block `val buf`, passed as a callback) through `bin/simple test
--no-cache --no-cover-check` on the deployed Rust seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, seed banner confirmed via
`--version`). The run is consistent with this doc's existing Arm A/B repros
(same seed, same construct class: nested `fn` inside an `it`-block lambda
referencing a lambda-local). Root cause and scope are unchanged from the
original write-up: this lives in the Rust seed's interpreter closure/scope
handling (`src/compiler_rust/compiler/src/interpreter*`), not in any `.spl`/
`.shs` source this lane may edit, and fixing it would require a seed rebuild
mid-session while other sessions are live in this tree — squarely against the
"Fix .spl not Rust" / "Pure Simple First" standing rules. No `.spl`/`.shs`
root-cause fix is available at this layer.
**Verdict: confirmed, left OPEN — architectural (Rust-seed interpreter),
out of scope for this lane.**
**Found:** 2026-08-04
**Severity:** high — the silent arm produces **wrong values with no error**, so
affected specs fail with plausible-looking assertion mismatches that read like
product bugs. `test/01_unit/os/acpi/acpi_test.spl` (3 failed) is one victim;
the pattern ("build a `[u8]` fixture, hand `read8`/`read32` closures to the
function under test") is a common way to unit-test byte-parsing kernel code.

## Symptom

Two arms, same construct. Both reproduce on the interpreter lane that
`bin/simple test` uses.

### Arm A — silent zero (the dangerous one)

`test/01_unit/os/acpi/acpi_test.spl`:

```
✗ extracts MMIO base from GAS address at offset 48
    expected 0 to equal 4275044352
✗ reads legacy PM_TMR_BLK at offset 76 for ACPI 1.0 FADT
    expected 0 to equal 45064
✗ prefers X_PM_TMR_BLK GAS at offset 208 for ACPI 2.0+ FADT
    expected 0 to equal 47104
```

Minimal self-contained repro (run with
`bin/simple test --no-cache --no-cover-check <file>`):

```
use std.spec
use os.kernel.acpi.hpet_table.{acpi_hpet_base_raw, GAS_SPACE_SYSTEM_MEMORY}

fn _make_hpet_table(mmio_lo: u32, mmio_hi: u32) -> [u8]:
    var buf: [u8] = []
    var i: u64 = 0
    while i < 64:
        buf = buf + [0]
        i = i + 1
    buf[44] = GAS_SPACE_SYSTEM_MEMORY
    buf[48] = (mmio_lo & 0xFF) as u8
    buf[49] = ((mmio_lo >> 8) & 0xFF) as u8
    buf[50] = ((mmio_lo >> 16) & 0xFF) as u8
    buf[51] = ((mmio_lo >> 24) & 0xFF) as u8
    buf

fn _buf_read8(buf: [u8], off: u64) -> u8:
    buf[off as i64]

fn _buf_read32(buf: [u8], off: u64) -> u32:
    val b0 = buf[(off + 0) as i64] as u32
    val b1 = buf[(off + 1) as i64] as u32
    val b2 = buf[(off + 2) as i64] as u32
    val b3 = buf[(off + 3) as i64] as u32
    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)

describe "acpi repro":
    it "fixture bytes are right":                     # PASSES
        val buf = _make_hpet_table(0xFED00000, 0)
        expect(_buf_read32(buf, 48) as u64).to_equal(4275044352)
    it "product fn via nested-fn callbacks":          # FAILS: expected 0 to equal 4275044352
        val buf = _make_hpet_table(0xFED00000, 0)
        fn r8(off: u64) -> u8: _buf_read8(buf, off)
        fn r32(off: u64) -> u32: _buf_read32(buf, off)
        val result = acpi_hpet_base_raw(r8, r32, 0)
        expect(result as u64).to_equal(4275044352)
```

The first example proves the fixture and the arithmetic are correct — the same
buffer read directly yields `4275044352`. Only the route through the nested-fn
callbacks yields `0`.

### Arm B — hard error

Calling the nested fn *directly* inside the same `it` block instead of passing
it on:

```
it "val-bound: via nested fn":
    val buf = _mk()
    fn r8(off: u64) -> u8: _rd8(buf, off)
    expect(r8(3) as u64).to_equal(77)
# ✗ semantic: variable `buf` not found
```

## What was ruled out (each probed, each refuted)

This took four wrong hypotheses; recording them so nobody re-walks them:

| hypothesis | probe result |
|---|---|
| `.push()`/array writes don't persist (value-type arrays) | **Refuted.** `.push()` mutates in place; discard vs. reassign both give `len=1`, interpreter *and* JIT |
| the u32 byte-split/recombine math is wrong | **Refuted.** Standalone probe: bytes `0,0,208,254`, recombined `4275044352`, `mmio_phys` `4275044352` |
| nested-fn closure capture is broken generally | **Refuted.** Inside a plain `fn main`, all of direct-index / via-helper / via-nested-fn / nested-fn-passed-as-arg return `77` |
| imported module-level `val` constants resolve to 0 | **Refuted.** `HPET_TBL_OFF_GAS == 44` and `HPET_TBL_GAS_OFF_ADDRESS == 4` assert green when imported into a spec |

The distinguishing variable is the **enclosing scope**: the identical nested-fn
construct works inside `fn main` and fails inside an `it` block. `it` bodies are
lambdas, so capture of a lambda-local by a nested `fn` declared in that lambda
is the broken case.

Note one further wrinkle, not yet explained: a nested fn passed as a callback
that is invoked with a *constant* offset **does** work
(`use_cb(r8)` reading offset 3 returned `77`), while the acpi case — where the
callee computes the offset (`base + HPET_TBL_OFF_GAS + …`) — returns 0. So Arm A
may be a second, distinct arm rather than the same capture failure; whoever
picks this up should bisect that boundary before assuming one fix covers both.

## Root cause (ISOLATED 2026-08-17 — exact call-resolution ordering)

**Re-reproduced 2026-08-17** on the deployed seed
(`bin/release/x86_64-unknown-linux-gnu/simple`) with a new self-contained spec,
`test/03_system/interpreter/nested_fn_captures_block_local_spec.spl`:

```
  ✗ nested fn reads a block-local array
    semantic: variable `buf` not found
  ✗ nested fn reads a block-local scalar
    semantic: variable `base` not found
  ✗ nested fn composes two block locals
    semantic: variable `lo` not found
Results: 4 total, 1 passed, 3 failed
```

The one PASSING example is the discriminator: *"nested fn passed as a callback
reads a block-local array"* passes, because a callback is called through the
`Value::Function` value (which carries `captured_env`), while a **call by
name** is not. Three-line mechanism, all in `src/compiler_rust/compiler/src`:

1. `interpreter_call/block_execution.rs:716-732` — a `Node::Function` inside a
   block closure (`it` block) is registered **twice**: into the global
   `functions` map (line 722, "so recursive calls can find it") *and* into
   `local_env` as a `Value::Function` carrying `captured_env` (line 725-732).
2. `interpreter_call/mod.rs:525` — "Priority 5: check regular functions" looks
   in the `functions` map and wins, **before** "Priority 6: check env" at line
   536 which is the only branch that would honour `captured_env`.
3. `interpreter_call/core/function_exec.rs:826` (and 1215/1303/1392) —
   `exec_function*` builds its frame with
   `captured_env_with_live_globals(func, &Env::new())`, i.e. an **empty**
   captured environment. The block's locals are gone; the read either errors
   (`variable X not found`, arm B) or resolves to a same-named global/zero
   (arm A, the silent one).

Contrast: the plain statement path `interpreter/node_exec.rs:388-399` inserts
the nested `fn` into `env` **only** (never into `functions`), so outside a spec
block Priority 5 misses and Priority 6 correctly supplies `captured_env` —
which is exactly why this defect is spec-block-specific.

Fix shape: at `interpreter_call/mod.rs:525`, prefer an env-resident
`Value::Function` with a non-empty `captured_env` over the same-named entry in
the `functions` map (or stop double-registering at
`block_execution.rs:722` and give the `functions`-map fallback the captured
env). Not applied in this pass: the fix lands in `interpreter_call/**`, outside
the editing lane assigned to this session, and verifying it requires a Rust
seed rebuild + redeploy while a bootstrap is live.

## Root cause (original wording, superseded above)

Not isolated to a specific line. The construct is a nested `fn` declaration
inside a lambda (`it` block) referencing a binding from the lambda's scope.
Arm B's `semantic: variable X not found` shows the capture environment for the
nested fn simply does not include the enclosing lambda's frame; Arm A shows a
path where, instead of erroring, the read yields `0`.

The failing lane is the seed interpreter — `bin/simple` here is the Rust
bootstrap seed (57MB, 2026-08-04, prints the seed banner) and specs run
`[mode: interpreter]`.

## Why not fixed now

The fix is in interpreter scope/closure handling in the **Rust seed**
(`src/compiler_rust/compiler/src/interpreter*`), which is outside this lane's
scope (`src/os/`, `src/lib/nogc_async_mut_noalloc/`) and against the standing
"Fix .spl not Rust" / "Pure Simple First" rules; it also forces a seed rebuild
while other sessions are live in this tree.

It must **not** be papered over by rewriting `acpi_test.spl` to avoid nested
fns: `acpi_hpet_base_raw` takes `read8`/`read32` function parameters by design
(`src/os/kernel/acpi/hpet_table.spl:40`) precisely so it can be unit-tested
against a fixture instead of real MMIO. Removing the callbacks would delete the
only hosted test of that parser.

The product code itself is **not** implicated: `acpi_hpet_base_raw`
(`hpet_table.spl:40-54`) reads correctly when driven by the same helpers
outside a lambda.

## Collateral: three acpi examples pass for the wrong reason

Because the silent arm yields `0`, `mmio_phys` comes out `0` and the function
returns `nil` — which is what the three negative tests assert. So
`returns nil when address_space_id is not SystemMemory`,
`returns nil when MMIO address is zero`, and the FADT equivalents are currently
**green regardless of the product's behaviour**. They will need re-checking
once the capture defect is fixed.

## Measurement note

`--no-cache --no-cover-check` are mandatory: without them a directory can report
`No test files found … Results: 0 total` and exit 0 (concurrent runs rewrite a
shared path-scoped manifest), and a missing `@cover` annotation aborts the run
so zero specs execute. Treat any `0 total` as **unmeasured**, not passing.
