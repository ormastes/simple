# BUG: a nested `fn` declared inside a spec `it` block does not capture the block's locals — silently reads zero, or dies with "variable not found"

**Status: OPEN — re-verified 2026-09-18 on a freshly redeployed seed. Not a stale-binary artifact.**

## Re-verification 2026-09-18, and a much smaller repro

This matters because the host's deployed seed was found to be 12 days stale that
same day and was replaced (see
`seed_jit_optional_unwrap_returns_enum_box_2026-09-18.md`), which invalidated
every measurement taken against the old binary. Several records checked in that
pass turned out to describe already-fixed behaviour. **This one does not.** Both
arms still reproduce on a seed built from `origin/main` on 2026-09-18.

**Arm B, loud, in three lines — no lambda and no callback required.** Every
earlier repro in this record went through an `it`-block lambda handing a closure
to a function under test, which framed this as a closure-passing defect. It is
simpler than that: a nested `fn` cannot see the enclosing block's locals at all.

```simple
use std.spec

describe "nested fn captures the it-block local":
    it "reads a captured array through a nested fn":
        val buf: [i64] = [7, 8, 9]
        fn r(i: i64) -> i64:
            buf[i]
        expect(r(1)).to_equal(8)

    it "reads a captured scalar through a nested fn":
        val n = 42
        fn g() -> i64:
            n
        expect(g()).to_equal(42)

    it "reads the captured array inline (control)":
        val buf: [i64] = [7, 8, 9]
        expect(buf[1]).to_equal(8)
```

```
✗ reads a captured array through a nested fn
    semantic: variable `buf` not found
✗ reads a captured scalar through a nested fn
    semantic: variable `n` not found
✓ reads the captured array inline (control)
3 examples, 2 failures
```

Three facts this adds to the record:

- **It is not array-specific.** A plain `i64` local fails identically. The
  original write-up's `[u8]` fixtures made this look like a container-capture
  problem; it is not.
- **It is a SEMANTIC-phase error, not a runtime one.** The message is
  `semantic: variable ... not found`, so the nested `fn`'s body is resolved
  against a scope that never contained the block's locals. That places the fix in
  name resolution, not in closure capture or environment copying.
- **The inline control passes**, so the local itself is bound correctly; only the
  nested `fn`'s view of it is missing.

**Arm A, the silent one, also still reproduces.** This record's named victim
`test/01_unit/os/acpi/acpi_test.spl` was re-run on the new seed and still fails
with the exact numbers quoted below:

```
✗ extracts MMIO base from GAS address at offset 48   expected 0 to equal 4275044352
✗ reads legacy PM_TMR_BLK at offset 76 ...           expected 0 to equal 45064
✗ prefers X_PM_TMR_BLK GAS at offset 208 ...         expected 0 to equal 47104
10 examples, 7 passed, 3 failed
```

So the two arms are one defect seen through two call shapes: calling the nested
`fn` **directly** raises the loud resolver error, while handing it to another
function as a callback yields the dangerous silent zero. Any fix must be checked
against both, and the three-line repro above is the cheaper of the two to iterate
on.

## Scope note on the earlier "out of scope for this lane" verdict

The 2026-08-09 re-confirmation below closed with "no `.spl`/`.shs` root-cause fix
is available at this layer", on the standing "fix Simple, not Rust" rule. That
reasoning still holds about WHERE the defect lives, but the conclusion that it
cannot be worked has weakened: a Rust-seed fix was authored and landed on
2026-09-18 (`src/compiler_rust/.../mir/lower/lowering_stmt.rs`, PR #1090) when
that was where a defect actually was. Seed work is therefore available for this,
with the usual cost that it needs a seed rebuild to verify.

---

## Original record, retained

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Root cause

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

