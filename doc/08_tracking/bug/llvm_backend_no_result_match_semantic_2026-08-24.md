# LLVM backend does not lower `ResultMatchSemantic`

**Status:** FIXED 2026-08-24 in `838f5e2e08c` — see the "FIXED" section at the end of this record.
**Was:** Open — top remaining blocker for native-building `Result`-using stdlib modules
**Observed:** 2026-08-24
**Area:** 70.backend / LLVM lowering

## Relationship to the io_runtime blocker

Split out of `io_runtime_import_borrow_local13_native_build_2026-08-24.md`
(FIXED in `9e3eb1adccd`). That record's two defects — the expression-position
`if val` binding loss in the seed interpreter, and the Return borrow check
rejecting every `Ref`-containing function — are both fixed, and both of its
filed signatures now count **zero** on the io_runtime fixture.

This is the **third, distinct** defect that surfaced underneath them. It is
what now blocks `use std.nogc_sync_mut.io_runtime`.

## Reproduction

Seed built from the fixed tree; exit code read DIRECTLY into a variable on the
line after the command, never through a pipe.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ "$SEED" native-build control.spl -o control.bin
$ NB_RC=$?
NB_RC=1
```

## Verbatim error

```text
error: E-BACKEND-LLVM-INST-ResultMatchSemantic: LLVM backend does not lower ResultMatchSemantic at unknown location
error: semantic: panic: compile error: E-BACKEND-LLVM-INST-ResultMatchSemantic: LLVM backend does not lower ResultMatchSemantic at unknown location
```

Measured 7 occurrences on a `std.nogc_sync_mut.io.file_ops` fixture.

## Scope

Affects modules whose functions return `Result<...>` and match on it —
`io.file_ops` and `io_runtime` confirmed. Modules that do not reach this
instruction now native-build and run end to end (`std.common.math`,
`std.nogc_sync_mut.io.signal_stubs`, both verified NB_RC=0 with the produced
binary executed).

## Not this defect

Two further, independent MIR-lowering gaps were measured on the same pass and
are NOT this record:

- `std.common.text` — `MIR lowering error: unresolved method call: index_of`
- `std.nogc_sync_mut.fs` — `MIR lowering error: undefined variable Dir`

## Diagnostic-quality note

The error reports `at unknown location` — no file, line, or function. The same
gap on the interpreter side is what made the previous defect unlocalizable
until a provenance probe was added (`SIMPLE_DEBUG_UNDEFINED_VAR=1`, see the
parent record). Attaching a real span here is worth doing before investigating.

---

## FIXED 2026-08-24 — it was never a missing lowering

**Root cause: `ResultMatchSemantic` is a VERIFICATION WITNESS, not an
executable instruction.** Four executable backends rejected a marker that has
no runtime meaning.

Measured evidence, not reasoning:

- **Emit site** `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2848`
  appends the marker into the merge block **after** the entire match is already
  lowered — arm blocks, payload binds, `emit_copy` of each arm result, the
  default arm, `terminate_goto(merge_block)`, and `switch_to_block(merge_block)`
  all precede it. Nothing about the match's execution depends on it.
- **Provenance:** `git log -S ResultMatchSemantic` on that file returns exactly
  one commit — `8a27fa62644 feat: implement formal verification 2.0`.
- **Its only real consumer** is the Lean backend,
  `70.backend/backend/lean_mir_translate.spl:280`, which scans for it purely to
  recover the match shape (`witness_count`, scrutinee/ok/err/merge/payload ids).
  `60.mir_opt/mir_opt/perf_facts.spl:210` also reads it. Both read MIR, not
  backend output.
- **`50.mir/verification_region_effects.spl:296` already classes it with `Nop`.**

So the third category named in the investigation brief applies: a construct that
carries no execution semantics reaching backends that demanded one.

### Fix

Named no-op arm (`()`) in the four executable backends — deliberately **not**
deletion into `case _`, which is the `E-BACKEND-LLVM-INST-Unknown` panic arm and
which `50.mir/verification_semantic_coverage.spl` expects to stay named:

| backend | file |
|---|---|
| LLVM text | `70.backend/backend/_MirToLlvm/core_codegen.spl` |
| C backend | `70.backend/backend/_CBackendTranslate/instruction_lowering.spl` |
| x86_64 isel | `70.backend/backend/native/isel_x86_64.spl` |
| MIR interpreter | `95.interp/mir_interpreter.spl` |

The marker is still emitted and still consumed by the Lean backend — the
verification path is unchanged.

### Proof

Seed rebuilt from this tree first (`cargo build --release --bin simple`,
`BUILD_RC=0`); every exit code read DIRECTLY into a variable on the line after
the command, never through a pipe.

Baseline on the fresh seed — the filed signature **does** still reproduce:

```text
$ timeout 900 "$SEED" native-build control.spl -o control.bin > base.log 2>&1
$ NB_RC=$?
NB_RC=1
ResultMatchSemantic occurrences: 7
error: E-BACKEND-LLVM-INST-ResultMatchSemantic: LLVM backend does not lower ResultMatchSemantic at unknown location
```

After the fix, same seed, same fixture: **`ResultMatchSemantic occurrences: 0`**.

End-to-end positive proof on a minimal `Result` match (both arms, native binary
actually executed):

```text
$ timeout 900 "$SEED" native-build rm_min.spl -o rm_min.bin
$ NB_RC=$?
NB_RC=0
$ ./rm_min.bin
ok 42
err div by zero
$ RUN_RC=$?
RUN_RC=0
```

Both arms produce correct payloads — semantics preserved, not merely silenced.

### Regression gate

`scripts/check/check-result-match-semantic-lowering.shs` — `--selftest` runs
FIRST and is FATAL (6 fixtures, both directions); verdict LAST on stdout.
Measured: `PASS — 6 case(s) checked` exit 0. `--native` adds the real
native-build + execute case.

It pins **both** halves, because half a ratchet is how this class recurs:
the four backends must not reject the witness *and* must keep a named arm, and
the 50.mir emit site plus the Lean consumer must still be present — deleting the
marker outright would silently break the formal-verification backend.

Mutation-tested against the real tree in both directions:

| mutation | result |
|---|---|
| restore the original reject in `core_codegen.spl` | `FAIL — 6 case(s) checked, offender(s): ...(rejects-witness)` exit 1 |
| delete the named arm entirely | `FAIL — ...(no-named-arm)` exit 1 |
| delete the witness emit site in 50.mir | `FAIL — ...(witness-no-longer-emitted)` exit 1 |
| restored tree | `PASS — 6 case(s) checked` exit 0 |

### `io_runtime` is NOT yet green — a FOURTH blocker is underneath

Reported honestly rather than claimed fixed. With `ResultMatchSemantic` gone
(7 → 0 occurrences), the `io_runtime` control fixture still gives `NB_RC=1`, now
with an entirely different signature:

```text
error: semantic: type mismatch: cannot convert object to int
E-HIR-BLOCK-VALUE-TYPE-DECAYED: block tail expression type_ word became a
non-well-formed heap reference between capture and HirBlock construction;
substituting a placeholder
```

Filed separately as
`doc/08_tracking/bug/hir_block_value_type_decayed_object_to_int_2026-08-24.md`.
This record is closed on its own signature, which is measured at zero.

## Side measurement: the `Some(40)` binds as `320` (`<<3`) report does NOT reproduce

Checked on the same freshly-built seed, because two lanes today found filed
signatures counting zero on a fresh seed. Five shapes of i64 Option payload
binding, on BOTH the interpreter (`run`) and native (`native-build` + execute
the produced binary, `NB_RC=0` / `RUN_RC=0`):

| shape | expected | measured |
|---|---|---|
| `if val v = pick(true)` (statement form, fn returning `i64?`) | 40 | **40** |
| `val w = if val u = pick(true): u else: -1` (expression form) | 40 | **40** |
| `if val a = o` where `val o: i64? = Some(40)` | 40 | **40** |
| `if val b = arr.first()` | 40 | **40** |
| `match o: case Some(c)` | 40 | **40** |

No `<<3` tag-width leak observed in any of them. The report predates
`4cc714ece3e` / `51a7b28e220` / `9e3eb1adccd`; it is most likely already fixed
by one of those. **No bug record filed** — filing one for a signature measured
at zero would be exactly the stale-record failure this repo keeps hitting. If
the `320` behaviour is seen again, it needs a fresh reproduction against a
freshly-built seed before it is treated as live.
