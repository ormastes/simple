# `native-build` of an `io_runtime` importer: `Option`/`Result` unresolved in three io modules

**Status:** RESOLVED 2026-08-24 — `native-build` reaches `NB_RC=0` and the binary runs. SEVENTH blocker in the `io_runtime` native-build chain
**Observed:** 2026-08-24
**Area:** 20.hir / 35.semantics (callable dependency origin resolution),
`std.nogc_sync_mut.io.{file_ops,process_ops}`, `std.nogc_sync_mut.io_runtime`
**Predecessor:** `native_compile_explicit_panic_diverging_process_ops_2026-08-24.md`
(blocker #6, RESOLVED — the LLVM `Abort` terminator routed through the
fail-the-build `emit_unsupported_panic` helper)

## Position in the chain

Blockers 1-6 are fixed. With blocker #6's spurious compile error removed, the
`explicit panic()` signature is **gone** (5 occurrences -> 0), and
`native-build` now fails on this, a **different and independent** defect.

This was **not** unmasked by the #6 fix in the sense of being caused by it —
it was reported alongside #6 all along, in that record's "Context reported
alongside" section, where its causal relationship was explicitly listed as
unmeasured. It is now measured: independent.

## Reproduction

Seed rebuilt from the fixed tree (`cargo build --release --bin simple`, rc=0).
Exit code read DIRECTLY into a variable on the line after the command.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ timeout 900 "$SEED" native-build lanework/control.spl -o lanework/control.bin
$ NB_RC=$?
NB_RC=1
```

```text
error: build failed: 3 failed, 0 unverified, 0 not run, 3 ok of 6 unit(s)
  ERROR: std.nogc_sync_mut.io.file_ops, std.nogc_sync_mut.io.process_ops,
         std.nogc_sync_mut.io_runtime
```

## The correlation that identifies it

The three ERROR modules are **exactly** the three owners of an
`Option`/`Result` dependency-origin report — no more, no fewer:

```text
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops     dependency=Option
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops     dependency=Result
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.process_ops  dependency=Option
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.process_ops  dependency=Result
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime      dependency=Option
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime      dependency=Result
```

each reading:

> no declaration, re-export hop, or explicit import of this name in the owner;
> a later `unresolved type: Option` will be reported against an importing
> module instead

A fourth module, `std.nogc_sync_mut.io.signal_stubs`, carries the same report
for `dependency=fn` but is **not** in the ERROR set — worth understanding, as
it may discriminate the mechanism.

## Note on the diagnostic itself

The report predicts its own downstream symptom ("will be reported against an
importing module instead") — i.e. the compiler already knows the blame is
being attributed to the wrong module. That misattribution is itself worth
fixing: it is the same "diagnostics that lie" half of this chain's recurring
family, and it is why this defect sat classified as background noise while six
other blockers were chased.

## Not yet measured

- Whether `Option`/`Result` genuinely lack an import/re-export hop in those
  three modules (a real source defect) or whether the origin resolver fails to
  follow a hop that exists (a compiler defect). **Not yet determined — do not
  assume the latter because the previous six blockers were compiler defects.**
- Why `signal_stubs` reports the same class but does not ERROR.
- The actual per-module error text. The `3 failed` summary names the modules
  but the underlying `unresolved type:` lines were not located in the captured
  stderr; the full stream is saved to a named file (see below) and should be
  re-read rather than inferred.

## Note on stderr truncation

The worker's stderr is middle-dropped. The full stream is saved to a named
file (`[native-build] FULL stderr (NNNNN bytes) saved to: /mnt/data/tmp/...`).
Read that file; the console output is explicitly labelled unreliable by the
tool itself.

## Operational note

`timeout` kills the `native-build` parent but the `native_build_worker.spl`
child can survive as a multi-GB, 100%-CPU orphan. Check
`pgrep -af native_build_worker.spl` after any interrupted reproduction, and
kill only PIDs belonging to your own working directory — other lanes run their
own workers.

## Gate

Blocker #6's gate
(`scripts/check/check-llvm-abort-terminator-not-unsupported.shs`) asserts the
ABSENCE of the `explicit panic()` signature and, without `--require-success`,
deliberately reports this residual rc=1 by name rather than failing on it.
Three gates in this chain now hold a `--require-success` flag that is
deliberately **NOT** the default, all waiting on exactly this bug:

- `scripts/check/check-hir-block-tail-and-loadglobal-decode.shs`
- `scripts/check/check-ssa-block-reach-not-exponential.shs`
- `scripts/check/check-llvm-abort-terminator-not-unsupported.shs`

Flip all three to require success once `native-build` reaches rc=0.


---

# RESOLUTION (2026-08-24)

**`NB_RC=0`.** The seed was rebuilt from this tree first
(`cargo build --release --bin simple`, rc=0); every exit code below was read
DIRECTLY into a variable on the line after its command, never through a pipe.

```text
$ timeout 1800 "$SEED" native-build lanework/control.spl -o lanework/control.bin
$ NB_RC=$?
NB_RC=0                      (was 1)

$ ./lanework/control.bin
$ RUN_RC=$?
RUN_RC=0    stdout: control ok        (interpreter oracle: control ok)
```

## The filed signature was a red herring — disproven, not merely doubted

The "correlation that identifies it" section above does not survive
measurement, and this record's earlier framing should not be reused.

`Option`/`Result` were never unresolved, and the eprint was never the failure.
The three ERROR modules coincide with the three eprint owners for a trivial
reason: they are **exactly the three io modules that mention `Option`/`Result`
in a callable signature** (`file_ops` 3, `process_ops` 5, `io_runtime` 2).
`io.signal_stubs` — the discriminator this record correctly flagged as worth
understanding — has **zero** `Option`/`Result` mentions, carries the same
advisory for `dependency=fn`, and does not ERROR. The correlation is with
"names the type in a signature", not with "fails to build".

The advisory is moreover **noise-by-design and documented as such**:
`hir_dependency_is_builtin_type` (`module_reexport_materialization.spl:1320-1330`)
deliberately leaves the container spellings (`Option`/`Result`/`Dict`/...)
unfiltered, because 42 `Result` and 14 `Option` real user declarations exist in
this tree and filtering them would stop materializing a genuine user type.

This is the third time in this chain that a headline log line named something
other than the defect (see blocker #4's tautology). **The per-unit reasons were
sitting in the build outcome summary the whole time** — `build_outcome.spl`
prints a `reason:` line per non-OK unit — and reading them, rather than the
eprints, resolved this in one step. The record's own "Not yet measured" note
was right to demand exactly that.

## Actual root cause: two INDEPENDENT llc rejections of malformed IR

Both had to be fixed; fix A alone took `3 failed` -> `1 failed`.

### A. `multiple definition of local value named 'lN'` (file_ops, io_runtime)

`ssa_alloca_transform_blocks` (`var_reassign_ssa.spl`) is the
mem2reg-equivalent that slots every multi-def local so the textual LLVM path
cannot emit a duplicate SSA def. Its instruction gate,
`ssa_instructions_supported_for_alloca`, rejected the **whole function** on
sight of `ResultMatchSemantic` — a verification-only witness that
`mir_instruction_kinds.spl` itself documents as having *"no runtime effect.
Backends may erase"*. Every function containing the canonical two-arm `Result`
match therefore kept its merge destination un-slotted and written once per arm:

```llvm
bb2:  %l4 = getelementptr i8, ptr %l8, i64 0   ; copy      <- def 1
bb4:  %l4 = getelementptr i8, ptr %l13, i64 0  ; copy      <- def 2, llc rejects
bb1:  ret ptr null                                        <- and the value was dropped
```

That is **every two-arm `Ok`/`Err` match in value position**, reproduced by a
10-line standalone fixture with no io involvement at all:

```simple
fn tail_match(n: i64) -> text:
    match pick(n):
        case Ok(content): content
        case Err(_): ""
```

Measured before any fix was written: an instrumented run named the rejecting
variant outright (`alloca-unsupported RESULTMATCHSEMANTIC`). Fixed by admitting
it to the gate alongside `CallIndirect`/`Alloc`/`Store`/`LoadGlobal`/
`StoreGlobal`, which that gate's own docstring records as having been added for
the **identical** failure mode (#135).

Note the `ret ptr null` above: this defect had a silent-wrong-answer sibling.
A dedup-only fix would have compiled a binary that returns null on one path,
which is worse than rc=1. That is why the gate RUNS the fixture and asserts
both arm values rather than asserting compilation.

### B. `'%lN' defined with type 'i32' but expected 'i64'` (process_ops)

`translate_ref` (`aggregate_intrinsics.spl`) hardcoded `native_int()` for a
borrow, which is the identity on the borrowed place. Correct only when the
place is i64; an i32/i1/f64/ptr place emitted `add i64 %lN, 0` over a
differently-typed value. Now type-directed off the place's registered type,
mirroring `translate_copy_move` (including the `-0.0` float form that preserves
negative zero).

## Which recurring shape this was

Both halves are the chain's **shape #1** — *a supported construct misclassified
by a fail-closed hardening*, the same as blockers #3 and #6. Notably #3 was
**also** about `ResultMatchSemantic`: that witness has now caused two separate
blockers by being present in IR that consumers were not taught to tolerate.
Worth watching as a third-strike candidate.

It was **not** shape #2. The prediction that "erased generics are the boundary
where five defects have hidden" did not hold here — erasure was innocent.

## Fix

- `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl` (+17)
- `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl` (+27/-3)

41 insertions, 3 deletions total. No semantics changed for any construct that
already compiled: fix A only widens which functions the existing slot transform
is allowed to run on, and fix B only replaces a hardcoded type with the real
one.

## Evidence

| check | result |
|---|---|
| `native-build lanework/control.spl` | `NB_RC=0` (was 1) |
| `./lanework/control.bin` | `RUN_RC=0`, prints `control ok`, matches interpreter |
| 10-line tail-match repro, build | `F1_RC=0` (was 1) |
| 10-line tail-match repro, run | `RUN_RC=0`, both arms correct vs interpreter |
| `cargo check --release --bin simple` | `CARGO_CHECK_RC=0` |
| fix A reverted, gate `--build` | `FAIL`, reproduces `multiple definition of local value named 'l4'` |
| fix B reverted, real `control.spl` | `NB_RC=1`, `1 failed ... ERROR: std.nogc_sync_mut.io.process_ops` |
| both restored | `PASS` |

Native `print` emits no trailing newline. Verified **pre-existing and
unrelated** with a three-print control containing no match and no borrow
(`A`,`""`,`B` -> `AB`), so it is not laundered into this record as a pass.
It remains an open defect owned elsewhere.

## Gate

`scripts/check/check-llvm-value-match-and-borrow-ir-valid.shs` — `--selftest`
first and fatal (6 fixtures), verdict last, `PASS`/`FAIL`/`ERROR` with a
0-check run forced to ERROR. `--build` compiles a fixture carrying BOTH defect
shapes under `timeout`, classifies `rc=124` as a DISTINCT HANG, and then
**executes** the binary asserting both arm values.

Mutation-tested in both directions against the REAL tree, not just fixtures:
reverting fix A yields `FAIL ... multiple definition of local value named 'l4'`;
reverting fix B yields three named offenders and `NB_RC=1` on the real
`control.spl`; restoring both yields `PASS`. The selftest additionally pins the
two ways a source-text gate lies: a variant that is **named but rejected**
(`return false`) must FAIL, and a **comment** naming the old form must not
false-positive.

## The three staged gates are now flipped

All three held a `--require-success` flag deliberately defaulted off, waiting
on exactly this. Each now defaults to REQUIRED, with
`--allow-residual-failure` as an explicit, recorded opt-out for a lane
knowingly mid-repair. Each was verified genuinely green **with a real
native-build**, not merely selftested:

- `check-hir-block-tail-and-loadglobal-decode.shs` — `PASS - 2 case(s) checked, 0 E-HIR-BLOCK-VALUE-TYPE-DECAYED and 0 object-to-int, native-build of an io_runtime importer exited 0`
- `check-ssa-block-reach-not-exponential.shs` — `PASS - 2 check(s) run, ... native-build terminated with exit 0 within 600s (NOT a hang)`
- `check-llvm-abort-terminator-not-unsupported.shs` — `PASS — 6 check(s) run, ... native-build rc=0`

## What this unblocks, and what it does NOT prove

`native-build` of an `io_runtime` importer now produces a working binary, which
unblocks the Stage 3 self-host investigation.

It does **not** prove self-hosting. Scope honestly: one importer, one
`native-build`, one run. In particular `io_runtime.read_file` still aborts the
process under `bin/simple run` — a separate, still-open defect
(`io_runtime_read_file_still_aborts_incomplete_fix_2026-08-24.md`) that this
change does not touch and must not be read as having fixed.
