# LLVM backend: narrow struct-field readback emits mistyped load → llc rejects
## Closed 2026-09-16 — RESOLVED: commit `09bee48d1a5` loads the physical native-width slot, then truncates to the declared narrow width

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## 2026-11-25 verification (work/p2w4-ae-20261125, origin/release/1.0.0 HEAD ef6a94f8a03)

`git merge-base --is-ancestor 09bee48d1a5 HEAD` confirms the resolution
commit (`fix(backend/llvm): trunc narrow struct-field loads to declared
width; cache writer creates parent dirs`) is in release/1.0.0. End-to-end
re-run of the llc lane was not attempted (interpreted native-build worker +
llc lane, Linux/macOS-oriented; pinned seed cannot compile at this HEAD due
to the repo-wide `@representation_boundary` rejection). Closure stands on the
recorded IR-level evidence plus commit ancestry. (Header line repaired: the
2026-09-16 normalization splice had mangled it.)

**Filed:** 2026-07-19 · **Status:** SOURCE FIXED / FOCUSED LLVM-IR REGRESSION ADDED · **Area:** LLVM backend / struct field access
**Lane:** interpreted native-build worker (`SIMPLE_NATIVE_BUILD_WORKER=1
bin/simple run src/app/cli/native_build_worker.spl --backend llvm ...`,
llc from /opt/homebrew/opt/llvm/bin). Pre-existing; surfaced while verifying
the omitted-defaulted-field fill fix.

## Symptom
Reading back a NARROW-typed struct field (`k: i32`, `flag: bool`) loads the
64-bit slot as `i64` but then widens it assuming the narrow type, producing
ill-typed IR that llc rejects:

```
%l6 = load i64, ptr %t6      ; field slot load (i64)
%t7 = sext i32 %l6 to i64    ; llc: '%l6' defined with type 'i64' but expected 'i32'
```
bool variant: `%l12 = load i64` then `zext i1 %l12 to i64`.

Store side is fine (widened to i64 slots correctly: `zext i1 ... to i64`).
i64-typed fields round-trip cleanly.

## Repro
`struct Cfg: name: text; k: i32 = 5; flag: bool = true` + `print
"k={c.k} flag={c.flag}"`, compile via the worker lane above → llc exit 1
with the sext/zext type error. All-i64 fields → compiles.

## Expected
Either load the slot as i64 and truncate (`trunc i64 -> i32/i1`) before the
widening, or emit typed loads matching the declared field width. The
mismatch is in the field-access lowering's readback of sub-64-bit fields
(struct slots are uniformly 8 bytes).

## Resolution

Commit `09bee48d1a5d` loads the physical native-width slot into a fresh SSA
temporary, then truncates it to the field's declared `i32`/`i16`/`i8`/`i1`
width. This keeps later sign/zero extension well typed without changing the
uniform aggregate layout. The focused LLVM-IR regression covers `i32` and
`bool` and rejects direct native-word definitions of the narrow destinations.

## Verification-lane notes (2026-07-19 evening)
Two additional infra findings while attempting the all-i64 end-to-end run:
1. **native cache writer does not `mkdir -p`**: after a cache clear
   (`build/native_cache` removed), object write fails with "Failed to write
   ELF bytes to build/native_cache/backend=llvm;...;/sources-.../object...o"
   — pre-creating the exact directory lets the write proceed. The writer
   should create parent dirs.
2. The interpreted native-build worker lane compiles the LIVE `src/compiler`
   tree; under concurrent agent sessions rewriting compiler source, each run
   can fail differently (lint-class aborts, transient semantic errors).
   End-to-end verification on this lane needs a quiescent tree or a pinned
   worktree. The defaulted-field fix's IR-level verification (store 5/true)
   was captured on a coherent tree and stands.

