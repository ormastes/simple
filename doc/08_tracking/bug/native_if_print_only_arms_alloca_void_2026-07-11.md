# BUG: native path — statement-form `if` with print-only arms emits `%lN = alloca void` (invalid IR)
## Closed 2026-09-16 — ...recorded in `3f6dbe1b4abd`. ## Resolution Statement-form Unit results no longer require an

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status (2026-07-15):** source implemented; historical native/oracle
regression evidence is recorded in `3f6dbe1b4abd`.

## Resolution

Statement-form Unit results no longer require an LLVM `void` stack slot. The
backend materializes any dead spill slot as the universal `i64` word, while
value-producing `if` and `match` expressions retain their real type. No fresh
execution was performed during the 2026-07-15 source audit.

## Symptom

On the normal native path (`env -u SIMPLE_BOOTSTRAP` + forced worker), a
statement-form `if` whose arms contain only `print` statements emits
`%lN = alloca void` in the LLVM module. `llc` rejects `alloca void`; the build
fails.

## Analysis

The if-expression lowering allocates a result slot even when the merged value
type is void (print-only arms produce no value). The slot allocation in
`70.backend` (MIR-to-LLVM) should be skipped when the merge type is void, or
MIR lowering should not synthesize a result local for statement-form `if`
with no value-producing arms.

## Repro shape

```
fn main() -> i64:
    if cond:
        print "a"
    else:
        print "b"
    0
```

(Exact failing probe was produced by the Wall-3 agent while building probe
fixtures; re-derive with the shape above on the normal native path.)

## Triage note (2026-07-17)

Confirmed fixed by commit `3f6dbe1b4abd` ("#169 materialize void spill slots as i64 (llc reject)", 2026-07-13). The commit directly addresses the `alloca void` symptom; commit message includes verified native==oracle regression evidence confirming the fix closes the gap.


## Verification 2026-11-25 (work/p2w4-ak-20261125, release/1.0.0)

Confirmed fixed; closure stands.

- Fix commit `3f6dbe1b4abd` ("fix(backend): #169 materialize void spill slots
  as i64 (llc reject)") is an ancestor of release/1.0.0 HEAD.
- Code inspection at HEAD: `translate_alloc` in
  `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:3674`
  materializes a void-typed spill slot as the universal `i64` word
  (`if raw_ty == "void": "i64"`), with the matching load/store arms
  (`core_codegen.spl:3754`, `:3779`) resolving the slot element type the same
  way, so `alloca void` can no longer be emitted for statement-form
  `if`/`match` unit temps.
- Execution limit: `bin/simple.exe test` is repo-wide blocked at this HEAD —
  the pinned seed (Rust v1.0.0-rc.1) rejects the `@representation_boundary`
  decorator added tree-wide by cfd89933699, so the named-repro execution
  could not be re-run on this Windows host. Verification is by commit
  ancestry + source inspection only.
