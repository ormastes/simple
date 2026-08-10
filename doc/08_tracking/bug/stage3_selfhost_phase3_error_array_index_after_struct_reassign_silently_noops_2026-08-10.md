# Stage-3 self-host — indexing `self.ctx.errors` right after `self.ctx = <returned struct>` silently produces no output

- **ID:** stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10
- **Status:** ROOT-CAUSED (narrowly), NOT FIXED. Found as a side effect of chasing
  Stage-3 self-host's phase-3 HIR failure (see
  `stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md` for
  the overall campaign chain). Distinct from, and downstream of, the bare-`Result`
  fix landed at `67055c4d3f1`.
- Area: pure-Simple native codegen — array field access immediately after a
  struct-typed local is reassigned from a function's return value.

## What was observed

`src/compiler/80.driver/driver_orchestration.spl`'s `compile()`, phase 3 failure
branch (~line 142 onward):

```
val (analyzed_ctx, analyze_ok) = self.lower_and_check_impl()
self.ctx = analyzed_ctx
...
if not analyze_ok:
    log_error("phase 3 FAILED")
    if (rt_env_get("SIMPLE_BOOTSTRAP_DEBUG") ?? "") == "1":
        val phase3_error_count = self.ctx.errors.len()
        eprint("[bootstrap-phase3-errors] count={phase3_error_count}")
        var phase3_error_index = 0
        while phase3_error_index < phase3_error_count and phase3_error_index < 20:
            val phase3_error = self.ctx.errors[phase3_error_index]
            eprint("[bootstrap-phase3-error] index={phase3_error_index} len={phase3_error.len()} text={phase3_error}")
            phase3_error_index = phase3_error_index + 1
```

Measured behavior in a Stage-2-compiled binary running Stage 3 self-host
(pinned near `origin/main` `2d68e12a6a9` / `67055c4d3f1`):

- `[bootstrap-phase3-errors] count=572` **prints correctly** — `.len()` on the
  array works.
- **Zero** `[bootstrap-phase3-error]` lines ever print, despite
  `phase3_error_index < phase3_error_count` (`0 < 572`) being trivially true on
  the first iteration. No crash, no error, no exit-code change — the loop body
  (or the interpolated `eprint` inside it) simply produces no observable output
  and the program continues past the loop normally.

This is **not** a print-buffering artifact: a structurally identical
hand-added diagnostic (own instrumentation, later reverted) reproduced the
exact same symptom independently — `errors.len()` printed a real, correct,
non-zero count, but neither a `while`-loop body indexing `errors[i]` nor a
`val diag_errs: [text] = self.ctx.errors; diag_errs[0]` direct access ever
printed. A `file_write()` call placed in the same reachable position also
silently did not produce a file on disk (checked via `find`), even though the
unconditional `eprint` immediately after the `file_write()` call *did* print —
ruling out "the whole block after the count line never runs."

**Contrast:** the *sibling* per-module diagnostic loop in
`driver_hir_pipeline_lowering.spl` (added in commit `6834081f503`, "trace
per-module HIR diagnostics") — which calls `lowering.lowering_error_message_at(idx, name)`
(a **method call**, not a direct array-literal index) — printed correctly,
with real, non-empty error text, once per module, across dozens of modules in
the same run. The failure is specific to **directly indexing an array that is
a field of a struct local that was just reassigned from a function's return
value** (`self.ctx = analyzed_ctx` two lines above), not to array indexing or
string interpolation in general.

## Why this matters

This exact code shape — `self.ctx = <fn>()` followed later by reading
`self.ctx.<array-field>[i]` — is common in this driver (the whole `compile()`
function is a sequence of `self.ctx = self.<phase>_impl()` reassignments). If
the defect generalizes beyond this one call site, it would mean **any**
downstream code that reassigns `self.ctx` and then indexes into one of its
array fields is at risk of silently reading nothing / doing nothing, with no
error surfaced. This is squarely in the same family as the `AggregateCopy`
tag-mask bug fixed today (`1f81b2b4f0b`) and the "preserve HIR diagnostic
owners" fix (`2d68e12a6a9`) — aggregate/struct-copy-adjacent codegen defects
around freshly-returned struct values — but has **not** been confirmed to be
the *same* bug as either. Not investigated further here due to time budget;
flagging for a dedicated pass.

## What was and was not done

- **Done:** reproduced independently (own instrumentation, not copied from
  another session), confirmed `.len()` works but indexing/iteration silently
  no-ops, confirmed the contrast with the working method-call-based sibling
  loop, confirmed a `file_write()` call in the same position also silently
  fails to produce output while adjacent unconditional prints do work.
- **Not done:** did not get an LLVM IR/MIR dump correlated to this exact site;
  did not determine whether this is the same root cause as the `AggregateCopy`
  tag-mask bug or a new instance; did not check whether the defect is
  MIR-lowering-level (wrong vreg selected for `self.ctx` after reassignment)
  or codegen-level (correct MIR, wrong native lowering of the indexed load).
  did not check whether `bin/simple` (deployed, unrelated binary) reproduces
  this outside the bootstrap self-host context.

## Suggested next step

Get IR/MIR for `driver_orchestration.spl::compile`'s phase-3-failure branch,
correlate the indexing/eprint sequence, and compare against a MIR dump of the
same code pattern with the `self.ctx = ...` reassignment removed (e.g. reading
from a freshly-`val`-bound local instead of `self.ctx`) to isolate whether the
struct reassignment is the trigger.
