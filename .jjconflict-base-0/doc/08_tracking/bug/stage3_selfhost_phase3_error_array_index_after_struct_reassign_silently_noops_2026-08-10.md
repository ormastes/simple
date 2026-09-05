# Stage-3 self-host — indexing `self.ctx.errors` right after `self.ctx = <returned struct>` silently produces no output

- **ID:** stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10
- **Status:** ROOT-CAUSED (narrowly), NOT FIXED — **still OPEN after a 2026-08-17
  re-probe; see the note directly below before spending time on it.**

### 2026-08-17 re-probe: the reassign-then-index SHAPE does not reproduce on either seed engine

A probe replicating the exact shape — `struct Ctx: errors: [text]`, a `me` method
returning `(Ctx, bool)`, `self.ctx = analyzed_ctx`, then `self.ctx.errors.len()`
followed by a `while` loop indexing `self.ctx.errors[idx]` — prints all five
elements correctly under **both** `SIMPLE_EXECUTION_MODE=jit` and
`=interpreter`.

Binary that produced this, stated because it is **not** current source:
`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, 59536728 bytes,
mtime 2026-08-16 22:59:37 — the stale Rust seed.

**This is NOT evidence that the row is fixed, and the row is deliberately left
OPEN.** The reported defect is in the *pure-Simple native codegen* as executed by
a Stage-2-compiled binary. Neither the seed's Cranelift JIT nor its tree-walk
interpreter is that code path, so a green from either is a negative control on
the wrong engine, not a retirement. Verifying it needs a Stage-2-built binary,
which this shared checkout (~15 concurrent lanes) must not produce.

**One confound was found and must be excluded before re-investigating.** Under
the JIT — and, per `core_codegen.spl:1603`, under the LLVM backend in current
source — `eprint` lowers to the **no-newline** `@rt_eprint`, so a diagnostic loop
of exactly this row's shape emits one unbroken line and reads as "the loop body
never ran". Filed separately as
`doc/08_tracking/bug/eprint_loses_newline_on_jit_and_llvm_backend_2026-08-17.md`.
It is **not sufficient** to explain this row (this row also reports a
`file_write()` in the same position producing no file, which no newline defect
can cause), but any future instrumentation of this row must not use `eprint` line
counts on a native binary as its signal.

Original filing follows. Found as a side effect of chasing
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

## UPDATE 2026-08-10 (part 2) — corrected, much narrower isolation: this is a
## `text` **parameter** defect, not an array/reassignment defect

Continued instrumenting directly at `CompileContext.add_error(message: text)`
(`src/compiler/80.driver/driver_types.spl`) — the single choke point every
error-reporting path in the driver funnels through — across five rebuild
cycles, each changing exactly one variable:

1. `eprint("[add-error-{count}] {message}")` guarded by
   `(rt_env_get("SIMPLE_BOOTSTRAP_DEBUG") ?? "") == "1" and count < 40` →
   **zero lines printed**, despite the guard string being present in the
   built binary (`strings` confirmed it) and `self.errors.len()` reporting
   572 afterward.
2. Same guard, `eprint("[add-error-unconditional]\n")` (**no reference to
   `message` at all**) → **572 lines printed**, exactly matching the error
   count. This rules out the guard condition, the method-call context, and
   the earlier "struct reassignment" hypothesis above — the eprint call site
   itself works fine unconditionally.
3. `eprint("[add-error-msg]{message}\n")` — reintroducing ONLY the
   `{message}` interpolation, guard removed entirely (fully unconditional) →
   **zero lines printed** again.
4. `eprint("[add-error-msg]" + message + "\n")` — swapping `{}`
   interpolation for `+` concatenation, same fully-unconditional form →
   **zero lines printed** again.

**Corrected, much narrower finding:** the defect is not about array indexing,
not about struct reassignment, not about the boolean guard, and not specific
to `{}`-style interpolation vs. `+` concatenation. It is specifically:
**an `eprint()` call inside `me add_error(message: text)` that references its
own `message: text` parameter (by any means: interpolation or concatenation)
silently produces no output, while the identical call site with only a
literal string (no parameter reference) prints correctly every time.** The
parameter itself is genuinely valid data — `self.errors.push(message)` on the
very next line always succeeds, and reading it back later via `.len()` /
`.push()` behavior is consistent with 572 real pushes.

This reproduced identically on 12 separate from-scratch Stage-2 rebuild
cycles (each a genuine `--fresh-cache` two-and-a-half-to-three-minute
recompile against a clean pinned checkout, not a cached/stale artifact), so
it is not a caching or provenance artifact.

**Not done:** did not test whether this is `eprint`-specific or affects
`print`/`file_write` equally when they reference a `text` parameter directly
(earlier, unrelated instrumentation in `driver_orchestration.spl` did also
see a `file_write` silently not persist a similarly-parameter-derived string,
which may be the same defect family, but that was not isolated with the same
rigor as this five-cycle test and should be re-verified narrowly). Did not
get IR/MIR correlated to this exact narrowed repro. Did not check whether a
plain top-level `fn` (not a `me` method) with a `text` parameter reproduces
the same symptom, which would rule `me`/`self` context in or out definitively.

**Suggested minimal repro for a follow-up session:** a single `.spl` file with
`fn f(x: text): eprint("{x}")` called from `main()`, native-built and run
standalone (no bootstrap self-host involved), to determine if this is
bootstrap-context-specific or a general native-codegen defect.

---

## RE-VERIFICATION 2026-08-17 (c_splmisc lane) — CONTROL LANE IS CLEAN; NATIVE LANE NOT REACHED

Classified by CONTENT, not by SHA. No source change made.

### The doc's own "suggested minimal repro" was built and run

Fixture (`r4.spl`) exercises the exact narrowed shape this row describes —
assign a returned struct into `self.ctx`, then immediately index/length the
array field on it:

```
struct Ctx:
    errors: [text]

class Drv:
    ctx: Ctx

impl Drv:
    me phase(c: Ctx) -> Ctx:
        Ctx(errors: c.errors.push("boom"))

    me drive():
        self.ctx = self.phase(self.ctx)
        eprint("count=")
        eprint(self.ctx.errors.len())
        if self.ctx.errors.len() > 0:
            eprint(self.ctx.errors[0])
```

**Interpreter / JIT control — CORRECT, no silent no-op:**

```
$ nice -n 19 bin/simple run .../r4.spl --timeout 300
rc=0
count=1boom
```

(`rc` assigned on the line *after* the command, never through a pipe.)
Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
59536728 B, mtime 2026-08-16 22:59 — the **Rust seed**. Both the `.len()` and
the `[0]` read see the reassigned struct. So the defect is **not** in the
seed's interpreter/JIT lane, consistent with the doc filing it as native-only.

Incidental finding while writing the fixture, worth a line: `go` is a reserved
word. `me go():` fails with `Unexpected token: expected identifier, found Go`,
diagnosed at parse time — loud, not silent, so not this defect class.

### COULD NOT PROVE — native lane

`bin/simple native-build r4.spl -o r4.bin` was started (nice -n 19, 600s cap)
and had not produced a binary when this lane stopped; it was still emitting
frontend warnings. A sibling lane independently recorded, on this same worktree
today, that the native lane is broken here in three different ways
(`bootstrap/stage3/simple native-build` SIGSEGVs even on `fn main(): print("hi")`;
seed `native-build` fails at LINK with `ld.lld: error: cannot ope[n]`) — see the
2026-08-17 section of
`doc/08_tracking/bug/stage4_aot_native_build_struct_field_access_sigill_2026-07-24.md`.
So **no native evidence was obtained in either direction**, and a link-time
failure could not have exposed a lowering defect anyway.

### Probable collapse — flagged, deliberately not duplicated

This row's shape — *a struct returned BY VALUE has its fields misread* — is very
likely the same root cause as the known `hir/lower/expr/access.rs:288`
`.unwrap_or(0)` defect, where a missing field index is guessed as `0` so every
field of a by-value returned struct reads as field 0. That would explain the
"silently no-ops" symptom exactly: `errors` resolves to field 0 of a struct
whose field 0 is not `errors`. `access.rs` is another lane's exclusive path in
this session and was **not** edited or measured here. Whoever fixes that row
should re-run the fixture above natively before filing separate work for this
one.

Still not done (unchanged from the doc's own list): no IR/MIR correlated to the
repro; not determined whether a plain top-level `fn` (rather than a `me` method)
reproduces it, which would rule `me`/`self` context in or out.

---

## 2026-08-17 (W2 driver lane) — FAMILY COLLAPSED, DRIVER-SIDE MITIGATION LANDED; CODEGEN ROOT STILL OPEN

**Not reproduced on any engine reachable from this checkout.** The exact shape
(`h.ctx = <returned struct>` then `h.ctx.errors.len()` / `h.ctx.errors[i]` /
typed-alias index) was probed three ways with the Rust seed at
`bin/release/x86_64-unknown-linux-gnu/simple`:

| engine | invocation | result |
|---|---|---|
| tree-walk interpreter | `SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe.spl` | `count=3` + all 3 items + `direct0=alpha` — correct |
| Cranelift JIT | `SIMPLE_EXECUTION_MODE=jit bin/simple run probe.spl` | identical, correct |
| Cranelift AOT native | `bin/simple compile probe.spl -o probe.bin --native` then run the ELF | identical, correct |

So the defect is specific to the **pure-Simple compiler's own native codegen**
(the Stage-2-compiled binary running Stage 3), which is not buildable within a
normal session. **The row stays OPEN** on the codegen axis, and the responsible
file could not be named — hence no cross-owner block was filed against a guess.

**Family found (the point fix in the original writeup would have missed it).** A
census of `ctx.errors[` across `src/compiler/80.driver/` found **six** sites of
the same reassign-then-index shape, and only ONE of them was the debug-gated
trace loop this doc was written about. Two are on the **non-debug production
path**, where the loss is not a missing trace line but a *silently blank
diagnostic*:

- `driver_orchestration.spl:158` — debug trace loop (the documented site)
- `driver_orchestration.spl:164` — first-error extraction, production path
- `driver_orchestration.spl:236,251` — `Method resolution` classification and the
  MIR-lowering failure message, both after `self.ctx = analyzed_ctx`
- `driver_pipeline_execution.spl:16`, `driver_aot_pipeline.spl:84` — MIR-lowering
  failure message, same shape

All six now go through a new method-shaped accessor
`CompilerContext.error_message_at(index)` in
`src/compiler/80.driver/driver_types.spl` (bounds-guarded, returns `""` out of
range). A method call on the owner is the only shape this doc measured to work in
the failing binary — the sibling `lowering_error_message_at()` loop in
`driver_hir_pipeline_lowering.spl` printed correctly in the same run. This does
not fix the codegen defect; it removes the driver's exposure to it.

`driver_hir_pipeline_passes.spl:112` (`ictx.errors[e_idx]`) was left alone: its
`ictx` is constructed by `HmInferContext.with_builtins()` and mutated in place,
never reassigned from a returned struct, so it is a different shape — and
`HmInferContext` is outside this lane's ownership.

### Specs
- `test/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.spl`
  (reproducer shape, pins count-vs-index agreement, typed alias, accessor):
  `Results: 3 total, 3 passed, 0 failed`.
- `test/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.spl`
  (similar-problem detection — fails when ANY driver phase file reintroduces the
  direct-index shape, which the reproducer cannot see):
  `Results: 3 total, 3 passed, 0 failed`.

**Ablation.** Reverting a single site (`self.ctx.error_message_at(0)` back to
`self.ctx.errors[0]`) drove the detection spec to
`Results: 3 total, 1 passed, 2 failed`; restoring it returned it to green. The
mitigation is therefore load-bearing for the guard.
