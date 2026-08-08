# MIR `self.error()` fail-open class — migration plan (scope only, do NOT execute)

**Date:** 2026-07-28
**Status:** PLAN ONLY. No migration started. Task #145 follow-up.
**Measured tree:** `origin/main` @ `e94139c3251`, re-verified byte-identical for
every cited file at `ac36d249d3b` (only unrelated `bootstrap_globals.spl`
path-handling lines differ between the two tips).
**Measured with:** static read of the pure-Simple compiler sources plus a
mechanical allowlist evaluation. The deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, 2026-07-28 05:45) is the **Rust
seed** — it contains zero occurrences of the marker strings
`unresolved method call` / `[mir-lower] WARNING`, and self-warns on startup. It
is therefore a *different codebase* from the one analysed here and cannot be
used to A/B this defect.

---

## 1. The corrected class size

`self.error(` under `src/compiler/**`:

| Count | Meaning |
|-------|---------|
| 128 | naive `grep -c` — **wrong**, includes 4 comment-only mentions |
| 248 | `glob('**', recursive=True)` — **wrong**, `src/compiler` has 17 symlinked dirs (`mir`, `hir`, `driver`, …) that double-count every file |
| **124** | **real, physical, non-comment call sites** — use this number |

The 4 comment-only mentions: `20.hir/hir_lowering/expressions.spl:1107`,
`50.mir/_MirLoweringExpr/method_calls_literals.spl:2204`,
`80.driver/driver_pipeline.spl:74` and `:112`.

Of the 124, **61** are in `50.mir` (not 62 — the `me error(...)` definition line
at `_MirLowering/asm_and_targets.spl:264` does not itself contain `self.error(`).

## 2. Classification

| Class | Count | Meaning |
|-------|-------|---------|
| **A — fatal by control flow** | 99 | error is followed by `return`/abort, or its message hits the fatal allowlist so the driver aborts before codegen. Already effectively fail-closed. |
| **B — FAIL-OPEN PLACEHOLDER** | **17** | execution continues and a bogus value is emitted into MIR that reaches codegen. **This is the real number.** |
| **C — recoverable diagnostic** | 7 | genuinely advisory; no bogus operand produced. |
| **D — unclear** | 1 | `asm_and_targets.spl:232` — a static `asm assert failed` demoted to a warning, so the assert effectively passes. Fail-open in spirit, but emits no bogus operand. |

Full per-site data: the classification TSV produced during this analysis
(file, line, class, reason, placeholder kind). All 17 B sites are in `50.mir`;
`10.frontend` (26), `20.hir` (22), `30.types` (3) and `70.backend` (12) are
uniformly fail-closed.

### The 17 fail-open sites

```
src/compiler/50.mir/mir_lowering_stmts.spl:793            dropped store (stale passthrough)
src/compiler/50.mir/mir_lowering_stmts.spl:825            dropped store
src/compiler/50.mir/mir_lowering_stmts.spl:852            dropped store
src/compiler/50.mir/mir_lowering_stmts.spl:1079           dropped store
src/compiler/50.mir/mir_lowering_ml.spl:102               fresh undefined temp
src/compiler/50.mir/_MirLowering/asm_and_targets.spl:163  nil asm body (block omitted)
src/compiler/50.mir/_MirLowering/asm_and_targets.spl:186  nil asm body
src/compiler/50.mir/_MirLowering/asm_and_targets.spl:193  nil asm body
src/compiler/50.mir/_MirLowering/asm_and_targets.spl:200  nil asm body
src/compiler/50.mir/_MirLowering/function_lowering.spl:483  default MirType.I64
src/compiler/50.mir/_MirLowering/function_lowering.spl:573  default MirType.I64
src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1058          const_int 0
src/compiler/50.mir/_MirLoweringExpr/literals.spl:52                 Const Int(0)
src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:457   const_int 0   <-- see 3.1
src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:978   const_int 3 (bogus tagged handle)
src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:174  sentinel -1 as enum id
src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1942 dropped spread (uninit fields)
```

## 3. Root mechanism — it is a *message-text* bug, not a control-flow bug

`self.error()` (`_MirLowering/asm_and_targets.spl:264`) is a bare
`self.errors = self.errors.push(...)`. It collects; it never raises. Whether a
collected error becomes fatal is decided **entirely by a string-prefix
allowlist**, `_mir_error_is_fatal` (`80.driver/driver_pipeline.spl:122`), via
`_driver_collect_mir_errors`:

* message matches a prefix → `ctx.add_error` → `lower_to_mir()` returns false →
  abort before codegen (fail closed).
* message does not match → `ctx.add_warning` → **the placeholder ships**.

So a site's safety depends on whether someone remembered to add its message
prefix to a list in a different layer. That coupling is the class defect.

### 3.1 Concrete live instance: `.unwrap_err()` (priority 1)

`method_calls_literals.spl:457` builds the message as:

```
val operation = if unwrap_err: "unwrap_err" else: "unwrap"
self.error("unsupported Result {operation} payload type", Some(receiver.span))
... val bad = b_bad.emit_const_int(0)
return bad
```

The allowlist entry is the literal `"unsupported Result unwrap payload type"`.

* `unwrap`     → `"unsupported Result unwrap payload type"`     → prefix matches → fatal.
* `unwrap_err` → `"unsupported Result unwrap_err payload type"` → **does not match** (`_err` breaks `starts_with`) → warning → const-0 returned in value position.

Verified empirically by running the real predicate on the real strings:
`"…unwrap_err payload type".starts_with("…unwrap payload type")` → `false`.

Supported `unwrap`/`unwrap_err` payload types are only `i64`, `f64`, `Str`, and
a `Named` struct with no default expression. Everything else (`bool`, `i32`,
arrays, tuples, non-struct `Named`) takes the fail-open branch. A
`Result<i64, bool>` + `.unwrap_err()` therefore lowers the error payload to
constant `0` (= `false`) while the interpreter oracle yields `true`.

**This one is fail-open in the DEFAULT `native-build` lane**, not only in the
bootstrap lane — it needs no special environment.

### 3.2 The second, independent drop: the bootstrap lane never consults the list at all

`driver.spl:1170` routes on the environment:

```
if SIMPLE_BOOTSTRAP == "1" and SIMPLE_BOOTSTRAP_STAGE4 != "1":
    (next_ctx, ok) = bootstrap_lower_to_mir_context(self.ctx)   # bootstrap lane
else:
    mir_ok = self.lower_to_mir()                                # default lane
```

* Default lane (`driver_pipeline.lower_to_mir`) calls
  `_driver_collect_mir_errors(self.ctx, bootstrap_lowering.errors)` — lowering
  errors are copied into `ctx` and filtered by the allowlist.
* Bootstrap lane (`driver_bootstrap.bootstrap_lower_to_mir_context`) returns
  `(next_ctx, next_ctx.errors.len() == 0)` and **never copies
  `MirLowering.errors` into `next_ctx`**. Its `ok` flag is structurally
  incapable of reporting any body-lowering error.

Underneath it, `bootstrap_lower_flat_hir_module_to_mir`
(`_MirLowering/bootstrap_globals.spl:313`) loops `lowering.lower_function(hir_fn)`
and then discards the `lowering` object, keeping only `.builder.module`. The two
existing `lw.errors.len() > 0` checks in that file (lines 512, 619) sit in
**type-registration** helpers that run *before* any function body is lowered, so
they can never observe a body-lowering error.

Net: in the bootstrap lane **all 61 `50.mir` sites are fail-open**, including
the 99-strong class A, because class A's fatality mostly derives from the
allowlist that this lane never consults.

## 3.3 Reproduction status — what is PROVED and what is not

**PROVED at the MIR-lowering layer** by a synthetic-HIR probe driven under
`bin/simple run` (no build step; ~60 s per iteration because the seed re-parses
the compiler each run). The probe builds a `MirLowering`, calls
`lower_method_call(IntLit(7), "frobnicate_zzz", [], MethodResolution.Unresolved)`
and **consumes** the returned `LocalId` via `emit_copy` — true value position,
since in statement position the temp is discarded and the bug hides.

Baseline (`pristine`, = `origin/main`):

```
%0 = CONST Int(7)
%1 = CONST Int(0)          <-- placeholder defining the returned local
%2 = COPY %1               <-- downstream consumes it as a real value
lowering.errors.len() = 1  -> "unresolved method call: frobnicate_zzz"
saw_rt_panic = false
```

Lowering **returned normally** with a fully usable operand; the diagnostic sat
inertly in `errors`. That is the fail-open shape exactly.

Patched (this change):

```
%2 = CONST Str("unresolved method call: frobnicate_zzz")
(void) = CALL const Str("rt_panic") (copy %2)
%1 = CONST Int(0)
saw_rt_panic = true, rt_panic_before_const0 = true
```

**NOT PROVED: an executed binary that exits 0 and prints a wrong value.** The
probe proves the placeholder is emitted and survives lowering; it does not run
generated code. Getting an executable end-to-end requires a pure-Simple compiler
binary, and redeploy is currently blocked (bootstrap peaks ~65 GB against a
64 GB monitor cap). A `native-build` run against the source tree is possible but
takes far longer than the seed-interpreted probe. Treat the executable
"exit 0 + wrong value" claim as **INFERRED from the emitted MIR plus the lane
analysis in 3.2**, not demonstrated.

## 4. Migration plan — phased, do NOT start yet

**Phase 0 — land the two contained fixes first (Phase 0a is already done).**
  * 0a. Make the unresolved-method site emit `rt_panic` before its const-0
    placeholder, matching the two siblings that already fail closed
    (`mir_lowering_stmts.spl:~1908` for-in-over-non-array, and
    `expr_dispatch.spl:~2905` match guards). **Landed with this plan.**
  * 0b. Fix the `unwrap_err` prefix mismatch (3.1). Deliberately *not* bundled
    here: it converts currently-"passing" builds into hard failures, so it needs
    its own native-smoke-matrix run. Track separately.

**Phase 1 — close the lane gap (highest leverage, smallest diff).**
Make `bootstrap_lower_to_mir_context` funnel lowering errors through
`_driver_collect_mir_errors` exactly as the default lane does. This single
change subordinates the bootstrap lane to the same allowlist and removes the
"class A is only fatal in one lane" asymmetry. Must be measured against the
bootstrap suite, since it will surface errors that lane has been silently
swallowing — expect fallout and triage it rather than re-widening the hole.

**Phase 2 — invert the allowlist into a denylist.**
Replace `_mir_error_is_fatal`'s opt-in prefix list with "fatal unless explicitly
marked advisory". Mechanically: add a severity field to `MirError` and set it at
the ~7 class-C call sites plus the `note:`-prefixed asm advisories, then have
`_driver_collect_mir_errors` branch on the field instead of on message text.
This kills the whole bug family — a new `self.error()` site is then safe by
default. It is also the change most likely to surface a long tail of
currently-swallowed errors, so it must follow Phase 1, not precede it.

**Phase 3 — belt-and-braces `rt_panic` at the remaining class-B sites.**
For the 17 B sites, emit `rt_panic` alongside the placeholder wherever the
placeholder is a *value* (13 of 17). The 4 `asm_and_targets.spl` sites are
different in kind — they omit an asm body rather than produce a bogus operand —
and two of them (163, 193) currently demote a **user-written `compile_error(...)`**
to a warning, which should simply be restored to fatal.

**Phase 4 — regression tests.** One spec per fixed site asserting the build
fails (or the binary panics) rather than producing a value. Invoke specs one per
process: a whole-directory spec run trips a 60 s CPU guard.

### Sequencing constraint
Phases 1 and 2 each convert silent warnings into build failures across the whole
compiler. Do them one at a time, each with a full native-smoke-matrix run, and
trust nothing measured on the Rust seed — a pure-Simple binary built from the
tree under test is required.

## 5. Explicitly out of scope
Making `self.error()` itself raise. With 124 call sites and a collect-then-batch
reporting contract (the driver reports *all* MIR errors, not just the first),
converting it to a raise would truncate diagnostics and rewrite control flow at
every site. Phases 1–3 achieve fail-closed behaviour without that.

---

## 6. EXECUTION STATUS — 2026-07-28 (landed)

**Landed:** commit `4b22f7e2121` on `main`.

### What was done
The message-text mechanism was **replaced**, not patched around:

* `MirError` gained an explicit `fatal: bool` field
  (`50.mir/mir_lowering_types.spl`).
* New `MirLowering.error_fatal(message, span)` sets it
  (`50.mir/_MirLowering/asm_and_targets.spl`). `error()` keeps the old
  non-fatal behaviour. `MirError` has exactly one construction site, so the
  migration surface was a single push expression.
* `_driver_collect_mir_errors` now aborts on `err.fatal or
  _mir_error_is_fatal(err.message)`. The allowlist is retained as a
  **deprecated fallback** and annotated to route new fatal sites to
  `error_fatal`, so the 99 already-fatal sites behave bit-identically.
* **All 17 class-B fail-open sites converted** to `error_fatal` — this
  subsumes plan Phase 1 and Phase 3's "restore to fatal" half.

Collection semantics are unchanged: `error_fatal` still only pushes onto
`self.errors`, so batch diagnostics survive and lowering keeps going.

### Corrected finding: the allowlist matched *none* of the 17

Section 3.1 called out `.unwrap_err()` as "the" live instance. Mechanically
evaluating the real predicate against all 17 real message strings gives
**17 of 17 downgraded** — the allowlist matched **zero** class-B sites. Two are
near-miss wording drifts where an entry was clearly *intended* to cover them:

| site message | allowlist entry | why it missed |
|---|---|---|
| `unsupported Result {operation} payload type` | `unsupported Result unwrap payload type` | `unwrap_err` breaks `starts_with` |
| `enum construction: missing runtime identity for '…'` | `enum construction: unregistered enum` | diverges after `enum construction: ` |
| `unsupported MIR assignment target: …` | `unsupported MIR expression:` | different noun |

And two sites (`asm_and_targets.spl` 163, 193) pass `arm.error_message` —
**user-authored `compile_error("…")` text**, which no allowlist in the driver
layer can ever enumerate. That is the structural argument for the replacement,
independent of any individual wording bug.

Contrapositive now expressible: the adjacent asm `"note: target backend differs
from recommended version"` diagnostics stay on `error()` and remain non-fatal,
sitting directly beside fatal siblings — a distinction prefix matching could not
draw.

### Phase 4 (regression specs) — NOT done
Still open, and now blocked by the gate below.

### BLOCKER: the native smoke matrix currently proves nothing

`scripts/check/native-smoke-matrix.shs` defaults to `SIMPLE_BINARY=bin/simple`,
which is the **Rust seed** (0 occurrences of `unresolved method call` or
`for-in over non-array iterables`); it cannot execute 50.mir/80.driver at all.
Pointed at the only pure-Simple binary on the box
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`, 2026-07-27) the
matrix is **24/24 FAIL**, every case with the identical
hyphen/underscore module-name collision — no case reaches lowering. Filed as
`doc/08_tracking/bug/native_build_blocked_by_hyphen_underscore_module_collisions_2026-07-28.md`.

Therefore **"what turns red" is not yet measurable**. It needs, in order:
1. the module-collision bug fixed, then
2. a redeploy of a pure-Simple binary built from a tree containing
   `4b22f7e2121` (blocked today: bootstrap peaks ~65 GB against a 64 GB cap),
3. then a matrix run, whose new failures must be triaged one by one as real
   defects the placeholder was hiding versus over-broad fatality.

Nothing was disabled, allowlisted, or weakened to reach a green result; the
matrix is simply not currently a functioning gate.

### Left deliberately unchanged
The single **class-D** site, `asm_and_targets.spl` "asm assert failed" (a static
assert demoted to a warning, so the assert effectively passes). It is fail-open
in spirit but emits no bogus operand, is outside the stated 17, and making an
assert fatal deserves its own change with its own evidence. Note the
near-identical `cannot evaluate asm target backend version` line lives in this
same assert path and was likewise left alone — only the arm-matching copy
(`Some(arm.span)`) was converted.
