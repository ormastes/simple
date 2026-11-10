# `self.error(...)` used where `self.error_fatal(...)` was intended — family sweep

## Statement-binding invariant follow-up, 2026-11-10

The release/1.0.0 source at `6d496f82c5a` still records eight statement
invariant failures as nonfatal in `mir_lowering_stmts.spl`: three missing
let-symbol paths, two missing initializer-local paths, an empty expression
statement payload, a missing range-loop symbol, and a missing indexed-loop
symbol. Returning after a malformed, unused binding does not guarantee a
later `undefined variable` diagnostic. These messages are absent from the
legacy fatal-message allowlist, so the driver can admit incomplete MIR.

This follow-up changes only those eight sites to `error_fatal`, preserving
diagnostic collection and lowering recovery. It leaves ordinary advisories
and the documented Option.None fallback unchanged.

`test/01_unit/compiler/mir/statement_binding_fatal_spec.spl` invokes the
production statement/range/indexed-array lowerers with unresolved symbols,
checks their source spans and actual driver fatal classification, and
includes resolved-binding and advisory controls. These tests isolate an
unused malformed binding rather than relying on a later variable use to
produce an unrelated fatal error. The additional initializer/payload guards
still require their producer-fault boundary evidence; no coverage claim is
made from the binding tests alone.

Status: source repair and executable regression authored; verification
pending. No admitted self-hosted full CLI/test runner was available during
authoring. The shared `bin/simple.exe` was independently identified as the
Rust seed and was not substituted for product verification. Required runtime
checks, original-boundary evidence, branch coverage, and generated SPipe
manual remain pending the campaign's runtime prerequisite. This subsection
does not close the full diagnostic family or reuse historical test passes.

Provider input/output/cache-read/cache-create token usage: unavailable.
Comparable cohort average and ratio: unavailable; no values were guessed.
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-08-08

## Background

`MirLowering.error(message, span)` (defined in
`src/compiler/50.mir/_MirLowering/asm_and_targets.spl:264`) records a
**non-fatal** diagnostic (`MirError.fatal = false`). Whether a non-fatal
`MirError` actually fails the build is decided downstream in
`src/compiler/80.driver/driver_pipeline_lowering.spl` by
`_driver_collect_mir_errors`, which promotes an error to fatal only if
`err.fatal` is `true` **or** `err.message` matches a deprecated
prefix-allowlist in `_mir_error_is_fatal` (line 119). Any `self.error(...)`
call site whose message is not covered by that allowlist is a **silent
warning**: the build can exit rc=0 (or produce a working-looking binary)
even though the call site fired for a condition the surrounding code and
comments clearly intend to be fatal.

`MirLowering.error_fatal(message, span)` (same file, line 275) is the
correct call for these sites: it sets `MirError.fatal = true`, which
`_driver_collect_mir_errors` always honors regardless of message wording.

This mechanism is **local to the 50.mir `MirLowering` class**
(`_MirLowering/*.spl`, `_MirLoweringExpr/*.spl`, `mir_lowering_*.spl`). The
other `self.error(...)` definitions in the compiler are separate classes with
different (already-fatal) semantics and are **out of scope** for this defect
class:
- `20.hir/hir_lowering/types.spl:360` (`HirLowering.error`) — pushed errors
  are unconditionally added to `ctx.errors`, gating `ctx.errors.len() == 0`
  in `driver_hir_pipeline_lowering.spl`. Always fatal.
- `70.backend/codegen.spl:663` (`Codegen.error`) — `codegen.errors.len() > 0`
  is checked at `codegen.spl:725-726` and returns `Err(...)`. Always fatal.
- `30.types/type_infer/context.spl:152` (`TypeInferContext.error`) and the
  `10.frontend/treesitter/outline*.spl` parser `self.error(...)` call sites —
  not part of the MirError/allowlist mechanism; not audited further here
  (different, older diagnostic plumbing — out of scope for this pass).

## Enumeration: 50.mir `self.error(...)` call sites

`/usr/bin/grep -rn 'self\.error(' src/compiler/50.mir --include=*.spl` — all
real (non-comment) call sites, cross-checked against the
`_mir_error_is_fatal` prefix allowlist
(`driver_pipeline_lowering.spl:119-131`: `undefined variable`,
`unresolved method call:`, `unsupported MIR expression:`, `match guards
(case x if cond:) are not supported`, `unsupported array/string slice
index`, `B5b`, `match default binding has no resolved symbol`, `enum
match:`, `enum construction: unregistered enum`, `unsupported struct field
initializer`, `unsupported Result unwrap payload type`, `for-in over
non-array iterables`).

Legend: **[FIXED]** = converted to `error_fatal` in this pass. **[HIGH]** =
clearly-should-be-fatal, not fixed this pass (future lane). **[COVERED]** =
message matches the allowlist, already effectively fatal today (no action).
**[WARN]** = clearly-intentional advisory. **[AMBIG]** = cannot tell from
context alone.

### switch_operators_calls.spl
| line | message (abridged) | class |
|---|---|---|
| 794, 915 | match default binding has no resolved symbol | COVERED (allowlist) |
| 1681,1692,1694,1736,1821,2006,2043,2045,2085 | `enum match: ...` | COVERED (allowlist prefix `enum match:`) |
| 2041 | enum variant lookup miss: bare pattern '{variant}' resolved to sole owner ... CONTESTED | **HIGH** — not covered (prefix is `enum variant lookup miss:`, not `enum match:`); a contested bare-enum lookup can dispatch to the wrong enum's variant silently |
| 2458 | `fmsg` (dynamic — Result unwrap-family message) | AMBIG — need to trace `fmsg` construction; likely already covered by `unsupported Result unwrap payload type` prefix in some but not all branches |
| 2657 | enum variant lookup miss: 'Option.None' resolved to discriminant -1 while lowering the '?' try-operator | **HIGH** — not covered; directly adjacent to the known "`?` early-return matches neither Ok nor Err" defect class (`reference_try_operator_early_return_matches_neither_ok_nor_err.md`) |
| 2850 | enum construction: unregistered enum '{enum_name}' | COVERED (allowlist) |
| 2863 | enum variant lookup miss: constructing '{enum_name}.{variant}' resolved to discriminant -1 | **HIGH** — not covered; silently constructs an enum value with the sentinel -1 discriminant |
| 2971 | enum variant lookup miss: constructing '{enum_name}.{variant}' (method-call form) resolved to discriminant -1 | **HIGH** — not covered, same class as 2863 |
| 3212 | unsupported struct field initializer | COVERED (allowlist) |

### expr_dispatch.spl
| line | message (abridged) | class |
|---|---|---|
| 200 | `message` (dynamic) | AMBIG |
| 1544 | unsupported array/string slice index | COVERED |
| 1912 | enum-to-integer cast could not read runtime discriminant | **HIGH** — not covered; a bad `as i64` enum cast silently produces a garbage integer |
| 1999 | MIR lowering produced no local for this expression | **[FIXED]** — single choke point every lowered expression passes through; substitutes a fabricated unit temp and continues on `nil` |
| 2455,2465,2495,2505 | undefined variable[: {name}] | COVERED |
| 2855 | unresolved method call: operator overload ... | COVERED |
| 3845 | unsupported MIR expression: {kind} | COVERED |
| 3847 | MIR lowering received a garbage expression handle (mis-extracted enum payload) | **[FIXED]** — default-arm fallback for a corrupt/garbage HIR expr handle; same choke-point family as 1999 |
| 3987 | `guard_unsupported_msg` (dynamic) | AMBIG — likely covered by `match guards ... are not supported` prefix, not independently verified |
| 4001-4129 (9 sites) | dynamic `B5b` Phase-2 int-match diagnostics | COVERED (allowlist prefix `B5b`) if truly B5b-prefixed at all 9 sites — not individually verified; flagged AMBIG for a future pass to confirm each site's actual string literally starts with `B5b` |

### method_calls_literals.spl
| line | message | class |
|---|---|---|
| 2876 | unresolved method call: {method} | COVERED |
| 3188 | unsupported array element (cannot lower to a value) | **[FIXED]** — exact duplicate-body twin of `literals.spl:52`'s `lower_array_lit`, which already uses `error_fatal` for the identical message. This is the "divergent duplicate methods" defect the background task cites: two `lower_array_lit` definitions (same class, same name, different files) differ by exactly this one line, and this file's copy was the one still silently downgrading to a warning. See Verification below — the specific fixture tried this pass did not conclusively exercise this exact branch. |

### asm_and_targets.spl
| line | message | class |
|---|---|---|
| 156 | asm match is non-exhaustive, missing: {missing_str} | **HIGH** — not covered; an asm block missing a target arm silently drops the arm instead of failing |
| 191, 234 | note: target backend differs from recommended version | WARN — "note:"-prefixed, explicitly advisory |
| 229 | cannot evaluate asm target backend version: {target_backend} version is unavailable | **HIGH** — not covered |
| 232 | asm assert failed: target {target_arch}-{target_os} does not match [{spec_str}] | **HIGH** — not covered; an asm target-compatibility assertion that doesn't abort defeats the point of the assertion |

### module_lowering.spl
| line | message | class |
|---|---|---|
| 321 | enum runtime ID collision: '{prior_name}' and '{runtime_name}' | **[FIXED]** — a hash-collision between two enums' runtime names; without this being fatal, the second enum's runtime id registration is silently skipped (early `return`), corrupting later runtime-id lookups for it |
| 376 | enum variant discriminant must be an integer constant | **[FIXED]** — part of `register_enum_variants`, the hot path for every enum declaration |
| 378 | enum variant discriminant must be a constant integer expression | **[FIXED]** — same function |
| 380 | enum variant discriminant {value} is outside portable runtime range 0..2147483647 | **[FIXED]** — same function; an out-of-range discriminant silently truncates/wraps at the runtime boundary |
| 388 | enum '{enum_def.name}' has duplicate discriminant {value} | **[FIXED]** — same function; two variants silently sharing one runtime discriminant corrupts every `match`/construction that dispatches on it. See Verification below — the specific fixture tried this pass did not conclusively exercise this branch. |

### mir_lowering_stmts.spl
| line | message | class |
|---|---|---|
| 599, 958, 982 | let binding has no resolved symbol | **HIGH**, lower urgency — the call site `return`s immediately after (no fabricated value pushed for codegen); the unbound symbol is likely to surface downstream as `undefined variable` (allowlisted). Not converted this pass. |
| 685, 1027 | let initializer produced no local | **HIGH**, same lower-urgency reasoning |
| 969 | empty HIR expression-statement payload | AMBIG |
| 2152 | for range loop variable has no resolved symbol | **HIGH**, same lower-urgency reasoning |
| 2319 | `iter_unsupported_msg` (dynamic) | AMBIG — likely `for-in over non-array iterables` (allowlisted), not independently verified for every call shape |
| 2477 | for loop variable has no resolved symbol | **HIGH**, same lower-urgency reasoning |

## Fixes landed this pass (5 locations, 8 call sites)

All changed `self.error(` → `self.error_fatal(`, no other logic change:

1. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3188` —
   `lower_array_lit`'s array-element-cannot-lower guard (the live twin of the
   already-fatal `literals.spl:52` duplicate).
2. `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1999` — the
   single "no local produced" choke point in `lower_expr`.
3. `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:3847` — the
   garbage-expression-handle default arm in `lower_expr_impl`.
4. `src/compiler/50.mir/_MirLowering/module_lowering.spl:321` — enum
   runtime-ID hash collision in `register_enum_runtime_name`.
5. `src/compiler/50.mir/_MirLowering/module_lowering.spl:376,378,380,388` —
   all four discriminant-validation diagnostics in `register_enum_variants`.

### Verification (honest results)

Oracle used: `env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple
native-build --source <dir> --entry-closure --entry <dir>/main.spl
--cache-dir <tmp>/c --output <tmp>/b`. `bin/simple` in this environment is
the Rust bootstrap seed (prints its own "bootstrap seed only" warning); the
host had multiple other unrelated multi-GB/multi-CPU-minute
native-build/self-host jobs already running throughout this session
(confirmed via `ps aux`), and every native-build invocation here reloads and
interprets the entire compiler + LLVM import graph before reaching codegen
(documented, expected behavior), so each run took several minutes.

Both fixes were already applied to source before these two repro builds ran
(no separate pre-fix baseline was captured for either — see below):

- **Repro 1** — array literal with `Lambda` elements:
  ```
  fn main():
      val arr = [\x: x + 1, \x: x * 2]
      print "built"
  ```
  Result: `native-build` exited **rc=1** with `error: MIR lowering error:
  unsupported MIR expression: HirExprKind::Lambda(...)`. This is a
  **different, pre-existing fatal path**: `expr_dispatch.spl`'s generic
  default-arm handler already classifies a bare `Lambda` expression as
  `unsupported MIR expression:`, which is in the `_mir_error_is_fatal`
  allowlist independent of this fix — `lower_expr` never reaches
  `lower_array_lit`'s `nil`-check for this fixture. **Inconclusive for the
  `method_calls_literals.spl:3188` fix specifically.** The conversion there
  is still correct-by-construction (mirrors the already-`error_fatal` twin
  at `literals.spl:52`) but is downgraded to evidence-based, not
  repro-confirmed; a future lane should find an input that reaches a `nil`
  from `lower_expr` without first tripping the generic `unsupported MIR
  expression:` catch-all.
- **Repro 2** — duplicate enum discriminant:
  ```
  enum Bad:
      A = 1
      B = 1

  fn main():
      val x = Bad.A
      match x:
          case Bad.A: print "A"
          case Bad.B: print "B"
  ```
  Result: `native-build` exited **rc=0**, binary ran and printed `A`
  (outwardly correct for `x = Bad.A`). The duplicate-discriminant branch in
  `register_enum_variants` was evidently **not entered** by this fixture (or
  had no observable effect on this trivial 2-variant program). **Inconclusive
  for the specific duplicate-discriminant branch**; the other three
  `module_lowering.spl` sites (:321, :376, :378) are untested by either
  repro. This run does double as an implicit regression signal for all four
  `module_lowering.spl` fixes together: `register_enum_variants` runs on
  every enum declaration, this program has one, and the build/run completed
  successfully with correct output — no evidence the fix broke anything.
- No clean/valid third-party program could be run through the oracle as an
  explicit, isolated regression control within this session's time budget,
  given the per-run cost described above.

### Assessment

Neither repro cleanly proves the exact silent-corruption mechanism each fix
targets — both landed anyway because (a) they are mechanically
correct-by-construction (identical call pattern to already-`error_fatal`
sibling call sites in the same class, so there is zero syntax/compile risk),
(b) each is backed by an explicit, specific code comment or allowlist-gap
analysis describing the exact silent-wrong-value mechanism it closes, and
(c) by construction a program that never enters these already-buggy branches
is unaffected — there is no plausible path by which this class of fix
regresses a **valid** program that doesn't already trip one of these
conditions. This should be treated as **evidence-based, not fully
build-proven** work; a follow-up lane with more build-time budget should
construct fixtures that definitively isolate each of the 5 fixed branches
(and the still-open HIGH-confidence sites below).

## Follow-up pass (2026-08-08, second lane)

Fixed 2 of the 4 highest-priority candidates from the original "Recommended
follow-up" list below. Both converted `self.error(` -> `self.error_fatal(`,
no other logic change:

1. `switch_operators_calls.spl:2863` (`lower_enum_lit`) — **[FIXED]**.
   Confirmed by reading: when `enum_variant_discriminant` returns -1 here,
   the `-1` value flows straight into `disc_local` and out to `rt_enum_new`
   with **no recovery path below** — this is the textbook silent-wrong-value
   shape, and it sits in the exact same function as the already-`error_fatal`
   "enum construction: unregistered enum" guard three lines above it (line
   2850/2854), i.e. this is that guard's obvious, previously-missed sibling.
2. `switch_operators_calls.spl:2971` (`lower_enum_construct_named`) —
   **[FIXED]**. Same shape as 2863 (method-call constructor form instead of
   the literal form); comment at the site already says "this had no guard at
   all" — no recovery path below, `-1` goes straight into `rt_enum_new`.

### Verification

Regression (clean program, no defect triggered): a 3-variant `enum Color`
exercised via literal construction (`Color.Red`), `match`, and an `if/elif`
constructor function, built and run through the oracle —
`native-build` exited **rc=0**, the binary ran and exited **rc=0**. (The
program's printed text was garbled — raw pointer values instead of "red" /
"green" / "blue" — but that is the pre-existing, unrelated
`reference_native_tuple_to_text_prints_raw_pointer` class of defect, not
something this change introduced; the signal that matters here is that build
and run both completed with no fatal MIR error, i.e. normal enum
construction never reaches the -1 branch this pass made fatal.)

No isolated positive repro (a program that actually drives `disc` to -1 at
either site) was built. Both sites require an already-broken *registration*
state (a bare-name-collision eviction, per `enum_variant_miss_detail`'s own
docstring) to produce -1 for an otherwise-valid variant reference — normal
user typos are caught earlier, at HIR/type-check. A concrete attempt to
manufacture the eviction (two modules each declaring `enum Status` with
disjoint variants, referenced together) did **not** reach MIR at all: HIR
lowering already raises its own unrelated, independently-fatal error first —
`enum payload dependency 'Status' conflicts: <mod_a>::Status::enum vs
<mod_b>::Status::enum` — before either MIR site's guard would ever run for
that particular construction. This mirrors the "Verification (honest
results)" section above for the first pass: both fixes are correct-by-
construction (identical call pattern to sibling `error_fatal` sites in the
same functions, zero syntax/compile risk, and by construction a program that
never drives `disc` negative is unaffected) but not repro-proven for the
specific -1 branch. Treat as evidence-based, matching the first pass's
standard.

### The `?`-operator connection did NOT hold — important correction

The original follow-up list (below) named line 2657 "directly adjacent to
the known `?`-operator Ok/Err defect" as the top candidate, hypothesizing it
might explain that bug's symptom. Reading
`try_operator_early_return_matches_neither_ok_nor_err_2026-08-07.md` in full
shows this connection does **not** hold, and that doc says so explicitly:
that bug's root cause was isolated entirely to the **Rust seed**'s
`lower_try` (`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2194`),
which emitted a bare `rt_enum_payload(inner)` with **no discriminant test and
no branch at all** — so `?` fell through unconditionally regardless of
Ok/Err, and was fixed at the seed source on 2026-08-07. That same doc
independently verifies (twice, in two different follow-up passes) that
**this file's** `lower_try_expr` (`switch_operators_calls.spl:2553`, which
contains line 2657) was **always correct**: it does emit the
discriminant-test + branch + `terminate_return` shape the seed was missing.
Line 2657 is therefore not a candidate explanation for that symptom — it is
a narrower, independent edge case (the pure-Simple lowering's `Option.None`
lookup losing to a bare-name collision) inside code whose overall control
flow was never in question. **Not fixed this pass**: unlike 2863/2971, line
2657 has an explicit, deliberate recovery path immediately below it
(`none_disc = 1`, "Restore the reserved Some=0/None=1 default so the
comparison stays meaningful, and say so loudly" — the code already chose
graceful degradation over aborting), so converting it to fatal would be a
behavior change beyond "make an already-silent corruption loud" and needs
its own review of whether that recovery default is actually always safe.

## Recommended follow-up (not fixed this pass)

Highest-confidence next candidates, in priority order:
1. ~~`switch_operators_calls.spl:2863,2971`~~ — **FIXED**, see "Follow-up
   pass (2026-08-08, second lane)" above.
1b. `switch_operators_calls.spl:2657` — still open; has a deliberate
   in-place recovery fallback (see correction above), so fixing it requires
   deciding whether that fallback is actually always safe, not just flipping
   `error` to `error_fatal`. **Not** the explanation for the `?`-operator
   Ok/Err bug (that was seed-only, already fixed — see correction above).
2. `switch_operators_calls.spl:2041` — contested bare-variant lookup in
   match arms (sibling of the already-`error_fatal` "enum match:" family,
   but this one's message prefix differs and slipped through).
3. `expr_dispatch.spl:1912` — enum-to-integer cast reading a bad runtime
   discriminant.
4. `asm_and_targets.spl:156,229,232` — asm non-exhaustive/version/assert
   sites (excluding the two `note:`-prefixed advisories at 191/234, which
   are intentional warnings and should stay non-fatal).
5. `mir_lowering_stmts.spl:599,685,958,982,1027,2152,2477` — the
   let/for-binding "no resolved symbol"/"no local" family. Lower urgency
   (see table) — worth confirming the "cascades into an already-fatal
   `undefined variable`" assumption actually always holds before converting;
   if it doesn't, these are open holes.
6. Find fixtures that actually isolate the 5 sites fixed this pass
   (see Verification above) — in particular an enum with an *explicit*
   discriminant collision that a native-build repro can drive through
   `register_enum_variants`'s duplicate-check branch, and an array-literal
   element expression that returns `nil` from `lower_expr` without first
   tripping the generic `unsupported MIR expression:` catch-all.

Do NOT convert the `B5b`-prefixed sites in `expr_dispatch.spl:4001-4129` or
the `enum match:`/`unsupported Result unwrap payload type` family without
first confirming each site's literal message text still matches its
allowlist prefix — a future rewording of any of these strings would silently
flip them back to non-fatal with no compiler error to catch it (this is
exactly the deprecated-allowlist failure mode the `error_fatal` mechanism
exists to replace).

## Follow-up pass (final 2 sites, 2026-08-08, third lane)

Resolved the last two open items from the "Recommended follow-up" list
(1b and 2 above): `switch_operators_calls.spl:2041` and `:2657`.

1. `switch_operators_calls.spl:2041` (in `lower_enum_match`) —
   **[FIXED]**, converted `self.error(` -> `self.error_fatal(`, no other
   logic change. This is the `owner_count == 1` arm of the same
   contested-bare-variant if/elif chain whose `owner_count > 1` sibling
   (line 2043, `enum match: bare variant ... is ambiguous`) and
   `owner_count == 0` sibling (line 2045, `enum match: unknown variant
   ...`) are both already effectively fatal via the `enum match:`
   allowlist prefix. Line 2041's message starts with `enum variant lookup
   miss:` instead, so it alone slipped through the allowlist despite
   reporting the same class of contested/unreliable resolution as its two
   already-fatal siblings — an oversight, not an intentional soft-fallback.
   Confirmed by reading: the diagnostic fires *after* `d` is already
   assigned (line 2026) and does not itself change `d` or take a recovery
   branch, so promoting it to fatal only makes a real ambiguity loud; it
   cannot change behavior on any input that doesn't hit this exact
   contested-bare-name-collision condition.
2. `switch_operators_calls.spl:2657` (in `lower_try_expr`) —
   **left non-fatal, on purpose**. Traced the surrounding code: when the
   bare name `"Option"` has been evicted by a name collision,
   `enum_variant_discriminant("Option", "None")` returns -1, but the very
   next line (`none_disc = 1`) unconditionally resets `none_disc` to the
   reserved `Some=0/None=1` layout *before* it is used to build
   `none_key`/`is_boxed_none` below — this is a real, already-safe
   in-place recovery, not a bug being masked. `?` on a boxed `Option` is a
   hot path (every `?`-desugared Option unwrap in ordinary user code), so
   making this fatal would hard-abort compilation on a rare, already-
   neutralized name-collision edge case instead of just warning about it.
   No `recovery`/`partial`/`lsp`/`best_effort` mode flag exists nearby or
   gates this branch — the softness here is inherent to the code's own
   fallback design, not an external error-recovery mode. Added a one-line
   (multi-line) comment directly above the call explaining why it is
   intentionally non-fatal, referencing this doc.

### Verification

Functional smoke test (native-build oracle, same style as prior passes):
a program with a 3-variant `enum Color` matched via `match c: case
Color.X: ...` (exercises `lower_enum_match`, the function containing the
:2041 fix) and a `Result`-returning function using `find_it(5)?` on an
`Option<i64>` (exercises `lower_try_expr`, the function containing the
:2657 non-fatal path) was built through `env -u SIMPLE_BOOTSTRAP
SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --entry-closure --entry
<dir>/main.spl ...`. Build exited successfully (binary produced) and the
binary ran to completion printing `green` then `done` (rc=0) — both
functions were reached and produced correct output on a clean, non-
contested input, so the :2041 fix does not regress ordinary enum-match
compilation and the :2657 fallback continues to behave as before (no
behavior change was made there).

A first attempt at this verification added `eprint("MARKER-...")` as the
first statement of both `lower_enum_match` and `lower_try_expr` to prove
direct liveness; the markers did not surface in native-build's captured
stderr (its wrapper appears to filter/buffer interpreter-level debug
prints even on a successful run), so liveness was instead confirmed via
the stronger functional signal above (correct compiled+run output, which
has no other code path than these two functions for a `match` on an enum
and a `?` on an `Option`). Markers were added, found inconclusive for this
harness, and removed — not left in source.

As with the second-lane pass above, no isolated positive repro that
actually drives the :2041 or :2657 branches to their miss-condition (a
genuine bare-name eviction) was attempted in this pass, for the same
reason recorded there: manufacturing that eviction previously surfaced an
unrelated, independently-fatal HIR-level error first. Treat both as
evidence-based (correct-by-construction reasoning documented per-site
above), consistent with the standard set by the earlier passes in this
doc.

### Shared-workspace note

Mid-pass, an uncommitted edit to this file (the :2041/:2657 changes plus
temporary eprint markers) was silently reverted by a concurrent session's
working-copy reconcile before it could be committed (confirmed via `git
status`/`git diff` showing no pending changes against HEAD immediately
after the edit tool reported success). The edits were redone and committed
immediately afterward with no further gap between edit and commit, per the
standing shared-WC guidance in `.claude/rules/vcs.md` and this repo's
memory notes on write-tool/edit clobbering.

## Unknown statement follow-up, 2026-11-06

The `E-MIR-STMT-Unknown` fallback in `mir_lowering_stmts.spl` still used
`self.error`, despite documenting that the statement is dropped. Its message
does not match any prefix in the current shared driver classifier,
`driver_mir_legacy_message_is_fatal_v1`. Therefore the fallback recorded only
an advisory and could allow publication of incomplete MIR. This is a distinct
remaining instance of this diagnostic-severity family, discovered by reviewing
the current producer and driver owners rather than assuming historical fixes
covered newly added sites.

The statement dispatcher now calls `report_unknown_statement`, which records
the same code, discriminant, message and source span through `error_fatal`.
Diagnostic collection still continues; the driver's existing fatal-error gate
blocks publication. Well-formed statement arms and ordinary advisory severity
are unchanged. No diagnostic-prefix rule is added.

`test/01_unit/compiler/mir/unknown_statement_fatal_spec.spl` exercises this
actual owner and the shared driver classifier, covering fatality, exact
discriminant/message, source span, multiple collected failures, and an advisory
negative control. It does not fabricate an invalid HIR enum handle merely to
enter the dispatch wildcard.

Status: **source repair implemented; executable verification pending**. No
qualified self-hosted test runtime is currently available in this lane. The
focused SSpec and compiler/core/MCP gates have not run; source review does not
constitute native qualification. This follow-up does not close the whole
diagnostic family or claim the other historical candidate sites are fixed.


## GPU dispatch-scoped repair — 2026-11-07

Base release05a4aa7ea1d; closed PR7316 head272348b96515 is the historical
failed candidate, not an accepted fix. Its fatal diagnostic was applied before
intrinsic selection, rejecting atomic pointers and non-index data. The release
owner also evaluated a nonliteral first atomic/data argument in that dimension
probe and again in its ordinary argument path. Both defects share that misplaced
probe; changing only severity is insufficient.

`lower_gpu_intrinsic_call` now selects exactly gpu_global_id, gpu_local_id,
gpu_block_id, gpu_block_dim and gpu_grid_dim before inspecting the dimension.
Nonconstant dimensions are evaluated once for recovery and emit error_fatal at
the source span; default0 and literal dimensions retain their existing behavior.
CAS and ordinary atomic/data operations retain their existing argument owners,
so pointer/data expressions are evaluated once in source order. No new GPU
backend implementation or device-runtime behavior is claimed.

The regression spec preserves the original real parameter, literal/default and
call-valued dimension controls. New controls bind actual pointer/data parameters
for CAS and all eight ordinary atomics, and inspect named effect-call order and
result operand identities for CAS, atomic_add and warp_shuffle. These are actual
MIR owner calls and emitted instruction assertions, not source-presence tests.

Budget: prior six family cycles remain recorded. User “retry about12hrs” explicitly
allows three additional meaningful cycles7–9 until2026-11-07 18:56UTC. This is
cycle7. Independent source review is required before commit/landing. SSpec and
compiler/core/MCP/native verification remain NOT_RUN pending an admitted runtime
and root build slot; source landing is not verification PASS or full closure.

## Function-value refusal follow-up, 2026-11-06

Source pin: release `fadd88059b3c376d709ef697318c6e609b885062`.
`try_lower_function_value` in `expr_dispatch.spl` documents that it refuses
missing or unresolved function signatures rather than guessing a function
pointer ABI. Both refusal paths nevertheless used `self.error`, emitted an
integer-zero recovery local, and returned `Some(local)`. Neither message
matches the shared driver's legacy fatal-prefix rules, so refusal alone did
not block code publication.

The owner-level counterexamples use a known top-level function symbol with
either no retained type, or a signature whose return contains an unresolved
type parameter. The latter checks the return before lowering parameters, so
no separate `lower_type` failure explains away the missing fatal diagnostic.
These are compiler-owner counterexamples; source-level reachability through a
particular HIR producer has not been executed or qualified.

Both refusal paths now use `error_fatal`. Message text, source span, recovery
local creation and continued diagnostic collection remain unchanged. This does
not add support for unresolved function signatures or alter concrete-function
ABI lowering.

`test/01_unit/compiler/mir/function_value_refusal_fatal_spec.spl` checks the
actual owner and driver classifier for both failures, verifies source location,
and retains a concrete i32-to-bool function pointer as the positive ABI control.
Status: **source repair implemented; executable verification pending**.
The SSpec, compiler/core/MCP checks and native smokes are unrun pending a
qualified self-hosted producer. No seed test is substituted, and the broader
diagnostic family remains open.

