# Bare `T?` in condition position silently takes the WRONG branch

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).
T3 full bootstrap to confirm. See "Fix landed" below for the precise reason
this cannot be closed as FIXED yet. Originally found
2026-08-01 while triaging
`optional_query_operator_identity_passthrough_2026-07-20` (which was itself
INVALID; this is the real defect in the neighbourhood).

**Severity:** high — silent wrong result, no diagnostic.

## Symptom

Using an optional directly as a condition, without `.?`, takes the branch for
"present" even when the value is absent:

```
if lookup(false).?:    # -> else branch   (CORRECT)
if lookup(false):      # -> THEN branch   (WRONG)
```

## Why

`RT_NIL` is the sentinel value `3`, which is non-zero and therefore truthy
under a plain truthiness test. So an absent optional reads as present.

This is the exact hazard the `lower_cond_expr` docstring
(`src/compiler/50.mir/mir_lowering_stmts.spl:1468-1494`) warns about. That
function implements a deliberate position split — `.?` in VALUE position keeps
the payload, `.?` in CONDITION position lowers to `rt_is_some` — but the split
only fires when `.?` is present. A bare optional never reaches it.

## Why this is not the same bug as the one that found it

`optional_query_operator_identity_passthrough_2026-07-20` claimed `.?` should
return `bool` and was closed INVALID: `.?` is specified to return `T?` in three
independent places (`doc/07_guide/quick_reference/syntax_quick_reference.md:505`,
`src/compiler/10.frontend/parser_types_expr.spl:229`, and the MIR position split
above). This defect is the INVERSE — not `.?` doing the wrong thing, but a
MISSING `.?` being silently accepted where it changes the answer.

## Open question for whoever owns this

Two defensible fixes, and the choice is a language decision rather than a bug
fix, so it is recorded rather than guessed:

1. Make a bare `T?` in condition position lower through `rt_is_some` too, so
   `if x:` and `if x.?:` agree.
2. Reject a bare `T?` in condition position as a type error, forcing `.?`.

Option 2 matches the existing idiom guidance (`.claude/rules/language.md:14`
prefers `.?` over `is_*` predicates) and turns a silent wrong answer into a
compile error, which is the better failure mode. Option 1 is friendlier but
leaves two spellings meaning the same thing.

Not fixed here: picking one silently changes the meaning of existing code that
compiles today.

## Fix landed 2026-08-10

Re-examined: this is NOT a genuine two-way language-design fork. Option 2
(reject at compile time) is the one that would silently change the meaning of
code that "compiles today" in a disruptive way (every existing `if opt:` site
turns into a hard error, unmeasured blast radius). Option 1 does not have that
problem, because there is no third behavior being displaced — the ONLY case
whose observable result changes is the absent (`None`) case, which was always
computing the wrong answer (`RT_NIL == 3` read as truthy). The present case
was already correct (any non-nil payload is non-zero and truthy), so it is
unaffected. There is no existing program that could be relying on "absent
optional in condition position takes the then-branch" as correct behavior,
because that state is indistinguishable from a compiler bug from the
program's point of view. So Option 1 is a strict bug fix, not an RFC-worthy
semantics choice.

Implemented in `lower_cond_expr`
(`src/compiler/50.mir/mir_lowering_stmts.spl`, the `case _:` fallthrough
arm): the condition is lowered via `lower_expr` as before, but if the
resulting local's semantic HIR type is `HirTypeKind.Optional(_)`, the raw
value is routed through the same `rt_is_some` runtime call the pre-existing
`ExistsCheck` (`.?`) arm already uses, instead of being branched on directly.
Non-optional conditions are untouched (`cond_local` returned as-is), so `if
b:` for a plain `bool` has zero code-path change.

This does not touch or resolve `bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04.md`
(a different site: a *bool-typed parameter*, not a raw `if` condition) or the
`.?`-return-type documentation contradiction noted in that file — both remain
open.

## Verification — what was actually tried, and why it stops short of runtime proof

**Tried:** ran the exact repro through `bin/simple test` against a live spec
(`describe/it/expect` wrapping `if lookup(false): ... else: ...`) to check
whether compiler-source edits are live under the deployed binary the way
library-source edits sometimes are. Result: the spec still FAILED
(`expected then to equal else`) with the fix present in source. This is not
evidence the fix is wrong -- `bin/simple --version` identifies the currently
deployed binary as the **Rust bootstrap seed**, which has its own independent
Rust implementation of MIR lowering (`src/compiler_rust/**`) and never reads
or executes `src/compiler/50.mir/mir_lowering_stmts.spl` at all. Editing that
file cannot be "live" under the seed by construction -- there is no code path
from this pure-Simple source file to seed execution. (The seed's own
interpreter appears to have the *same class* of bug independently, but that
is `src/compiler_rust`, explicitly off-limits for this pass and a separate
defect to file, not to fix here.)

Checked `.claude/rules/bootstrap.md`'s verification tiers before assuming T3
was really required: T0 ("hosted seed probe") applies to logic that the seed
can run directly, which is exactly the case that just failed for the reason
above -- the seed cannot exercise pure-Simple compiler-internals source at
all, hosted or not. T1 ("incremental kernel build") is explicitly scoped to
"a small pure-Simple **lib** change ... that feeds the freestanding kernel";
this change is to `src/compiler` itself, which the same doc's own T3 line
states in so many words: "T3 — full bootstrap. ONLY when the compiler itself
changed (`src/compiler_rust` seed or `src/compiler` pure-Simple)." There is
no narrower tier for a change to the self-hosted compiler's own MIR-lowering
source -- confirmed structurally (which module the file lives under), not
merely assumed. T3 requires exactly the `bin/simple build bootstrap` /
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap` step this
session's mandate forbids running, and no locally cached self-hosted binary
post-dates this edit (checked `bootstrap/stage3/simple` etc. -- all built
2026-08-09, before this change, and rebuilding them requires the same
forbidden step).

**What IS backed by real execution today:** a source-content regression spec,
`test/01_unit/compiler/driver/bare_optional_condition_rt_is_some_guard_spec.spl`,
sabotage-verified in this pass:
1. GREEN with the fix present (`declared>=1 executed=1 passed=1 failed=0`).
2. Reverted the fix in place (restored the original one-line `case _:
   self.lower_expr(cond)` fallthrough) -> spec went RED
   (`passed=0 failed=1`, `expected then to equal else` no longer applies here
   since the guard spec is content-based, but the failure was the missing
   fix-marker strings).
3. Restored the fix -> spec back to GREEN, and `git hash-object` confirmed
   the restored file is byte-identical to the version already pushed to
   `origin/main` (`33a55d749f3a6ddd79e8bd6732d53953063262a4`).

This proves the fix is present, syntactically well-formed enough to compile
under this test run, and covered by a regression guard that will catch a
future accidental revert. It does **not** prove the fixed MIR lowering
produces the correct branch at runtime, because nothing that runs in this
session's environment executes that lowering path. **Anyone with T3
bootstrap access:** rebuild the self-hosted binary from this commit, deploy
it as `bin/simple`, and run the repro directly:
```
if lookup(false):      # expected after fix: else branch (was: THEN branch, wrong)
```
plus the behavioral spec at `/tmp/probe_spec/bare_optional_cond_probe_spec.spl`
(not committed -- recreate from the "Symptom" repro above) to get the actual
runtime confirmation this doc cannot provide from this session alone.

## Related

- `dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20` (OPEN) — a
  neighbouring but distinct defect: an unchecked `bool` PARAMETER coercion lets
  `check(opt.?)` pass `42` into a `bool` slot. Not `.?`-specific; `check(7)`
  does the same.
- `coalesce_on_raw_i64_corrupts_index_3` — same `RT_NIL == 3` sentinel, biting
  in a different operator.
