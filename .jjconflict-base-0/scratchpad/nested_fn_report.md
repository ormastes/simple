# Nested Named Functions — Native `--entry` Path Characterization

**Scope:** ONE ITEM — non-capturing/capturing nested named functions
(`fn outer(): fn inner(...): ...; inner(...)`) on the native `--entry` build
path. Pinned commit: `35c4b52ead636edda2f2c8f9706ede0abb86d8e5` (worktree
`/tmp/wt_nestfn`, binary linked to
`bin/release/x86_64-unknown-linux-gnu/simple`).

## Headline finding: native-build is universally broken at this commit

Before any nested-fn-specific work could be characterized, the baseline
native path itself was tested and found **completely non-functional for any
Simple program** at the pinned commit — not just for nested functions.

- Trivial baseline `fn add(a,b)->i64: return a+b` / `fn main(): print(add(2,3))`
  fails to build: `error: semantic: type mismatch: cannot cast array to i64`,
  exit 1, no binary emitted. Reproduced deterministically 3/3 tries, with and
  without `SIMPLE_BOOTSTRAP=1`.
- Even `fn main(): print(1)` (single line) fails identically.
- `SIMPLE_COMPILER_TRACE=1` shows the crash happens at
  `[frontend] parse_and_build:start path=<file>` — i.e. inside the
  self-hosted `.spl` **parser**, before any HIR/nested-fn-specific lowering
  is ever reached. This is a parse-stage failure for the simplest possible
  program, not a nested-fn-scoped issue.
- Ran the repo's own `scripts/check/native-smoke-matrix.shs` (15 cases,
  unrelated to this task) — **result: 0/15 pass, 15/15 build-failed**, every
  single case (arithmetic, if/else, while, arrays, structs, enums, strings,
  dict, closures, Option, Result, and the matrix's own `nested_fn_3deep`
  case) hits the exact same `cannot cast array to i64` error. `option_nil_check`
  (the one case the task allows to fail) failed for the *same* reason as
  everything else, not for its own distinct known reason.
- A sibling parallel-agent worktree (`/tmp/wt_chain`) was observed, during
  this session, independently bisecting the same commit range
  (`f10db44f0f4 4193dffee1e 2611a119b51 87ddcece561 b60984e621f 9e67d55918e`,
  ancestors of `35c4b52ead6`) for native-build regressions — confirming this
  is an already-known, actively-being-chased, repo-wide "redeploy wall"
  issue (matches memory note `project_native_build_cannot_emit_2026-07-08`:
  "native-build emits no binary on ANY backend in current source"), not
  something introduced by, or specific to, nested-function handling.

**Conclusion: the native `--entry` path cannot be exercised at all right now
for this commit**, so there is no way to empirically build/run/verify any
nested-fn-specific native binary, nor to safely land or verify a fix on this
axis. Per the hard rule ("never convert loud → silent-wrong"), the current
behavior is already maximally loud (non-zero exit, no binary emitted, clear
error text) — there is nothing to make "loud" that isn't already loud, and
no way to test a "fix" without a working baseline. I did not touch any
source file (see `nested_fn.patch` — empty diff on tracked files).

## Oracle (interpreter) characterization — the 5 requested shapes

Since native-build cannot run, the oracle
(`env -u SIMPLE_BOOTSTRAP bin/simple run p.spl`, which uses the Rust seed's
built-in interpreter/JIT-fallback, NOT the self-hosted parser used by
native-build) was used to characterize interpreter-side behavior for #52
(already claimed fixed) plus the new edge cases requested:

| # | Shape | File | Result | Notes |
|---|-------|------|--------|-------|
| 1 | Non-capturing nested fn, called once | `scratch/t1_basic.spl` | **4** (correct, `3+1`) | JIT lowering fails first (`HIR lowering error: Unknown variable: inner while lowering outer`), falls back to interpreter, which then computes correctly |
| 2 | Nested fn called twice, different args | `scratch/t2_twocalls.spl` | **15** (correct, `inner(3)+inner(10)=4+11`) | Same JIT-fallback pattern |
| 3 | Nested fn capturing outer local | `scratch/t3_capture.spl` | **101** (correct, `outer_local+1=100+1`) | Same JIT-fallback pattern; interpreter DOES support the capture correctly |
| 4 | Two outer fns, same-named nested fn in each | `scratch/t4_collision.spl` | **2** then **101** (both correct — `outer_a`'s `inner(1)+1=2`, `outer_b`'s `inner(1)+100=101`) | No collision; each outer's `inner` resolves independently |
| 5 | Nested fn **shadowing** a top-level fn of the same name | `scratch/t5_shadow.spl` | **1005** then **1005** — **WRONG** | Expected `outer()` → **6** (its own nested `helper(5)=5+1`), then top-level `helper(5)` → **1005**. Got `1005` **both times**: `outer()`'s call silently resolved to the outer/module-scope `helper`, completely ignoring its own nested `helper` declaration. No warning, no fallback-notice printed for this case (unlike 1-4) — the lookup found *a* symbol directly and never hit the "unknown variable" path that triggers interpreter fallback in the other cases. |

**New finding (shape 5): nested-fn shadowing of a same-named top-level
function is silently wrong in the current interpreter/oracle path**, not
merely "unfixed on native" — this is a genuine correctness bug independent
of native-build, and it violates the project's "no silent-wrong" rule. It
was not previously called out as fixed or broken by the #52 characterization
this task was scoped against. This is a **new bug to file**, distinct from
this task's native-`--entry` scope (fixing it means changing nested-fn name
resolution/scoping in the interpreter's declare/lookup path, which is a
different, non-native-path piece of work, and I have no reliable way in this
environment to verify a scoping fix doesn't regress other things while the
native/self-hosted toolchain is down).

## Design note (informational only — not implemented, not verified)

The task's suggested design was to lambda-lift nested `Function` declarations
to synthesized top-level functions at the HIR level
(`20.hir/hir_lowering/` declaration/statement lowering), mangling names and
rewriting call sites, mirroring the `#165` `__lambda_lift_<n>` machinery in
the (owned, off-limits) `switch_operators_calls.spl`. `20.hir/hir_lowering/_Items/module_lowering.spl`
is the natural home for this (it already does two lowering passes: declare
symbols, then lower bodies), but the file is dominated by extensive
`bootstrap_mode`-specific branches for self-hosting the compiler itself and
would need careful scoping to avoid touching that path. No implementation
was attempted: with native-build unable to compile *anything*, there is no
way to build/run a check to distinguish a correct lift from a broken one,
and landing an unverified change to shared, actively-touched HIR lowering
code carries real risk of silently regressing other in-flight lanes' work.

## Battery / matrix status vs. task's gate

Task asked for oracle-equal-or-loud-fail across the 5 shapes plus a
multi-construct case, and `native-smoke-matrix.shs` gate ≥14/15 with only
`option_nil_check` allowed to fail. Actual: smoke matrix is **0/15**
(everything fails for the same non-nested-fn-related parse-stage bug), so
the gate cannot be met in the current environment regardless of any
nested-fn work — this is an environmental blocker, not a battery failure of
a fix that was attempted here.

## Deliverables

- `/home/ormastes/dev/pub/simple/scratchpad/nested_fn.patch` — empty (no
  tracked-file changes made; see reasoning above)
- `/home/ormastes/dev/pub/simple/scratchpad/nested_fn_report.md` — this file
- Worktree `/tmp/wt_nestfn` removed after this report was written
- Test fixtures used (for reference, not committed):
  `/tmp/wt_nestfn/scratch/t1_basic.spl` … `t5_shadow.spl`,
  `t0_baseline.spl`, `t_min.spl`

## Recommendation

1. Do not attempt to land a nested-fn-specific native fix until the
   repo-wide native-build parse-stage regression (`cannot cast array to
   i64`, reproduces on `fn main(): print(1)`) is resolved — this is already
   being bisected by another lane (observed live in `/tmp/wt_chain`).
2. File the shape-5 finding (nested-fn shadowing a same-named top-level fn
   silently resolves to the wrong function) as its own bug — it is real,
   reproducible today via the oracle interpreter, and separate from the
   native-path task.
3. Once native-build is restored, re-run this same battery
   (`scratch/t1..t5_*.spl` shapes + a multi-construct combining two outers
   with nested fns and top-level fns) against native to get the actual
   native-path characterization this task set out to produce.
