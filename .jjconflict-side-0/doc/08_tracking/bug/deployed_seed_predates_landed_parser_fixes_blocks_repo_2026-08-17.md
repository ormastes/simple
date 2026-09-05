# Bug: the DEPLOYED seed predates two landed parser fixes — repo-wide parse block is a stale-binary artifact

- **ID:** deployed_seed_predates_landed_parser_fixes_blocks_repo_2026-08-17
- **Severity:** P1 — every `bin/simple test` / `run` / pre-push guard that parses
  `origin/main`'s compiler source dies in seconds. Not a hang.
- **Discovered:** 2026-08-17, while investigating a reported "expr_dispatch.spl does not parse".
- **Status:** RESOLVED 2026-08-17 by rebuilding + redeploying the seed. Zero `.spl`
  and zero Rust source lines changed. See "Verification" below.

## The finding

Both parse failures attributed to `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
are **already fixed in `src/compiler_rust/`**. The failures reproduce only because
`bin/simple` is a seed built **before** those fixes landed.

| evidence | value |
|---|---|
| `readlink -f bin/simple` | `bin/release/x86_64-unknown-linux-gnu/simple` |
| size / mtime | 59,536,728 bytes, **2026-08-16 22:59:37 UTC** |
| fix A commit | `d7213eb61742` — **2026-08-17 07:36:55 UTC** |
| fix B commit | `17d3496f3f3` — **2026-08-17 12:14:12 UTC** |

Both fixes postdate the binary. The binary cannot contain them.

## Defect 1 — `expected Fn, found Assign` (the hard failure)

Trigger, reduced to four lines (`bin/simple run`, rc read directly):

```
fn main():
    var literal = 1
    literal = 2
    print("ok")
```

`literal` lexes to `TokenKind::Literal` (`parser/src/lexer/identifiers.rs:254`).
The statement dispatcher routed `TokenKind::Literal` unconditionally to
`parse_literal_function`, which immediately `expect`s `Fn` — so **reassigning any
variable named `literal`** failed with `expected Fn, found Assign`, a diagnostic
that never names the keyword collision. `var literal = 1` and `literal` in
expression position always worked (`parse_keyword_identifier("literal")`), which is
why the collision hid for so long.

Bisection inside `origin/main`'s copy of `expr_dispatch.spl` (region deletion, never
`head -N` truncation): deleting lines 138-146 fixed it; deleting any single `match`
arm did not; replacing the arm bodies with `supported = true` fixed it; and
`literal = true` alone still failed while `supported = f(1)` parsed. The single
variable name `literal` is the whole trigger — the new `bare_scalar_const_pattern`
method declares `var literal` at line 136 and reassigns it in three `match` arms.

**Already fixed** at `parser/src/parser_impl/core.rs:670-676` (`d7213eb61742`), which
peeks for `Fn` and otherwise falls through to `parse_expression_or_assignment`.

## Defect 2 — `Use angle brackets: X<...> instead of X[...]` (a WARNING, not an error)

Reported as a parse failure at `expr_dispatch.spl:3074:96` and `:4056:94`. It is
**not** one: `bin/simple run` on that file exits **0** and the text is preceded by
`warning: Deprecated syntax for type parameters`. Trigger (2 of 7 variants):
`i < a.len() and a[i] == "str"` warns; `i < 3 and a[i] == "str"` and
`i < a.len() and true and a[i] == "str"` do not — a backtracked speculative
generic-argument parse leaking the hint it pushed.

**Already fixed** at `parser/src/expressions/postfix.rs` (`17d3496f3f3`) by truncating
`error_hints` to a watermark on both backtrack paths. Documented at
`doc/08_tracking/bug/parser_bracket_index_after_less_than_still_misread_as_generics_2026-08-17.md`.

## What is NOT the cause (corrections to circulating notes)

- **`origin/main` is not carrying broken source.** The 88-line
  `bare_scalar_const_pattern` addition is valid Simple; it merely names a local
  `literal`.
- **`/mnt/data/worktrees/simple-main` does not hold an uncommitted fix for that
  file.** `git status` reports it clean; the local HEAD copy simply *predates* the
  88-line addition (`git diff HEAD origin/main` = +88/-19). Committing the local
  copy would **revert another lane's feature work** — the clobber pattern
  `.claude/rules/vcs.md` forbids.
- **The push block is not this defect.** `check-native-trailing-default-param.shs`
  run from the main tree reaches its selftest and its real scan, then reports
  `FAIL — native-build failed to compile the fixture (exit 1, ...)`, exit **1**
  (not ERROR/2). Cause is an unrelated LLVM lane defect:
  `llc-20: invalid redefinition of function '__simple_main'`. Tracked under
  `native_build_static_method_trailing_default_unresolved_2026-08-17.md`.

## Fix

Rebuild and redeploy the seed from current `src/compiler_rust/`
(`cargo build --release --bin simple`, then redeploy to
`bin/release/<triple>/simple`). No source change is required for either parse defect.

**The systemic gap this exposes:** nothing in the repo detects that the deployed
binary is older than a landed parser fix. Every guard checks tree structure or
compiles the tree; none compares `bin/release/<triple>/simple`'s mtime against the
newest commit touching `src/compiler_rust/`. That single comparison would have
turned a multi-session, repo-wide misdiagnosis ("origin/main's source is broken",
"another lane has an uncommitted fix") into a one-line verdict. Worth a guard.

## Verification (ablation across the binary, holding source fixed)

One tree, one source state, two binaries. `rc` read into a shell variable on the
line after each command — never through a pipe.

| probe | stale seed (2026-08-16 22:59Z) | rebuilt seed (2026-08-17 12:58Z) |
|---|---|---|
| 4-line `literal = 2` repro | `Unexpected token: expected Fn, found Assign`, rc=1 | prints `ok`, **rc=0** |
| `origin/main`'s `expr_dispatch.spl` | 1 parse error, rc=1 | **0** parse errors, rc=0 |
| local HEAD's `expr_dispatch.spl` | 4 `Use angle brackets` warnings, rc=0 | **0** warnings, rc=0 |

Rebuild: `CARGO_TARGET_DIR=/mnt/data/cargo-litfix cargo build --release --bin simple`
in `src/compiler_rust`, rc=0. Deployed to
`bin/release/x86_64-unknown-linux-gnu/simple` (59,537,240 bytes) via `cp` to
`.new` + `mv` per `.claude/rules/code-style.md` (a direct `cp` hits "Text file
busy"). Post-deploy `bin/simple run` on the repro prints `ok`, rc=0.

Because the source was never touched, this is an ablation on the binary axis
alone: it proves the deployed artifact, not the tree, was the defect.

## Guard re-run after the redeploy (the residual FAIL is a DIFFERENT defect)

`sh scripts/check/check-native-trailing-default-param.shs`, run from the main tree
on the rebuilt seed, `rc` read into a variable:

```
GUARD_RC=1
FAIL — native-build failed to compile the fixture (exit 1, log saved to /tmp/check-native-trailing-default-param.2785153.log)
```

That is a **real verdict line**, exit 1 — not `ERROR — nothing was checked` / exit 2,
and the fatal `--selftest` ran to completion first. So the guard is functioning; it
is reporting a genuine downstream failure.

**The failure mode changed with the seed**, which is itself evidence the old symptom
was binary-bound:

| seed | guard failure |
|---|---|
| stale | `llc-20: invalid redefinition of function '__simple_main'` (LLVM lane) |
| rebuilt | `error[E1002]: function `TMPDIR` not found`, during the `parse` step |

The LLVM redefinition is gone. The residual `TMPDIR` error is unrelated to the
fixture (neither `main.spl`, `dep.spl` nor the guard script mentions `TMPDIR`); the
only occurrence in the tree is
`src/compiler/70.backend/backend/runtime_compiler.spl:55`,
`val tmpdir = rt_env_get("TMPDIR")` — i.e. a **string-literal argument being
resolved as a function name** somewhere on the native-build path. That belongs to
the `native_trailing_default_param_guard_*` / `native_build_static_method_*` open
family, not to this record, and is left OPEN rather than papered over.

## Second-order defect worth its own attention

The `expected Fn, found Assign` diagnostic carries **no file line/column** when
surfaced through the module loader (`parse: in "<file>": Unexpected token: ...`),
which is what made this cost a full bisection. The span exists at the parser level;
it is dropped on the way out.
