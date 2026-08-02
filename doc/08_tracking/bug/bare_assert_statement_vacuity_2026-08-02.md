# Bare `assert` vacuity — remaining inert sites after the interpreter fix

**Date:** 2026-08-02
**Status:** interpreter half FIXED (`7d73d4dd3a6e`); two sites still OPEN
**Related:** `doc/08_tracking/bug/` spec-DSL false-green family; shim-vacuity findings

## What was fixed

A bare `assert <cond>` statement was silently inert in the Rust seed
interpreter everywhere except the top-level statement path. `Node::Assert`
had no arm in `exec_node` (plain `fn` bodies) nor in
`exec_block_closure_mut` / `exec_block_closure_into` (lambda, block-closure
and BDD `it`-block bodies), so it fell through their catch-all wildcard.

Measured pre-fix: an `it` block containing only `assert 1 == 2` reported
PASS. Fixed in `7d73d4dd3a6e`.

## Measured truth table (2026-08-02, `simple run <spec>`)

Each form deliberately made FALSE; a form that stays green is inert.
Fixture: 30 examples across three spec files, plus TRUE controls.

| form | pre-fix | post-fix |
| --- | --- | --- |
| `assert a == b` | INERT | fails |
| `assert false` / `assert <bool var>` | INERT | fails |
| `assert a == b, "msg"` | INERT | fails |
| `assert <call>()` | INERT | fails |
| `assert` nested in `if` / `for` | INERT | fails |
| `assert` inside a called plain `fn` | INERT | fails |
| `expect(<literal>)` / `expect(<identifier>)`, no matcher | INERT | **still INERT** |
| `assert!(...)` macro form | fails | fails |
| `assert(...)` paren-call form | fails | fails |
| `assert_true` / `assert_false` / `assert_eq` / `assert_ne` | fails | fails |
| `assert_nil` / `assert_not_nil` / `assert_contains` | fails | fails |
| `expect(a == b)` infix, `expect(x).to_be/.to_equal`, `expect_not` | fails | fails |
| `expect(<call>())` no matcher | fails | fails |
| `fail_assertion("...")` | fails | fails |

TRUE controls (`assert 1 == 1`, `assert_true(true)`, `expect(1).to_equal(1)`,
`expect(1 == 1)`) pass both before and after — the measurement is not
degenerate.

## OPEN 1 — pure-Simple compiler DISCARDS `assert` entirely

`src/compiler/10.frontend/core/parser_stmts.spl` (the `if ident_text ==
"assert":` branch) parses the condition and the optional message and then
returns `stmt_expr_stmt(assert_cond, 0)` — an ordinary expression statement.
The condition's value is thrown away and the message is bound to an unused
local. There is no `StmtKind` for a runtime assert at all, so the self-hosted
compiler cannot lower one.

This means bare `assert` is still inert on the pure-Simple path, which is the
intended default tooling. The interpreter fix does not cover it.

Fixing it needs a bootstrap lane: `src/compiler/**` and `src/lib/**` contain
bare `assert` statements themselves, so making them live is a truth reveal
inside the compiler's own sources and must be verified by a full bootstrap.

## OPEN 2 — `expect(<literal-or-identifier>)` with no matcher is inert

`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`, the general
`expect` fallback path. Comparison forms and `Expr::Call` / `Expr::MethodCall`
subjects set `BDD_EXPECT_PROVISIONAL`; a plain literal or identifier subject
does not, so `expect(flag)` with `flag == false` and no `.to_*()` chain
reports PASS.

The in-tree rationale is that eagerly hard-failing broke
`expect(false).to_equal(false)`. That rationale predates
`BDD_EXPECT_PROVISIONAL` + `BDD_MATCHER_RAN`, which a following matcher
already clears — so marking a falsy literal/identifier subject PROVISIONAL
should now be safe. Not changed here because it is a different failure family
from the `assert` statement and deserves its own verification pass.

Census (anchored, `/usr/bin/grep -rEl '^[[:space:]]*expect\([A-Za-z_][A-Za-z0-9_.]*\)[[:space:]]*$' test --include=*.spl`):
**25 files**.

## OPEN 3 — `test/01_unit/compiler/native/baremetal_syntax_spec.spl` executes nothing under `run`

Under `simple run`, that file emits no example results at all — its 22
`describe`/`it` blocks produce zero `PASS`/`FAIL` lines, only a trailing
printed feature list. Its assertions are also tautological (they assert on
string literals the test itself just wrote, e.g. `val keyword = "unsafe"` then
`assert keyword == "unsafe"`), so even once live they prove nothing about
baremetal syntax. Rewrite is a separate task; do not treat it as coverage.

## Census of bare `assert` in specs (2026-08-02)

Predicate: `/usr/bin/grep -rEl '^[[:space:]]*assert[[:space:]]+[^[:space:]]' test --include=*.spl`
(excludes `assert(`, `assert!`, and `assert_*(` — after `assert` the next
character must be whitespace).

- **15 files**, **144 bare-assert lines** under `test/**`.
  8 distinct files; the rest are `test/unit/**` / `test/system/**` mirrors of
  `test/01_unit/**` / `test/03_system/**` that are byte-identical.
- Per-example classification (`it` block granularity, mirrors included):
  **75 FULLY_VACUOUS** (bare assert is the only assertion — the example proved
  nothing), **3 PARTIAL** (also carries a live `expect`), 37 already-OK,
  19 with no assertion at all.
  De-duplicating mirrors: ~41 fully vacuous, ~2 partial.
- Repo-wide (`src` + `test`): **76 files** use bare `assert`. The `src/**`
  occurrences are in-language contract checks that were equally disabled in
  the interpreter — and remain disabled on the pure-Simple path (OPEN 1).

Files carrying fully-vacuous examples:

- `test/01_unit/app/interpreter/collections/persistent_dict_intensive_spec.spl` (45 bare asserts, 14 vacuous examples)
- `test/01_unit/compiler/native/baremetal_syntax_spec.spl` (14 / 14) — see OPEN 3
- `test/01_unit/os/services/nvfs/posix_shim_test.spl` (8 / 5)
- `test/01_unit/compiler/codegen/native_cross_module_abi_spec.spl` (3 / 3)
- `test/01_unit/compiler/codegen/baremetal_cross_module_val_spec.spl` (3 / 2)
- `test/03_system/quality/code_quality/deprecated_removed_spec.spl` (1 / 1)
- `test/03_system/quality/code_quality/iter_deprecated_spec.spl` (1 / 0, 1 partial)
- the two `.spipe_matchers_*` generated siblings of the above
- plus the `test/unit/**` and `test/system/**` byte-identical mirrors

## Truth reveal

Running every affected spec with the fixed binary: **zero examples turn red.**
The previously-inert assertions all in fact hold — the vacuity was real but
the assertions were true. `test/01_unit/os/services/nvfs/posix_shim_test.spl`
fails to compile at all (missing `opendir` on `NvfsPosixDriver`), identically
before and after, so it is unaffected by this change and is a pre-existing
separate defect.

The reveal measurement is itself proved non-vacuous: sabotaging one
previously-inert assertion in a copy of the persistent-dict spec
(`assert dict.len() == 0` -> `== 999`) turns exactly that example red under
the fixed binary.

## Why the specs were NOT rewritten to `expect`

Making bare `assert` live is the fix; the affected specs now assert for real
without any edit, and rewriting 144 lines across 15 files would be churn that
changes no behaviour on the interpreter path. The case for migrating anyway is
OPEN 1 — bare `assert` stays inert on the pure-Simple path until the parser is
fixed. Recommendation: fix OPEN 1 rather than migrate the specs, because a
migration leaves every `src/**` contract check still disabled.

## Trap for future lanes

`bin/simple test <spec>` does NOT execute the spec in the invoked binary. It
spawns `src/compiler_rust/target/debug/simple test --no-session-daemon ...`,
which in turn spawns `src/compiler_rust/target/debug/simple run <spec>`. A
freshly built binary invoked as `simple test` therefore measures the OLD
debug binary in the shared working copy and shows no change at all — this
lane hit exactly that and briefly concluded the fix had no effect. Use
`<your-binary> run <spec>` to measure the binary you actually built.
