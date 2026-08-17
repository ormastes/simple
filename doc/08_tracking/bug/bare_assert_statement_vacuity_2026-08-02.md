# Bare `assert` vacuity — remaining inert sites after the interpreter fix

**Date:** 2026-08-02
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
(`62c075bbe3cf`); OPEN 3 FIXED (`f93a9abb5d0d`); **OPEN 1 still OPEN** — it
needs more than the parser change first assumed, see the revised section below
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
| `expect(<literal>)` / `expect(<identifier>)`, no matcher | INERT | INERT until `62c075bbe3cf`, now fails |
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

## OPEN 1 — pure-Simple compiler DISCARDS `assert` entirely (STILL OPEN)

`src/compiler/10.frontend/core/parser_stmts.spl` (the `if ident_text ==
"assert":` branch, line 615) parses the condition and the optional message and
then returns `stmt_expr_stmt(assert_cond, 0)` — an ordinary expression
statement. The condition's value is thrown away and the message is bound to an
unused local. There is no `StmtKind` for a runtime assert at all, so the
self-hosted compiler cannot lower one.

This means bare `assert` is still inert on the pure-Simple path, which is the
intended default tooling. The interpreter fix does not cover it.

### Why the obvious one-line parser patch is NOT enough — do not land it

The tempting patch mirrors the `print` desugar 10 lines above in the same
function and turns the statement into an ordinary call:

```
        if ident_text == "assert":
            parser_advance()
            val assert_cond = parse_expr()
            var assert_args: [i64] = []
            assert_args.push(assert_cond)
            if par_kind_get() == 160:
                parser_advance()
                val assert_msg = parse_expr()
                assert_args.push(assert_msg)
            val assert_callee = expr_ident("assert", 0)
            val assert_call = expr_call(assert_callee, assert_args, 0)
            return stmt_expr_stmt(assert_call, 0)
```

That patch is structurally correct and it is what the `print` branch does, but
landing it alone would make things WORSE, because **there is no runtime
`assert` callee anywhere on the pure-Simple path for it to resolve to.**
Verified by exhaustive anchored grep over `src/compiler/**`:

- `src/compiler/70.backend/backend/interpreter_calls.spl` dispatches builtins
  by name (`print`, `println`, `to_string`, `str`/`text`, `type_of`, `clone`,
  `file_exists`, …) — **no `assert` arm**.
- `src/compiler/30.types/type_system/builtin_registry.spl` — **no `assert`
  entry** (no match for `assert` at all).
- `src/compiler/95.interp/mir_interp_intrinsics.spl` — **no `assert`
  intrinsic**.
- The only `assert`-shaped things the self-hosted compiler knows are
  compile-time: `@static_assert`, desugared by the parser into
  `__traits("static_assert", cond, msg)` and handled in
  `src/compiler/10.frontend/core/interpreter/eval_builtins.spl`; and
  `asm assert [...]`, a target guard handled in
  `_ParserPrimary/primary_expr.spl`. Neither is a runtime assertion.

So an emitted `assert(...)` call would land on an unregistered callee. Per
`reference_unregistered_extern_returns_nil_silently` and
`reference_documented_dict_workaround_was_itself_link_broken`, that is either a
link error or a silent nil — i.e. it would trade a knowingly-inert statement
for a statement that looks live and is not, which is strictly worse.

### What the real fix needs (two coordinated changes, one bootstrap)

1. The parser patch above, so the condition and message stop being discarded.
2. A runtime `assert` builtin on the pure-Simple path, wired the same way
   `print` is: a name arm in `70.backend/backend/interpreter_calls.spl`, an
   entry in `30.types/type_system/builtin_registry.spl`, and lowering that
   calls the existing C runtime primitive `rt_panic` (declared
   `src/runtime/runtime.h:300`, defined `src/runtime/runtime_native.c:8498`)
   on a false condition, with the optional message threaded through.

**Both halves must land together and the result must be verified by a full
bootstrap**, because `src/compiler/**` and `src/lib/**` contain bare `assert`
statements themselves — 76 files repo-wide use the form — so making them live
is a truth reveal inside the compiler's own sources.

**Status of this analysis: the mechanism is PROVED (grep is exhaustive and
anchored, and the parser line is read directly). The patch above is
UNVERIFIED — it has not been compiled or bootstrapped.** It is filed rather
than landed deliberately: an unverified guess landed as a fix is worse than a
precise filing.

## OPEN 2 — `expect(<literal-or-identifier>)` with no matcher was inert — FIXED `62c075bbe3cf`

`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`, the general
`expect` fallback path. Comparison forms and `Expr::Call` / `Expr::MethodCall`
subjects set `BDD_EXPECT_PROVISIONAL`; a plain literal or identifier subject
does not, so `expect(flag)` with `flag == false` and no `.to_*()` chain
reports PASS.

The in-tree rationale is that eagerly hard-failing broke
`expect(false).to_equal(false)`. That rationale predates
`BDD_EXPECT_PROVISIONAL` + `BDD_MATCHER_RAN`, which a following matcher
already clears — so marking a falsy literal/identifier subject PROVISIONAL
should now be safe. **Confirmed and fixed in `62c075bbe3cf`:** the eager mark
is now applied to every subject shape, PROVISIONAL only, never hard.

Census (anchored, `/usr/bin/grep -rEl '^[[:space:]]*expect\([A-Za-z_][A-Za-z0-9_.]*\)[[:space:]]*$' test --include=*.spl`):
**25 files**, **22 distinct after de-duplicating the `test/unit/**` mirrors of
`test/01_unit/**`** (`md5sum | uniq -c`: 22 distinct contents across 25 files).

### Decision: assert truthiness, do NOT make it a loud error

Argued from the DSL's own semantics, not convenience. The `expect` handler in
`interpreter_call/bdd.rs` recognises four subject shapes, and three of them
already meant "assert truthy" before this change:

| subject shape | matcher-less behaviour BEFORE |
| --- | --- |
| `expect(a == b)` / `expect(a != b)` | falsy ⇒ PROVISIONAL ⇒ example fails |
| `expect(a < b)` and other ordered comparisons | falsy ⇒ PROVISIONAL ⇒ fails |
| `expect(f())` / `expect(x.m())` | falsy ⇒ PROVISIONAL ⇒ fails |
| `expect(<literal>)` / `expect(<identifier>)` | **asserted nothing** |

So truthiness is already the form's meaning; the literal/identifier case was
the sole hole. Making it assert restores consistency rather than adding a
fourth semantics. Erroring instead would have to error for `expect(f())` and
`expect(a == b)` too, which are live and in wide use — that is a much larger,
gratuitously breaking change with no semantic justification.

The prior lane's reasoning **does transfer**: bare `assert` was made to *work*
rather than error because it is a first-class statement with existing lowering.
Matcher-less `expect` is likewise a first-class form with existing live
semantics on its sibling shapes. The transfer holds for the same reason in both
cases — the form already exists and already means something everywhere else.

### Truth reveal (OPEN 2)

Running all 25 affected files under the fixed binary: **zero examples turn
red.** The failure NAME SET is byte-identical before and after — 17 entries,
all pre-existing (13 `file_io_spec` / `file_system_spec` example failures, plus
4 `no_paren_test.spl` files that execute no examples at all).

Non-vacuity of that reveal is proved by sabotaging a **real affected spec**,
not a shim or a local copy of the DSL: flipping `val is_type = true` to `false`
at `test/unit/app/lsp/symbol_kind_spec.spl:308` turns exactly that example red
under the fixed binary and leaves it green under the base binary, with the
identically-named sibling example at output line 80 staying green as a local
control.

Note for a follow-up lane: many of the revealed-live `expect(<ident>)` sites
are themselves tautological — e.g. `val is_type = true` immediately followed by
`expect(is_type)` proves nothing about the code under test. They now *run*, but
running is not the same as testing. Same shape as OPEN 3's file.

## OPEN 3 — a spec with a `fn main` executes ZERO examples under `run` — FIXED `f93a9abb5d0d`

Under `simple run`, `test/01_unit/compiler/native/baremetal_syntax_spec.spl`
emitted no example results at all — its `describe`/`it` blocks produced zero
`PASS`/`FAIL` lines, only a trailing printed feature list, and it exited 0.

### Root cause — it is NOT specific to that file

**PROVED by measurement on a two-example fixture whose second example is
deliberately false:**

| invocation | result |
| --- | --- |
| default engine, file contains `fn main` | prints `MAIN RAN`, **0 examples, exit 0** |
| same file with `fn main` deleted | 2 examples, 1 failure, exit 1 |
| same file, `SIMPLE_EXECUTION_MODE=interpreter` | 2 examples, 1 failure, exit 1 |

The silencing mechanism is **engine selection gated on the presence of
`main`**. With a `main` present, `run` takes the JIT entry path, which calls
`main` and nothing else; every module-level `describe`/`it` statement is
dropped. Without a `main`, `has_main_function` is false and the pipeline falls
back to the interpreter, which does execute module-level statements
(`pipeline/execution.rs:586`, `driver/src/exec_core.rs:606`/`878`).

This is the general shape of the trap: **a spec that declares a `fn main`
reports success for having executed nothing.**

### Census of what else it silenced

26 spec files under `test/**` declare both a `fn main` and module-level BDD
blocks. Measured base-vs-fixed, **6 of them executed zero examples** (3 distinct
after de-duplicating the `test/unit/**` mirrors) and now execute **86 examples,
43 distinct**:

| file | before | after |
| --- | --- | --- |
| `test/01_unit/compiler/native/baremetal_syntax_spec.spl` | 0 | 14 |
| `test/01_unit/compiler/custom_primitive_sffi_spec.spl` | 0 | 20 |
| `test/01_unit/gpu/graphics_session_spec.spl` | 0 | 9 |

Truth reveal: **zero of the 86 turn red.** No file in the census runs fewer
examples than before, and every file that already had failures has the same
failure count before and after (5/5, 5/5, 2/2, 1/1, 2/2 — all pre-existing).

### Fix

`run_file_jit` now bails out to the interpreter when the module declares
module-level examples, exactly like the generator bail-out immediately below
it. This also covers the explicit `SIMPLE_EXECUTION_MODE=jit` case, so no
invocation can reach the zero-example silent success again. Detection uses the
repo's own authority, `simple_parser::test_analyzer::extract_file_test_meta`,
whose `analyze_node` does **not** descend into `Node::Function` bodies — so a
program whose examples live inside a function is untouched. Three unit tests in
`exec_core.rs` pin that invariant, because the bail-out would misfire for
ordinary programs if the analyzer ever started descending.

### Still open on this file — tautological assertions

`baremetal_syntax_spec.spl` now genuinely runs, but its assertions remain
tautological: each example writes a string literal into a local and then
asserts that same literal (`val keyword = "unsafe"` then
`assert keyword == "unsafe"`). It proves nothing about baremetal syntax.
**Running is not the same as testing — do not treat this file as coverage.**
Rewrite is a separate task.

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

## Traps for future lanes

**A `fn main` in a spec file silences every module-level example.** See OPEN 3.
Fixed for the `run` path, but the shape generalises: any execution path that
dispatches on "does this module have a `main`" will drop module-level
statements. When adding one, check for module-level BDD blocks first.

`bin/simple test <spec>` does NOT execute the spec in the invoked binary. It
spawns `src/compiler_rust/target/debug/simple test --no-session-daemon ...`,
which in turn spawns `src/compiler_rust/target/debug/simple run <spec>`. A
freshly built binary invoked as `simple test` therefore measures the OLD
debug binary in the shared working copy and shows no change at all — this
lane hit exactly that and briefly concluded the fix had no effect. Use
`<your-binary> run <spec>` to measure the binary you actually built.


## Re-measurement 2026-08-17 (P0-core silent-wrong lane): seed engines both FIRE

```
fn main():
    assert 1 == 2
    print "assert-did-not-fire"
```

| engine | result |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `error: semantic: assertion failed: condition evaluated to false` |
| `SIMPLE_EXECUTION_MODE=jit` | `Assertion violation in function 'main': contract condition failed` |

Neither engine reached the `print`, so bare `assert` is not vacuous on either
Rust-seed engine. This is consistent with the doc's own record that the
interpreter case was fixed in `7d73d4dd3a6e`, and extends it to the JIT, which
the doc did not state.

**This does NOT close "OPEN 1".** That item is about the PURE-SIMPLE compiler
discarding bare `assert`, and the pure-Simple compiler could not be exercised
here at all: no self-hosted binary is deployed in this tree (`bin/simple` is
the 2026-08-16 Rust seed, and `bootstrap/stage3/simple` has no `run`/`test`
subcommand). The remaining open item is untouched and unverified.
