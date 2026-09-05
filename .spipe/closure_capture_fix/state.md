# Lane CAPFIX2 — closure selective-capture fix

- **Status:** DONE (not committed — lane is under a no-commit instruction)
- **Bug:** `doc/08_tracking/bug/closure_selective_capture_skips_non_expression_statements_2026-07-27.md`
- **Binary under test:** `build/capfix/simple_capfix`
  (copy of `src/compiler_rust/target/release/simple`, built 2026-07-27 23:06 from the edited
  sources at 23:01/23:02). `bin/simple` and `bin/release/**` were **not** touched.
- **Out-of-tree backup of the edits:** `/tmp/capfix_backup/`
  (`interp_control.rs`, `hir_control.rs`, `closure_capture_statements_spec.spl`)

## Change

Both closure free-variable walkers were rewritten from "collect every `Identifier`, descending
only into `Node::Expression` statements" into proper **scope-aware** walkers.

| file | entry point |
|---|---|
| `src/compiler_rust/compiler/src/interpreter/expr/control.rs` | `collect_free_vars` |
| `src/compiler_rust/compiler/src/hir/lower/expr/control.rs` | `collect_used_identifiers` |

New shape in each (names differ per file: `collect_free_vars_*` vs `collect_identifiers_*`):

- `*_block(stmts, bound, out)` — walks a statement list as a lexical scope, `bound.truncate(mark)`
  at the end.
- `*_stmt(node, bound, out)` — handles `Expression, Let, Const, Static, Assignment, Return, If,
  Match, For, While, Loop, Break, Defer, ErrDefer, Guard, Assert, Assume, Admit, Calc, Context,
  With, Function`; type/module declarations contribute no reads.
- `bind_pattern_*(pattern, bound, out)` — registers binders from
  `Identifier/MutIdentifier/MoveIdentifier/Tuple/Array/Or/Struct/Enum/Typed`, and *reads* the
  sub-expressions of `Literal`/`Range` patterns.
- `*_arms(arms, ...)` — match arms now bind their pattern, walk the guard, and walk the arm body
  as a full block (previously only `Node::Expression` statements in the arm body were walked).
- Expression walker gained the missing arms: `KernelLaunch, OptionalMethodCall, TupleIndex, Slice,
  LabeledTuple, ArrayRepeat, Dict, List/DictComprehension, Go, CastOrReturn, ContractOld, Await,
  Try, ForceUnwrap, ExistsCheck, UnwrapOrReturn, Spread, DictSpread, OptionalChain, UnwrapOr,
  CastOr, Coalesce, UnwrapElse, CastElse, Range, FunctionalUpdate, StructInit spread, Forall,
  Exists`, and lambda/`Go` params now shadow. The HIR twin additionally had **no
  `Expr::DoBlock` arm at all**, so a `fn(): <block>` body captured nothing.

## Shadowing model (deliberate, and the direction of error is deliberate)

- Binders are registered **sequentially**, *after* their initializer is walked — so `val x = x`
  correctly captures the outer `x` for its own initializer.
- Binders are dropped at the end of their block (`truncate`).
- The runtime actually *leaks* block-local binders into the enclosing scope (see below), so this
  static model is strictly **more conservative** than the runtime: it can over-capture, never
  under-capture. Over-capture is harmless (the filter is only an optimisation); under-capture is
  the correctness bug being fixed.

## Verification (all with `build/capfix/simple_capfix`, `--no-session-daemon`)

Truth table (`build/capfix/matrix_new.log` vs `matrix_base_binsimple.log`), both engines:

| fixture | pre-fix | post-fix |
|---|---|---|
| `h_matrix` H1–H10 (jit) | 5 passed, 5 failed | **10 passed, 0 failed** |
| `h_matrix` H1–H10 (interp) | 5 passed, 5 failed | **10 passed, 0 failed** |
| `h2_same_it` P1/P3/P4/P5 (jit) | 3 passed, 2 failed | **5 passed, 0 failed** |
| `h2_same_it` P1/P3/P4/P5 (interp) | 3 passed, 2 failed | **5 passed, 0 failed** |
| `k2_plain` (jit) | `KA=0 KB=0 KC=1 KD=0 KE=0 KF=0` | **`KA=10 KB=10 KC=11 KD=10 KE=10 KF=10`** |
| `k2_plain` (interp) | `KA=10` then hard error | **all six correct** |

Regression spread (`build/capfix/spread_new.log`): `duplicate_owner` 7/0, `ecs` 16/0,
`ds_service` 19/0, `container_escape_suite` 32/0, `two_hop_field_method_mutation` **5/0**,
`closure_capture_statements` 30/0.

New spec `test/01_unit/compiler/closure_capture_statements_spec.spl`: 30 examples across three
describes (every statement kind; shadowing; the non-sspec plain-`fn()` silent-zero cases).
**22 of the 30 fail on the pre-fix binary** (`build/capfix/newspec_base.log`), 0 after.

### `cargo test --release -p simple-compiler --lib` — A/B, zero regressions

The main tree has **other lanes' uncommitted edits** in this same crate (`interpreter/place.rs`,
`codegen/common_backend.rs`, `node_exec.rs`, …), so HEAD is not the right comparator. A true
baseline was built out-of-tree at `/tmp/capfix_base` = the working tree with **only** the two
`control.rs` files reverted to HEAD.

| | passed | failed |
|---|---|---|
| baseline (`build/capfix/cargo_test_base.log`) | 3357 | 125 |
| with fix (`build/capfix/cargo_test.log`) | 3372 | **110** |

Set-diff of the failing test names: **new-only failures = ∅ (no regressions)**; 15 names fail at
baseline and pass with the fix. Treat that 15 with care — the `pipeline::native_project::*`
entries in it are plausibly artefacts of the `/tmp` sandbox (symlinked `src/compiler`, different
cwd), not real fixes. The load-bearing, sandbox-independent claim is the empty regression set.

The 110 remaining failures are pre-existing and belong to other lanes — e.g.
`value::tests::test_value_matches_type_float` (`Value::Float(3.15).matches_type("f32")`),
`codegen::runtime_sffi::tests::all_funcs_have_unique_names` (static table, 1132 vs 1133),
`codegen::common_backend::tests::referenced_empty_extern_is_declared` (panics in
`mir_inline.rs:237`) — none reachable from a free-variable walker.

### Over-capture smoke — 15 unrelated specs, byte-identical

`build/capfix/smoke_base.log` vs `smoke_new.log` (script `build/capfix/run_smoke.shs`, sample
`build/capfix/smoke_list.txt`): all 15 `Results:` lines identical between the pre-change and
post-change binaries. 14 fully green; `app/llm_caret/.spipe_matchers_claude_api_spec.spl` is
16/2 on **both** (live-API spec, pre-existing).

Over-capture is provably harmless at the call site: the filter is
`env.iter().filter(|(k, _)| used.contains(k))`, so a name in `used` that is absent from `env` is
simply never copied.

## Separate finding — NOT this defect, do not conflate

Block-local binders leak past their block, identically on the **pre-fix** binary and outside any
closure: `build/capfix/scope_probe.spl` prints `IF_LEAK=55 FOR_LEAK=7` on both binaries in a plain
`fn`. Two draft assertions that pinned non-leakage were therefore reframed to assert what the
language actually does (shadowing wins *inside* the block); the leak itself is deliberately not
pinned. Recorded in the bug doc's "Remaining".

## Not done

- The pure-Simple `src/compiler` tree was **not** inspected or changed (out of lane scope; other
  lanes were live there). The same hole may exist there.
- Nothing committed or pushed.
