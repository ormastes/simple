# Seed binds a call to the wrong same-named function (2026-11-27)

Status: verification-pending (fix in the seed + pure-Simple interpreter; see Fix). Found while wiring the phase-3 Hello matrix twin to the
BuildRunner lane twin (PR #12220). Reproduced on the Rust seed
`C:/dev/wt/bound3x-target/release/simple.exe` (sha256
`9c509c621f2cc69fbeb1e4c5df8db6b2e0620ea3c9f6ef9cfc4ef671e37c117f`), Windows.
Both forms run silently: no error, wrong body or nil.

## Form 1 - explicit import loses to a local definition of another arity

`build/repro/rp/alpha.spl`:

```simple
pub fn same_name(a: text, b: text) -> text:
    "alpha:" + a + b
```

`build/repro/rp/beta.spl`:

```simple
use build.repro.rp.alpha.{same_name}
pub fn same_name(n: i64) -> text:
    "beta:{n}"
pub fn call_alpha() -> text:
    same_name("x", "y")
```

`build/repro/main1.spl`:

```simple
use build.repro.rp.beta.{same_name, call_alpha}
fn main():
    print(same_name(7))
    print(call_alpha())
```

`simple run build/repro/main1.spl` prints `beta:7` then `beta:4804457911617`:
the two-`text` call is bound to the local `(i64)` body and runs with a text
handle reinterpreted as an integer. Expected: `alpha:xy` (the explicitly
imported, arg-type-matching definition) or a compile error. The only signal is
the generic `compiler_cross_module_private_symbol_collision` warning, which
claims call sites "resolve by the caller's import path, else by exact arg-type
match" — neither happened.

## Form 2 - a local helper named `context` evaluates to nil in a spec

```simple
use std.spec
struct Box:
    v: i64
fn context(v: i64) -> Box:
    Box(v: v)
describe "local fn named context":
    it "returns the struct":
        val b = context(5)
        expect(b.v).to_equal(5)
```

`simple test <file>` fails with `undefined field 'v': cannot access field on
value of type 'nil'`. The same helper in a plain `simple run` program prints
`v=5`, so the call is bound to the spec DSL's `context` instead of the
module-local function, and the type mismatch is not reported.

## Expected

A module-local or explicitly imported function must win over any other
same-named symbol; when the chosen definition does not accept the argument
types, compilation must fail. Never a silent nil or reinterpreted argument.

## Workaround in tree

PR #12220 renamed its entry to `matrix_buildrunner_run_lane` and the spec helper
to `spec_matrix_ctx`; both are tagged here so they can be reverted once fixed.

## Fix (2026-11-28, verification-pending)

Root cause, form 1: HIR `flatten_owned_callable` rule 1 returned the calling
module's own definition by name alone, before its selective import was even
consulted, so the JIT/native lanes ran `beta`'s `(i64)` body. The Rust
interpreter was already right (it scores overloads by value). Root cause,
form 2: the interpreter's spec-DSL arm (`eval_bdd_builtin`) ran before user
lookup for every DSL word, including a spec file's own `fn context`.

Rule now, on every engine: when a module declares `f` AND selectively imports
another `f`, both are visible and the call's arguments choose (arity, then
argument type; an exact match outranks an untyped slot). Identical signatures
keep the own-definition tie-break. Two different signatures that fit equally
well are a compile error tagged `[compiler_cross_module_private_symbol_collision]`.
A DSL word the calling module declares itself is that module's function.

- Seed HIR: `select_flatten_call_candidate` (`hir/lower/expr/calls.rs`),
  `flatten_call_site_candidates` (`hir/lower/lowerer.rs`); DSL statement gate
  in `try_lower_bdd_statement` (`stmt_lowering.rs`).
- Seed interpreter: `own_vs_import_bound` and the `BDD_DSL_NAMES` caller gate
  (`interpreter_call/{mod,bdd}.rs`).
- Pure Simple: `func_resolve_for_call` (`eval_tables.spl`, arity only; a
  same-arity, different-signature pair is an error rather than type-ranked).
- Tests: `src/compiler_rust/compiler/tests/same_name_fn_binding.rs`,
  `test/01_unit/compiler/pipeline/same_name_fn_binding_spec.spl`,
  `test/01_unit/compiler/pipeline/local_fn_shadows_spec_dsl_spec.spl`.

**The two renames from PR #12220 (`matrix_buildrunner_run_lane`,
`spec_matrix_ctx`) can be reverted once the seed carrying this fix is
redeployed.** Until then the deployed seed still has the bug.
