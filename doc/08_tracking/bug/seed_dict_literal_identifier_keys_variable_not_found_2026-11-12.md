# Seed: dict literal with bare identifier keys — `variable 'name' not found` (2026-11-12)

- **Status:** RESOLVED — NOT A SEED DEFECT. Bare identifier dict keys are
  **variable reads by language contract**; the failing specs were shorthand
  drift and are quoted now. An interpreter "fix" was attempted and **reverted**
  after review (PR #8434).
- **Severity:** P2 (spec-lane blocker; affected specs using `{ ident: value }`
  where the intent was a literal string key)
- **Found:** 2026-11-12, release/1.0.0 Windows seed lane
- **Area:** language contract for dict-literal keys (all engines), seed
  interpreter evaluation (`compiler/src/interpreter/expr/collections.rs`)

## Symptom

Dict literals whose keys are bare identifiers fail under the seed
interpreter with:

```
semantic: <file>:<line>:<col>: variable `name` not found
```

First observed in `test/02_integration/app/app_mcp_intensive_spec.spl:166`
(`val config = { name: "simple-mcp-server", ... }`); the probe showed the
shape is any dict entry with a bare identifier key (single or multi key).

## Root cause — shorthand drift in the specs, not an interpreter bug

A dict-literal key is a full expression in every engine:

- seed interpreter: `Expr::Dict` evaluates keys via `evaluate_expr`
  (`compiler/src/interpreter/expr/collections.rs`);
- seed HIR lowering: `lower_dict` lowers keys via `lower_expr`
  (`compiler/src/hir/lower/expr/collections.rs:707`);
- self-hosted frontend: `lower_dict_entry`
  (`src/compiler/20.hir/hir_lowering/_Expressions/expression_components.spl:90`).

So a bare identifier key is a **variable read**, and an unbound identifier
correctly errors. Product code depends on the bound-name behavior, e.g.
`src/app/spipe/fusion/rrf.spl:105` `{skey: candidate.source_rank}` where
`skey` is a bound variable (indexed as `[skey]` on lines 92/101). The
documented syntax (`doc/syntax_quick_reference.md:317`) shows quoted keys
only.

## What happened in this lane (review record)

1. First attempt treated identifier keys as literal string keys in the seed
   interpreter only. That made the interpreter silently diverge from every
   compiled path (P1, review on PR #8434) and was **reverted**.
2. Correct disposition: quote the identifier keys at the spec sites that
   used the shorthand. `test/02_integration/app/app_mcp_intensive_spec.spl`
   had 10 such dict literals (lines 166, 181, 208, 261, 302, 333, 379, 407,
   457, 557); all keys are now quoted. Sites that legitimately key dicts by
   bound variables were left alone: `test/01_unit/compiler/codegen/
   cuda_backend_intensive_contract_spec.spl` (`Dict<SymbolId, ...>` keyed by
   `struct_symbol`/`symbol` vals) and `test/01_unit/compiler/loader/
   module_loader_spec.spl:305` (keyed by `owned_symbol_name` vals).

## Regression fixture

`test/01_unit/compiler/interpreter/dict_literal_identifier_key_variable_read_spec.spl`
pins the contract for every engine: bound-identifier keys key by value,
quoted keys stay literal.

## Verification (post-revert seed, PR #8434)

- New contract spec: 3/3 examples pass under the seed interpreter.
- `test/02_integration/app/app_mcp_intensive_spec.spl`: all 10
  `variable \`...\` not found` failures eliminated (quoted keys); remaining
  failures are the known skip-class contexts named in the lane brief.
