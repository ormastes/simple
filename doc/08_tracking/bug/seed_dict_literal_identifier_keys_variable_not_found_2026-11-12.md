# Seed (Windows): dict literal with bare identifier keys mis-evaluated as variables (2026-11-12)

- **Status:** FIXED — seed-side (`src/compiler_rust`), fix on `work/seed-bugs-20261112`
- **Severity:** P2 (spec-lane blocker; affects any spec using `{ ident: value }` dict entries)
- **Found:** 2026-11-12, release/1.0.0 Windows seed lane
- **Area:** seed interpreter dict-literal evaluation (`compiler/src/interpreter/expr/collections.rs`)

## Symptom

Every dict literal whose keys are bare identifiers fails under the seed
interpreter with:

```
semantic: <file>:<line>:<col>: variable `name` not found
```

First observed in `test/02_integration/app/app_mcp_intensive_spec.spl:166`
(`val config = { name: "simple-mcp-server", version: "0.5.0", ... }`), but a
minimal probe shows the shape that breaks is **any dict entry with a bare
identifier key** — single-key, multi-key, one-line and multi-line all fail
identically; string-literal keys (`{ "name": "x" }`) work.

Probe evidence (tmp/seed_probe/dict_probe_spec.spl under the lane worktree,
5 examples against the pre-fix seed):

| example | shape | pre-fix result |
|---------|-------|----------------|
| 1 | `{ name: "x" }` | FAIL `variable 'name' not found` |
| 2 | `{ name: "x", version: "y" }` | FAIL `variable 'name' not found` |
| 3 | multi-line multi-key | FAIL `variable 'name' not found` |
| 4 | `{ "name": "x", "version": "y" }` | PASS |
| 5 | multi-line single identifier key | FAIL `variable 'name' not found` |

The full spec: 35 executed, 14 passed, 21 failed; 10 of the failures carry the
`variable \`...\` not found` signature at the first identifier key of a dict
literal (lines 166, 181, 208, 261, 302, 333, 379, 407, 457, 557).

## Root cause

The seed parser keeps a bare identifier dict key as `Expr::Identifier(name)`
(`parser/src/expressions/primary/collections.rs`, `parse_dict_literal` parses
keys with `parse_expression()`), and the interpreter's dict-literal evaluation
evaluated that key through the generic identifier path, which resolves it as a
variable reference and dies with E1001 "variable not found"
(`compiler/src/interpreter/expr/literals.rs`).

The language contract (shared with the pure-Simple frontend and exercised by
checked-in specs that pass under the self-hosted compiler) is that a bare
identifier in dict-entry position is a **literal string key** — the Python/JS
`{ name: value }` shorthand — not a variable read. No currently-passing code
can depend on the old behavior because the old behavior was always a hard
error for unbound names.

## Fix

`compiler/src/interpreter/expr/collections.rs` (`Expr::Dict` evaluation arm):
when a key is `Expr::Identifier(name)`, insert the key as the literal string
`name` instead of evaluating it. All other key expressions (strings,
concatenations, parenthesized expressions, dict spreads) are unchanged, so
compiled-mode behavior and the AST are untouched; this is interpreter-only,
matching the "do not change compiled-mode behavior" constraint.

## Verification (post-fix seed, see commit message for exact commands)

- Minimal probe spec (all 5 shapes above): 5/5 PASS.
- `test/02_integration/app/app_mcp_intensive_spec.spl`: all 10
  `variable \`...\` not found` failures eliminated; remaining failures are in
  the known skip-class contexts the lane brief names (not pursued).

## Notes

- The lane brief titled this "multi-key dict literal misparse"; the probe
  narrowed it to *identifier-keyed* dict literals of any arity.
