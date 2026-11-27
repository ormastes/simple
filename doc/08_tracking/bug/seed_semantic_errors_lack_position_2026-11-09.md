# Seed reports semantic errors with no file:line:col

- **Priority**: P3
- **Duplicate (2026-11-09)**: closed as resolved-duplicate; tracked by `seed_semantic_error_missing_position_2026-11-09` (kept).
- **Status**: open
- **Split out**: 2026-11-09, by owner decision, from `seed_optional_query_comparison_divergence_2026-08-16.md` (was Divergence C there).

## Divergence C — Seed reports semantic errors with no position information

Both divergences A and B presented as runtime mysteries (nil pointer dereference, type mismatch with no source location) because the seed's semantic error reporting omits file and line number information.

Error format under seed:
```
error: semantic: <error message only>
```

Error format under self-hosted:
```
<file>:<line>:<col>: error: semantic: <error message>
```

This lack of context makes seed-vs-self-hosted discrepancies hard to localize. A semantic error can be traced only by runtime behavior (where it manifests), not by its origin.

**Diagnosability gap:** The seed should report error position on all semantic failures.

**Status:** Open; no immediate fix planned. Workaround: use the self-hosted compiler for debugging semantic errors, not the seed.


## 2026-11-09 — FIXED on work/p3-subj4-seed-20261109

(Tracked canonically by `seed_semantic_error_missing_position_2026-11-09`,
which has no DB row; this duplicate row records the same fix.)

The seed now reports semantic errors raised during interpreted evaluation
with the enclosing statement's position:

```
error: semantic: sem_err.spl:2:5: variable `nope_undefined` not found
error: semantic: sem_err2.spl:2:5: variable `missing_name` not found   (inside a function body)
```

Mechanism: each interpreter statement-execution loop head (module-level
both passes, the two `block_execution` loops, and `interpreter/block_exec`'s
`exec_block`/`exec_block_fn`) records the current node's span in a
thread-local; `CompileError::semantic_with_context` adopts that span plus
the current file when the raise site recorded no position; `Display`
renders `semantic: <file>:<line>:<col>: <message>`. Cargo pin:
`src/compiler_rust/compiler/tests/semantic_error_position.rs` (2 tests).
Limitation: `Expr` carries no span, so position is statement-granularity,
and plain (non-contextual) `CompileError::Semantic` sites are untouched.
Verified on a fresh cargo build of release/1.0.0 source.
