# Bug: `VerificationCache.invalidate_dependents` treats the file-level `"*"` symbol sentinel as a trackable dependency key, causing false-positive invalidation of unrelated proof units

- **Date:** 2026-07-20
- **Status:** open
- **Area:** `src/compiler_rust/lib/std/src/verification/cache.spl` (`VerificationCache.invalidate_dependents`), tested via `test/00_formal_verification/compiler/cache_correctness_spec.spl`
- **Binary:** reproduced on `bin/release/x86_64-unknown-linux-gnu/simple`, which currently prints the Rust-seed bootstrap warning (`WARNING: this Rust-built Simple binary is a bootstrap seed only`) — this is pure-`.spl` logic, not seed-interpreter-specific, but has not been independently re-verified on a genuinely self-hosted binary.

## Symptom

`cache_correctness_spec.spl`, example "removes cached entries for units depending on changed module", fails:

```
expected nil cache entry to equal preserved cache entry
```

`cache.lookup("a.spl", fp_a)` returns `nil` after `cache.invalidate_dependents("base_defs", [unit_a, unit_b])`, even though `unit_a` (`a.spl`) has no dependency on `"base_defs"` and only `unit_b` (`b.spl`) does.

## Root cause

`ProofUnit.source_symbol` uses the literal string `"*"` as a sentinel meaning "file-level unit, no specific symbol" (see `proof_unit.spl:13`: `source_symbol: text # Primary symbol (fn/class name, or "*" for file-level)`).

`invalidate_dependents` (cache.spl:168-197) folds `unit.source_symbol` into the `changed_keys` propagation set whenever a unit is invalidated:

```simple
if unit.source_symbol.len() > 0 and not changed_keys.contains(unit.source_symbol):
    changed_keys = changed_keys + [unit.source_symbol]
```

When `unit_b` (dependent on `"base_defs"`) is invalidated, its `source_symbol` — the sentinel `"*"` — is added to `changed_keys`. On the next fixed-point iteration, ANY other proof unit whose `source_symbol` is also `"*"` (i.e. any other file-level unit, which in v1 is every unit per `proof_unit.spl`'s own doc comment: "Proof units are file-level for v1") matches:

```simple
if unit.source_symbol.len() > 0 and changed_keys.contains(unit.source_symbol):
    depends_on_changed = true
```

`unit_a`'s `source_symbol` is also `"*"`, so it gets spuriously invalidated even though it has zero actual dependency relationship to `base_defs` or `unit_b`.

## Trace (confirms via the failing test's fixtures)

```
unit_a = ProofUnit.create("a.spl", "*", "Verification.A", "a.lean")   # dependencies=[]
unit_b = ProofUnit.create("b.spl", "*", "Verification.B", "b.lean").with_dependencies(["base_defs"])

invalidate_dependents("base_defs", [unit_a, unit_b]):
  pass 1: unit_a not invalidated (no match). unit_b invalidated (dependencies contains "base_defs").
          changed_keys += ["b.spl", "Verification.B", "*"]   <- the "*" is the bug
  pass 2: unit_a.source_symbol == "*" and changed_keys.contains("*") -> depends_on_changed = TRUE
          unit_a is spuriously invalidated
```

## Impact

Any project with more than one file-level (v1-default) proof unit will over-invalidate its verification cache whenever ANY single unit is invalidated for an unrelated reason — every other file-level unit's cache entry is dropped too, defeating the purpose of the cache (forces full re-verification far more often than necessary; the cache's own doc comment states "Invariant: cache MUST never preserve a false Verified result" — this bug doesn't violate soundness, but it does break precision/usefulness of the invalidation set).

## Suggested fix direction

Do not propagate the `"*"` sentinel into `changed_keys` (skip the `unit.source_symbol` addition when `source_symbol == "*"`), or track file-level dependents by `(source_file, source_symbol)` pairs rather than by bare symbol string so the wildcard can't collide across units.

## Repro

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/00_formal_verification/compiler/cache_correctness_spec.spl --no-session-daemon
```
Failing example: "Verification Cache > invalidate_dependents > removes cached entries for units depending on changed module".
