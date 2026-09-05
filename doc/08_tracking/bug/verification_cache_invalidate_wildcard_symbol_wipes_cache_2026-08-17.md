# `VerificationCache.invalidate_dependents` treats the `"*"` file-level wildcard as a symbol key, wiping the whole cache

- **Filed:** 2026-08-17
- **Status:** FIXED 2026-08-17
- **Severity:** high (silent correctness/perf loss — one changed module evicts every file-level proof unit)
- **Component:** `src/compiler_rust/lib/std/src/verification/cache.spl:168-197`
- **Found by:** crash-isolated sweep of `test/00_formal_verification/`

## Symptom

`test/00_formal_verification/compiler/cache_correctness_spec.spl` — 22 examples,
21 passed, 1 failed:

```
invalidate_dependents
  ✗ removes cached entries for units depending on changed module
    expected subject to be truthy, got nil
```

The three sibling examples in the same `context` (transitive dependents,
dependent cycles, field-wrapper semantic dependents) all PASS. The failing one
is the only example that asserts the **negative** direction — that a unit which
does *not* depend on the changed module survives invalidation.

## Root cause

`ProofUnit.source_symbol` is documented at `proof_unit.spl:14` as:

```
source_symbol: text              # Primary symbol (fn/class name, or "*" for file-level)
```

`invalidate_dependents` grows its transitive frontier by seeding the invalidated
unit's `source_file`, `lean_module` **and `source_symbol`** into `changed_keys`
(line 195-196), and matches later units against that same set (line 182).

For a file-level unit `source_symbol` is the literal `"*"` — a wildcard shared
by *every* file-level unit, not a symbol name. So:

1. `changed_keys = ["base_defs"]`.
2. `unit_b` matches (its `dependencies` contain `base_defs`) and is evicted.
   `changed_keys` now gains `"b.spl"`, `"Verification.B"`, **and `"*"`**.
3. The `while progressed` loop runs again. `unit_a` — which depends on nothing —
   now matches at line 182 on its own `source_symbol == "*"` and is evicted.

With N file-level units, invalidating any single genuine dependent cascades to
all N. The cache is not merely "conservative"; it is fully wiped on every
change, which is why the cache appears to work in every test that only asserts
that dependents *are* removed.

## Fix

Exclude the literal `"*"` from both the match and the seeding, leaving named
symbols working exactly as before:

```
if unit.source_symbol.len() > 0 and unit.source_symbol != "*" and changed_keys.contains(unit.source_symbol):
...
if unit.source_symbol.len() > 0 and unit.source_symbol != "*" and not changed_keys.contains(unit.source_symbol):
```

## Specs

- **Repro + generalization:**
  `test/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.spl`
  - repro: the exact two-unit shape from the failing example.
  - generalization: five file-level units where only one depends on the changed
    module (the blast radius grows with N, so two units under-tests it); a bare
    `invalidate_dependents("*", ...)` which must not be read as "everything
    file-level"; and a **named** symbol which must still propagate transitively,
    so the fix cannot have traded over-invalidation for under-invalidation.
- The pre-existing example in `cache_correctness_spec.spl` (lines 79-103) is the
  in-situ regression guard and returns to green.

## Repro

```
SIMPLE_TIMEOUT_SECONDS=600 bin/simple test test/00_formal_verification/compiler/cache_correctness_spec.spl
SIMPLE_TIMEOUT_SECONDS=600 bin/simple test test/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.spl
```
