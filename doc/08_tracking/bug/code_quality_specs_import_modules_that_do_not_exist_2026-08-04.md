# `test/system/code_quality` specs import three modules/types that exist nowhere in the tree

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Found:** 2026-08-04

## Symptom

Three specs under `test/system/code_quality/` fail before any example runs, or
fail every example, because of unresolvable imports. Measured with:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
  test/system/code_quality > /tmp/sys.log 2>&1
```

```
# deprecated_removed_spec.spl
error: runtime: Module "std.common" does not export 'set_utils'
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed

# iter_deprecated_spec.spl  (use std.common.iterable.{each, each_with_index})
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed

# allow_suppressions_spec.spl
✗ AC-2: Set operations compile with explicit imports (no star_import suppression)
    semantic: variable `Set` not found
Results: 4 total, 3 passed, 1 failed
```

Expected: the specs' replacement-API examples run.
Actual: 3 examples red, 2 of the files are dead entry points.

## Root cause

Three separate missing pieces, all verified by exhaustive grep over `src/`:

1. **`std.common.set_utils` does not exist.** The module is present only in the
   seed's std tree, under a different package:
   `src/compiler_rust/lib/std/src/tooling/set_utils.spl`, i.e. reachable as
   `std.tooling.set_utils`. Verified working:

   ```
   use std.tooling.set_utils.{set_intersection}
   fn main():
       print set_intersection([1, 2, 3], [2, 3, 4]).len()   # -> 2
   ```

   Repointing the import is not sufficient on its own — see (3) — and one of
   the three imported names is wrong regardless: the module declares
   `symmetric_difference` (`set_utils.spl:65`), not `set_symmetric_difference`.

2. **`std.common.iterable` does not exist at all.** The nearest thing in the
   tree is `src/compiler_rust/lib/std/src/core/iterable_defaults.spl`, which
   does not carry `each` / `each_with_index` under that path. `src/lib/text.spl:11`
   has an `each_with_index` for `text` only, which is not what
   `iter_deprecated_spec.spl` imports.

3. **There is no `Set` type anywhere in `src/`.** `grep -rn '^class Set:|^struct Set:'`
   over the whole tree returns nothing, yet both `deprecated_removed_spec.spl`
   (line 88, `var b = Set.new()`) and `allow_suppressions_spec.spl` construct
   one. `src/lib/*/src/collections/hashset.spl` exists in four tiers but
   declares `HashSet`, not `Set`, and is not what these specs import.

So `deprecated_removed_spec.spl` needs both (1) and (3) before it can go green;
`iter_deprecated_spec.spl` needs (2); `allow_suppressions_spec.spl` needs (3).

## Why not fixed now

(1) is a one-line repoint, but landing it alone just moves
`deprecated_removed_spec.spl` from "no examples executed" to red on
`Set.new()`, so it buys nothing until (3) exists. (2) and (3) are unwritten
library surface — authoring a `Set` collection and a `std.common.iterable`
module is feature work owned by whoever owns `src/lib/common/`, not a
test-repair change. Recorded per the standing rule that a spec importing a
module that was never written is a missing feature, not a defect.

Note the same root shape was *fixable* one file over and has been fixed:
`primitive_api_types_spec.spl` imported the wrapper types via the package root
`use std.common.{ActorId, ...}`, but `src/lib/common/` has no `__init__.spl`,
so nothing resolved and all 18 examples died with `function ActorId not found`.
Those types do exist (`src/lib/common/types.spl`), so repointing to
`use std.common.types.{...}` took that spec from 0/18 to 18/18. The missing
`src/lib/common/__init__.spl` is worth filing separately if package-root
imports of `std.common` are meant to work — 193 entries live in that directory
and none of them are reachable that way today.

## Re-verified 2026-08-10

Static re-check confirms nothing has changed:

```
/usr/bin/grep -rn '^class Set' src/                          # -> no matches (Settings/SettlementBuilder only, unrelated)
/usr/bin/grep -rn 'std.common.iterable' src/                  # -> no real matches (only build-artifact false hits)
ls src/lib/common/__init__.spl                                 # -> No such file or directory
find src -iname 'set_utils.spl'                                 # -> src/compiler_rust/lib/std/src/tooling/set_utils.spl (only)
```

Fresh execution of the one spec whose failure mode doesn't require a full
20-minute suite run:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
  test/system/code_quality/allow_suppressions_spec.spl
...
✗ AC-2: Set operations compile with explicit imports (no star_import suppression)
Results: 4 total, 3 passed, 1 failed
```

Same `variable `Set` not found` failure as originally recorded. Status
confirmed **ARCHITECTURAL-OPEN**: (2) `std.common.iterable` and (3) a `Set`
collection type are still unwritten library surface (feature work owned by
whoever owns `src/lib/common/`), not a test-repair fix. No code change
lands with this re-verification.

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN. `ls src/lib/common/iterable.spl src/lib/common/set_utils.spl` ->
both "No such file or directory". `test/system/code_quality/deprecated_removed_spec.spl`
is still present and still imports them. The specs remain unloadable.
