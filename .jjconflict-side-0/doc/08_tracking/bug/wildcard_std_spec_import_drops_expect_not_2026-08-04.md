# `use std.spec.*` silently drops `expect_not` — the matcher the linter tells you to use

**Status:** OPEN — architectural (needs either a Rust-seed `bdd.rs` intrinsic-table
change + bootstrap rebuild, or module-resolver wildcard-export-expansion work
with tree-wide blast radius; re-confirmed 2026-08-10)
**Found:** 2026-08-04
**Severity:** high — `checker_spipe.rs` emits `expect_not(condition)` as a
recommended *auto-fix*, so following the linter's advice in a file that imports
`std.spec` by wildcard turns a passing spec red

## Symptom

Identical call, two import styles, opposite outcomes.

**Fails** — `test/01_unit/lib/nogc_sync_mut/spec_bool_expect_spec.spl`:

```
use std.spec.*

describe "boolean expect helpers":
    it "accepts bare negative boolean expectations":
        expect_not(false)
```

```sh
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
    test/01_unit/lib/nogc_sync_mut/spec_bool_expect_spec.spl
  FAIL  … spec_bool_expect_spec.spl (2 passed, 1 failed)
        Error: semantic: function `expect_not` not found
```

**Passes** — `test/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.spl`:

```
use std.spec.{describe, it, expect, expect_not, assert_not_equal}
```

```sh
Results: 2 total, 2 passed, 0 failed
```

Note which assertions survive in the failing file: the two that pass use
`assert_true` and `expect`, and the one that fails uses `expect_not`.

## Root cause

`expect_not` is defined, and re-exported, everywhere it should be:

- `src/lib/nogc_sync_mut/spec.spl:533` — `pub fn expect_not(value: bool) -> ExpectHelper`
- `src/lib/nogc_async_mut/spec.spl:39` and `src/lib/gc_async_mut/spec.spl:39` —
  named in the explicit `export use std.nogc_sync_mut.spec.{…}` lists
- `src/lib/gc_sync_mut/spec.spl:3` — `export use std.gc_async_mut.spec.*`

So the declaration is not the problem; the *wildcard* is. The names that keep
working under `use std.spec.*` are exactly the ones the interpreter also
provides as spec-DSL intrinsics in
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs` — `expect` (line 800),
`assert_true` (1484), `assert_false` (1503), `assert_nil`, `assert_not_nil`,
`assert_contains`, `be_true`, `be_false`, `eq`, `be_close_to`. That table has
**no `expect_not` entry**. Every name that survives the wildcard has an
intrinsic behind it; the one that does not survive is the one that would have
had to come from the `.spl` module.

That is the actual defect: under `use std.spec.*` the pure-Simple `pub fn`s in
`spec.spl` are not reachable at all, and the wildcard's apparent success is an
artifact of the intrinsic table shadowing it. An explicit named import resolves
the `.spl` function correctly, which is why the second file above passes.

`src/lib/gc_sync_mut/spec.spl` compounds it: it is a wildcard re-export *of* an
explicit re-export list, so any name-dropping in the wildcard path applies
twice.

## Blast radius

```sh
$ grep -rl 'expect_not(' test --include='*_spec.spl' | wc -l
45
$ grep -rho 'expect_not(' test --include='*_spec.spl' | wc -l
319
```

319 call sites in 45 spec files; 12 of those files are under
`test/01_unit/lib/`. Each one is fine or broken purely according to whether its
`use std.spec` line happens to be explicit or wildcard.

The linter makes this worse rather than better. `checker_spipe.rs:826` reports
"false boolean matcher wrapper in spec/example; use `expect_not(condition)`
instead of `.to_equal(false)` or `.to_be(false)`", and line 564 builds the
replacement text `format!("expect_not({})", subject)`. Applying that suggested
fix to any wildcard-importing spec converts a green `.to_equal(false)` into a
hard `function not found`.

## Why not fixed now

Two candidate fixes, both outside what this session can land safely:

1. **Add `expect_not` to the `bdd.rs` intrinsic table.** Smallest change, makes
   the wildcard work by giving it the same shadow every other spec name has —
   but it is a Rust seed change requiring a bootstrap rebuild, and it treats
   the symptom: the next pure-Simple spec helper added to `spec.spl` breaks the
   same way.
2. **Fix wildcard export expansion so `use std.spec.*` delivers the module's
   `pub fn`s.** The correct fix, but it is module-resolver work whose blast
   radius is every `export use …*` in the tree, and this session has no way to
   regression-test that.

Until one lands, the linter's `expect_not` suggestion should not be offered as
an auto-fix — a rule that reddens correct code is worse than no rule.

## Re-verification (2026-08-10)

Confirmed both halves of the root cause are unchanged:
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs` still has no
`"expect_not"` entry in the intrinsic table, and `expect_not` is still a plain
pure-Simple `pub fn` (now at `src/lib/nogc_sync_mut/spec.spl:657`, moved from
:533 by unrelated edits but otherwise identical). Both candidate fixes remain
out of scope for a docs/measurement-lane pass: the intrinsic-table fix needs a
Rust-seed edit + bootstrap rebuild (both off-limits here), and the
wildcard-export-expansion fix touches every `export use …*` in the tree with
no regression harness available in this pass.

## Related

- `.claude/memory` — "lint SPIPE007's 'safe' auto-fix reddens code" is the same
  failure mode in a different rule.
- "Spec DSL = Rust intrinsics in bdd.rs, .spl spec-libs unreachable on seed" —
  this bug is the first case where that architecture is externally visible as a
  spec failure rather than as dead code.
