# BUG: `use std.spec.*` does not import `expect_not` — only the explicit form does

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** medium — the documented boolean-assertion shortcut is unreachable
through the import form the specs actually use, and the repo's own lint rules
tell authors to write `expect_not(...)`.
**Files:**
- `src/lib/nogc_sync_mut/spec.spl:533` — `pub fn expect_not(value: bool) -> ExpectHelper`
- `src/lib/nogc_async_mut/spec.spl:1,39` — `export use std.nogc_sync_mut.spec.{... expect_not ...}`
- failing spec: `test/01_unit/std/spec_expect_bool_shortcut_spec.spl`

## Symptom

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/std/spec_expect_bool_shortcut_spec.spl
  ✗ accepts expect_not for false boolean expressions
    semantic: function `expect_not` not found
Results: 3 total, 2 passed, 1 failed
```

The same symbol resolves fine when imported by name. Four probes, same binary,
same runner:

| probe | import | result |
|-------|--------|--------|
| `/tmp/probe_en_spec.spl` | `use std.nogc_sync_mut.spec.{describe, it, expect_not, assert_true}` | **1 passed** |
| `/tmp/probe_star_spec.spl` | `use std.spec.*` | `expect_not` not found |
| `/tmp/probe_star2_spec.spl` | `use std.nogc_sync_mut.spec.*` | `expect_not` not found |
| `/tmp/probe_star3_spec.spl` | `use std.nogc_async_mut.spec.*` | `expect_not` not found |

Probe 3 matters: `src/lib/nogc_async_mut/spec.spl` line 1 is an explicit
`export use std.nogc_sync_mut.spec.{...}` block that names `expect_not` at line
39, and the star import *still* does not pick it up.

Star import is not broken in general — a local module works:

```
# /tmp/starmod/mymod.spl
pub fn my_star_fn(x: i64) -> i64:
    x + 1
export my_star_fn

# /tmp/starmod/probe_star4_spec.spl
use mymod.*
... expect(my_star_fn(1)).to_equal(2)   ->  1 passed
```

## Root cause

Not fully pinned — and one plausible-looking cause was **tested and refuted**,
so it is recorded here to stop the next person repeating it.

What is established:

1. `expect_not` exists only as a `.spl` symbol. `grep -rn expect_not
   --include=*.rs src/compiler_rust/` returns only lint *message strings* — there
   is no `expect_not` runtime intrinsic, unlike `describe` / `it` / `expect` /
   `assert_true` / `check_msg`, which are intrinsics (see
   `.claude/memory/reference_spec_dsl_is_rust_intrinsics_spl_speclib_unreachable.md`).
2. Therefore every DSL name that *appears* to arrive via `use std.spec.*` is in
   fact being satisfied by an intrinsic of the same name. `expect_not` is the
   one name with no intrinsic, which is precisely why it is the one that fails.
   The star import is plausibly contributing **nothing** in these specs.
3. **Refuted hypothesis:** that `src/lib/nogc_sync_mut/spec.spl` fails to
   star-export because it has no `export` statement (it has none — the file ends
   at line 845 on a dangling comment, `# Internal helper export (used by
   skip_it, skip_on_interpreter, only_on_interpreter)`, with the list it
   introduces missing). An explicit 25-line `export` list naming all 53 public
   symbols was added and the probes re-run: **still `expect_not` not found**.
   The change was reverted as unproven. So the missing export list is a real
   wart but is *not* the gate here.

The remaining suspect is the resolution path for `std.*` modules under the
runner specifically — note the runner delegates spec execution to the Rust seed
child (`WARNING: this Rust-built Simple binary is a bootstrap seed only` appears
in every spec run), so the stdlib view the spec compiles against may not be the
`src/lib` tree on disk. That needs confirming before anyone edits further.

## Why not fixed now

The fix depends on which of the two remaining explanations holds, and telling
them apart needs a lane that can rebuild/bootstrap and re-measure:

- If the seed compiles specs against a baked-in stdlib, no `src/lib` edit can
  fix this and the answer is to stop delegating (or to rebuild the seed) —
  neither is a test-repair change.
- If star import genuinely drops re-exported symbols for `std.*` paths, the fix
  is in module resolution and needs its own before/after across the whole suite,
  since it would change what every `use std.X.*` in the repo brings into scope.

Separately, `src/lib/nogc_sync_mut/spec.spl` should get its missing `export`
list on general principle (all three sibling tiers have one) — but land that
with a test that actually observes it, not as a speculative fix for this bug.
