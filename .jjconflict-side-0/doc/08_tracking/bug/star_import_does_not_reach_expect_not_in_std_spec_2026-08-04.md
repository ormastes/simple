# BUG: `use std.spec.*` does not import `expect_not` — only the explicit form does

## Status 2026-08-17: REPRODUCED, root cause located, NOT fixable inside src/lib

Reproduced under `SIMPLE_EXECUTION_MODE=interpreter`:

```
use std.spec.*
...  expect_not(false)
  x expect_not resolves via star import
    semantic: function `expect_not` not found
```

**Root cause:** `std.spec` names two different things. The brace form
`use std.spec.{expect_not}` resolves to the MODULE
`src/lib/nogc_sync_mut/spec.spl` (where `pub fn expect_not` is at line 710);
the star form `use std.spec.*` resolves to the PACKAGE directory
`src/lib/nogc_sync_mut/spec/` and therefore only ever sees
`spec/__init__.spl`'s export list.

**A src/lib-only fix was attempted and does NOT work** (recorded so it is not
retried): adding `use std.nogc_sync_mut.spec.{expect_not, before_all, after_all}`
plus `export expect_not, before_all, after_all` to
`src/lib/nogc_sync_mut/spec/__init__.spl` leaves the probe failing identically
(`function 'expect_not' not found`) -- the star form does not pick up that
re-export either. The change was reverted; `__init__.spl` is unmodified.

This is a compiler module-resolution defect (package shadows same-named module
under `*`), not a stdlib content gap. The same root cause was hit from the
other side while fixing
`spipe_before_all_after_all_not_found_t32_hw_2026-07-20.md`, where
`export use std.spec.*` had to be abandoned for an explicit name list.


**Status:** OPEN (re-verified 2026-08-10) — architectural, needs compiler
module-resolution work, not a source-level fix
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

## 2026-08-10 re-verification

Re-ran the doc's own repro on Linux (self-hosted-tooling not deployed here —
`bin/simple` resolves to the Rust seed
`bin/release/x86_64-unknown-linux-gnu/simple`, same "bootstrap seed only"
delegation the original report flagged):

```
$ SIMPLE_TIMEOUT_SECONDS=180 bin/simple test test/01_unit/std/spec_expect_bool_shortcut_spec.spl
    semantic: function `expect_not` not found
SPEC FILE VERDICT: ... declared>=3 executed=3 passed=2 failed=1 dropped=0
```

Identical to the original report (2 passed / 1 failed, same "function
`expect_not` not found" message). This confirms: (a) the bug is real and
reproducible on Linux, not Windows-specific; (b) it survives to the current
`main` unchanged.

`src/lib/nogc_sync_mut/spec.spl` still has **zero** `^export` lines (`grep -c
'^export' src/lib/nogc_sync_mut/spec.spl` → 0) — the missing-export-list wart
noted above is still present and still unfixed, and per the doc's own record
that fix was already tried and found NOT to resolve the star-import failure
(refuted, see above), so it was not retried here.

This is left OPEN as architectural: root-causing requires either (a) tracing
the Rust-seed's `use std.X.*` resolution path to determine whether star
imports re-walk `export use module.{...}` re-export lists (the
`nogc_async_mut/spec.spl` probe shows they don't, even though `expect_not` is
explicitly named there), or (b) confirming the seed compiles specs against a
baked-in stdlib snapshot rather than `src/lib` on disk. Both require
instrumenting or rebuilding the Rust seed (`src/compiler_rust/**`), which is
out of scope for a pure-Simple source fix and excluded from this session's
edit scope. No regression was added beyond the existing
`test/01_unit/std/spec_expect_bool_shortcut_spec.spl`, which already pins the
failure precisely and continues to fail for the right reason.
