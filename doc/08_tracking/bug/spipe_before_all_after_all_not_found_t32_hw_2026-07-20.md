# `before_all`/`after_all` unresolved when imported from `std.spipe` (t32_hw specs)

## Status: FIXED (resolution half) 2026-08-17 -- one half remains, see below

**Reproduced** (`bin/simple run`, seed 2026-08-16, both `SIMPLE_EXECUTION_MODE=interpreter`
and `=jit`), with a probe importing `use std.spipe.{describe, it, expect, before_all, after_all}`:

```
[use-warning] 'after_all' is named in `use std.spipe.{...}` but module
'.../src/std/nogc_async_mut/spipe.spl' does not provide it
```

**Root cause:** `src/lib/nogc_async_mut/spipe.spl` (and the `nogc_sync_mut` /
`gc_async_mut` siblings) contained only a bare `use std.spec`. A `use` is not a
re-export, so none of `std.spec`'s own `pub fn`s -- including `before_all`
(`src/lib/nogc_sync_mut/spec.spl:617`) and `after_all` (`:620`) -- were visible
through the alias. `describe`/`it`/`expect` kept working only because they are
served by the runner's own DSL builtins, not by the alias module.

**Fix:** each alias now names the hooks explicitly and exports them:

```
use std.spec
use std.spec.{before_all, after_all}

export before_all
export after_all
```

`export use std.spec.*` was tried first and is WRONG here: the star form
resolves `std.spec` to the `spec/` PACKAGE directory (`spec/__init__.spl`), not
`spec.spl`, and produced `error[E1002]: function 'before_all' not found`.
That package-vs-module asymmetry is the same root cause as
`star_import_does_not_reach_expect_not_in_std_spec_2026-08-04.md` and is NOT
fixed by this change.

**After:** the use-warning is gone and the hook runs, in both engine arms:

```
BEFORE_ALL RAN
  v sees
1 example, 0 failures
```

Specs: `test/01_unit/std/spipe_alias_before_after_all_export_spec.spl`
(reproducing) and `test/01_unit/std/spipe_alias_family_export_parity_spec.spl`
(class detection over all four `src/lib/*/spipe.spl` families; ablation-proved
-- reverting `gc_async_mut/spipe.spl` to the bare `use std.spec` turns it RED
1-of-4).

**Remaining, filed here rather than papered over:** `after_all` now RESOLVES but
its deferred hook still does not fire at the end of the enclosing `describe`.
`spec.spl` wires the drain correctly (`_drain_after_all` at `:89`), so the
non-firing is in the runner's builtin `describe`, not in `src/lib/**`.


## Symptom

```
error[E1002]: function `before_all` not found
  = help: check the function name or import the module that defines it

error: test-runner: no examples executed
```

Occurs at spec-load time (before any `it` block executes), so the failure is
independent of whether real T32 hardware is attached.

## Affected specs (at least)

- `test/02_integration/t32_hw/.spipe_matchers_24_history_tail_spec.spl`
- `test/02_integration/t32_hw/12_core_tools_spec.spl`
- `test/02_integration/t32_hw/19_resources_spec.spl`
- `test/02_integration/t32_hw/16_error_check_spec.spl`
- `test/02_integration/t32_hw/10_session_open_spec.spl`
- `test/02_integration/t32_hw/17_window_list_describe_spec.spl`

(All t32_hw specs using the same import line — likely the whole directory.)

## Minimal repro

Every affected file starts with:

```simple
use std.spipe.{describe, context, it, expect, before_all, after_all}

describe "T32 history tail":
    before_all:
        ...
```

Run: `bin/release/x86_64-unknown-linux-gnu/simple test
test/02_integration/t32_hw/.spipe_matchers_24_history_tail_spec.spl --no-session-daemon`

## Root-cause hypothesis

`std.nogc_async_mut.spipe` (resolved via `use std.spipe`) is a 5-line alias
module (`src/lib/nogc_async_mut/spipe.spl`) that just does `use std.spec`.
Neither that alias file nor `src/lib/nogc_sync_mut/spec.spl` (nor any file
under `src/lib/**`) defines a `before_all` or `after_all` function — grepping
the whole `src/lib` tree for `fn before_all` / `before_all,` returns zero
hits. `describe`, `context`, `it`, `expect` all resolve fine (used
successfully by dozens of green specs in the same directory), so this is not
a general import-path problem — specifically `before_all`/`after_all` are
missing as real, importable symbols, even though the SSpec DSL parser accepts
the `before_all:` **block** syntax inside `describe`. It looks like
`before_all`/`after_all` used to exist as callable hook registration
functions (or the block-form desugars to a call of that name) and were
removed/renamed without updating call sites, or the block-form desugar target
was never added to `std.spec`'s export surface.

## Not attempted

No Rust seed / `src/compiler_rust` fix attempted (out of scope per triage
guide — needs a rebuild). This doc is filed for follow-up; do not re-file for
the same "function `before_all` not found" signature in other t32_hw specs —
reference this doc instead.
