# `before_all`/`after_all` unresolved when imported from `std.spipe` (t32_hw specs)

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
