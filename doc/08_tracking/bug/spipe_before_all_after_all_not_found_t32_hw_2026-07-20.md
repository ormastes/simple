# `before_all`/`after_all` unresolved when imported from `std.spipe` (t32_hw specs)
## RESOLVED 2026-11-25 — hooks implemented in `std.spec` and re-exported by the `std.spipe` alias; verified by code inspection (see note at bottom)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Verification 2026-11-25 (release/1.0.0 HEAD 4bc2c986375, work/p2w5-aa lane)

The root-cause hypothesis in this doc was exactly right, and the fix matching
it is in tree:

- `src/lib/nogc_sync_mut/spec.spl:1301` defines `pub fn before_all(hook: fn())`
  (runs the block immediately at its declaration point) and `:1314` defines
  `pub fn after_all(hook: fn())` (deferred, drained by the enclosing `describe`
  via `_drain_after_all`, `:1319`). The implementation comment at `:1280-1300`
  cites this bug doc by name.
- `src/lib/nogc_sync_mut/spipe.spl:13-16` explicitly imports and re-exports
  both hooks (`use std.spec.{before_all, after_all}` + `export`), with a
  comment explaining why a bare `use std.spec` did not re-export them —
  also citing this bug doc. `src/lib/nogc_async_mut/spipe.spl` and
  `src/lib/gc_async_mut/spipe.spl` carry the same fix.

So `use std.spipe.{describe, context, it, expect, before_all, after_all}`
now resolves every name. Live spec execution is environment-blocked on this
host: the pinned v1.0.0-rc.1 seed rejects the `@representation_boundary`
decorator at release/1.0.0 HEAD, so `bin/simple.exe test` fails repo-wide at
semantic analysis before any spec (including the t32_hw specs, which also
need real T32 hardware) can load. Verification is by code inspection; the
symbols, the re-export chain, and the hook semantics all exist as described.
Closing as STALE (fixed in tree; the "Open 2026-09-16" header came from the
2026-09 tree-transplant normalization, not from a live defect).
