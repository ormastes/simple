# Native coverage lane fails to compile any spec importing `compiler.loader.provider_admission.admission`

- Status: OPEN (2026-09-12)
- Found by: lane L6 (dynlib / aspect dynload) fan-out, while adding unit specs
  under `test/01_unit/compiler/99.loader/`
- Scope: out of L6's scope; filed, not fixed
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
  (Rust bootstrap seed), sha256 `3d120a6f9ab5704b...`
- Base revision: `79a67e79135`

## Symptom

`bin/simple test <dir>` runs a native coverage lane in addition to the
interpreter lane. That native lane fails to compile any spec that transitively
imports `compiler.loader.provider_admission.admission`:

```
error: compile failed (/tmp/spipe_wrapped__tmp_simple_cov_..._spec_native.spl):
  semantic: ...: struct `Task` has no field named `priority`
```

The spec then reports `outcome=ERROR ... passed=0 failed=1` even though the
same spec is GREEN when run as a single file (interpreter lane).

## Minimal repro

Six lines, no L6 code involved:

```simple
use std.spec.step
use compiler.loader.provider_admission.admission.{provider_admission_digest_valid_v1}

describe "native lane probe: provider admission":
    it "imports the in-tree digest validator":
        step("Verify: pre-existing import compiles in the native coverage lane")
        expect(provider_admission_digest_valid_v1("a".repeat(64))).to_equal(true)
```

```
bin/simple test <dir containing that spec>/     -> rc=1, the error above
bin/simple test <that spec file>                -> rc=0, 1 passed
```

Importing `std.nogc_sync_mut.concurrent.thread.{thread_yield}` alone does NOT
reproduce it, so the trigger is not the thread import by itself.

## Suspected cause

A `Task` type-name collision surfaced by whole-program co-compilation in the
native lane. At least three unrelated `Task` declarations exist:

- `src/lib/scv/lifecycle/model.spl:153` — `struct Task` (no `priority` field)
- `src/lib/nogc_async_mut/async/task.spl:35` — a `Task` that does have `priority`
- `src/lib/nogc_async_mut/async/runtime.spl:32` — `struct Task<T>`

This is the same family as the `compiler_cross_module_private_symbol_collision`
warnings the same run emits for `shell`, `process_wait`,
`process_run_with_limits`, `file_read_text_at` and `mcdc_condition_key`: the
native lane resolves a name to the wrong definition when several co-compiled
modules declare it.

## Impact

Any new unit spec placed in a directory alongside one that reaches
`provider_admission` fails the directory-mode run, which makes directory-mode
verdicts unusable for `test/01_unit/compiler/99.loader/`. Per-file runs are
unaffected, so this is a lane defect, not a product-code defect.

## Not done here

No fix attempted: the owning paths are outside L6's scope and
`src/compiler/99.loader/provider_admission/state.spl` is fenced in the current
freeze.
