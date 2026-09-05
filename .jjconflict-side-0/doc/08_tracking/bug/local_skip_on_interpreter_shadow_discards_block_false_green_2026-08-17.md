# 19 spec files define a local `skip_on_interpreter` that DISCARDS its block and reports PASS

**Status:** OPEN — root-caused and measured, not fixed (fixing it turns the
affected examples honestly RED; see "Why not fixed here")
**Found:** 2026-08-17, while closing the stale-`MirTerminator.Return` half of
`vhdl_backend_block_temps_emit_process_variables_not_signals_2026-08-04.md`
**Severity:** High — silent false green. Every assertion inside the block is
dead, and the example is still counted as `passed`.

## Symptom

19 spec files under `test/` declare their own helper:

```simple
fn skip_on_interpreter(name: text, block: fn()):
    print "    it {name} ... skipped (interpreter mode)"
```

`block` is never called. Because the helper is invoked from *inside* an
already-registered `it`, the example is registered, executes to completion
with zero assertions, and is reported as **passed**:

```
# test/03_system/feature/compiler/mir_native_spec.spl, as it stands
Results: 3 total, 3 passed, 0 failed
```

Replacing the helper body with `block()` (nothing else changed) shows what
those three greens were hiding:

```
Results: 3 total, 0 passed, 3 failed
    semantic: unknown variant or method 'Return' on enum MirTerminator
```

This helper **shadows the real std decorator**
`skip_on_interpreter(reason: text) -> fn(text, fn())`
(`src/lib/nogc_sync_mut/spec/decorators.spl:295`), which is correct: it routes
to `_skip_or_reject` only when the runtime actually matches, and otherwise
calls `rt_test_it(name, block)` so the body really runs
(`decorators.spl:248-252`). The local shadow is an unconditional, unreported
skip wearing the same name.

## Affected files (19)

`/usr/bin/grep -rln 'fn skip_on_interpreter(name' test/`

```
test/feature/lib/mcp/helpers_spec.spl
test/feature/lib/mcp/handler_function_test.spl
test/feature/usage/resource_cleanup_spec.spl
test/01_unit/compiler/driver/pipeline_basic_spec.spl
test/03_system/feature/ffi/syscalls_test.spl
test/03_system/feature/lib/mcp/helpers_spec.spl
test/03_system/feature/lib/mcp/handler_function_test.spl
test/03_system/feature/compiler/pipeline_native_spec.spl
test/03_system/feature/compiler/mir_builder_spec.spl
test/03_system/feature/compiler/native_compile_elf_spec.spl
test/03_system/feature/compiler/pipeline_multi_spec.spl
test/03_system/feature/compiler/mir_complex_spec.spl
test/03_system/feature/compiler/driver_native_spec.spl
test/03_system/feature/compiler/mir_native_spec.spl
test/03_system/feature/io/async_driver_spec.spl
test/03_system/feature/io/async_driver_echo_spec.spl
test/03_system/feature/usage/resource_cleanup_spec.spl
test/03_system/feature/app/mcp/server_spec.spl
test/unit/compiler/driver/pipeline_basic_spec.spl
```

## Second defect this hid: x86_64 ISel rejects a SIMD value live across a call

With the block actually running AND the stale `MirTerminator.Return` renamed
to the real variant `Ret`, `mir_native_spec.spl`'s three examples still fail,
now for a genuine product reason:

```
Results: 3 total, 0 passed, 3 failed
    semantic: panic: x86_64 SIMD selection rejected: simd-value-across-call-unsupported
```

`isel_module` (`compiler.backend.native.isel_x86_64`) refuses a MIR module in
which a SIMD-typed value is live across a call boundary, instead of spilling
and reloading it around the call. This has presumably been broken for as long
as the false green has been in place; no separate record of it exists.

## Why not fixed here

Making the 19 helpers honest is a one-line change per file, but it converts an
unknown number of currently-"green" examples into honest REDs across compiler,
MCP, FFI and async-IO lanes — at minimum the 3 measured above, which need the
ISel SIMD-spill gap fixed first. Per `.claude/rules/testing.md` those REDs must
not be re-suppressed, so this needs to land as its own campaign with the
product fixes, not as a drive-by in a bug-triage pass. The
`MirTerminator.Return` half — which is a pure correctness defect with no such
blast radius — HAS been fixed; see
`test/01_unit/compiler/mir/mir_terminator_variant_name_spec.spl` and
`test/01_unit/compiler/mir/mir_enum_variant_references_exist_spec.spl`.

## What was NOT proved

- Only `mir_native_spec.spl` was measured with `block()` restored. The other
  18 files' true pass/fail state is unknown.
- All measurements are on the deployed 2026-08-16 **Rust seed**
  (`bin/simple --version` prints its own bootstrap-seed-only warning). Nothing
  here was re-checked against a freshly bootstrapped pure-Simple compiler.
