# Bug: String method calls return -1 in core-c-bootstrap native builds

- **ID:** native_string_method_returns_neg1_core_c_bootstrap
- **Severity:** P1 (blocks native string ops) — *needs confirmation of scope*
- **Date:** 2026-05-29
- **Area:** compiler / seed native codegen (string method dispatch)
- **Status:** RESOLVED — deployed seed reverified 2026-05-29

## Summary

In `native-build --runtime-bundle core-c-bootstrap`, calling `.len()` on a
`text`-typed receiver returns **-1**, even though the string runtime symbols
are present in the linked binary (`_rt_string_len`, `_spl_str_len`, `_rt_len`
all confirmed via `nm`). The native codegen appears NOT to call these functions
for string `.len()` — it emits a dynamic-dispatch path that returns -1 (the
"not-found" sentinel). The same affects `.slice()` and `.substring()`.

## Impact

Blocks the editor TUI **native render path (Route 2)** — `len`/`slice` are used
throughout the render/controller code, so the editor cannot draw a frame even
after the `EditorBuffer`/LSP layer compiles. Likely affects other native
programs that use string methods in `core-c-bootstrap` mode.

## Evidence (from the render agent, 2026-05-29)

- The string runtime IS linked (symbols present in the binary).
- `.len()` still returns -1 → codegen isn't dispatching to the runtime fn.
- Earlier a related symptom appeared as `function not found: str.slice`.

## Root cause analysis (2026-05-29)

Two separate bugs, both fixed:

### Bug 1: `.len()` returning -1 (fixed earlier today)

The Cranelift inline len implementation in `helpers.rs` loaded `i8` at offset 0
and compared it to `0x53545231` — but `RtCoreString.kind` is `uint32_t`, so the
comparison always failed. The -1 sentinel was returned because `tag == heap` but
`kind != string`, so the type check fell through to `done_block` with `invalid`.

Fix: load `i32` at offset 0 and compare to `0x53545231i64`
(`src/compiler_rust/compiler/src/codegen/instr/helpers.rs`).

### Bug 2: `.slice()` and `.substring()` printing "function not found: str.slice"

For `val s: text`, `TypeId::STRING` maps via `builtin_type_name` to `"str"`,
so the MIR emits `MethodCallStatic { func_name: "str.slice", args: [start, end] }`.

`compile_method_call_static` sets `prefer_builtin_first = true` (because
`lookup_name` contains a dot and `receiver_ty == TypeId::STRING`), and calls
`try_compile_builtin_method_call`. That function correctly handles `"slice"` /
`"substring"` by calling `rt_slice` — BUT only if `ctx.runtime_funcs.get("rt_slice")`
succeeds. If it returns `None`, the function returns `Ok(None)` and execution
falls through to `rt_function_not_found`.

`runtime_funcs` is populated by `declare_runtime_functions`, which skips any
symbol not in `referenced_names` AND not a `runtime_symbol_is_codegen_root`.
`"rt_slice"` was in neither list: `referenced_names` only gets `"rt_slice"` from
`MirInst::SliceOp`, but `MethodCallStatic` with `"str.slice"` never adds it.

Fix: add `"rt_len"` and `"rt_slice"` to `runtime_symbol_is_codegen_root` in
`src/compiler_rust/compiler/src/codegen/common_backend.rs`.

## Verification

Minimal repro (`val s: text = "abc"; println(s.len()); println(s.slice(1,3)); println(s.substring(1))`):

- Before fix: `3` / `function not found: str.slice` / `function not found: str.substring`
  (`.len()` was already fixed by today's `helpers.rs` i32 change; the seed at 05:33
  post-dated `helpers.rs` at 05:30 so the i32 fix was already active.)
- After fix: `3` / `bc` / `bc` ✓

Backend: Cranelift (bootstrap binary built without `--features llvm`; default
`BackendKind::for_target` returns `Cranelift` when LLVM feature is absent).

## Re-verification (2026-05-29, post-commit check)

Repro run against the currently deployed seed (`bin/simple`, mtime 05:33 UTC May 29):

```
$ bin/simple compile /tmp/string_method_repro.spl -o /tmp/out --native --runtime-bundle=core-c-bootstrap
$ /tmp/out
-1
Runtime error: Function 'str.slice' not found
Runtime error: Function 'str.substring' not found
```

**Still broken.** Root cause: fix commit `27b41b8340` (05:57 UTC May 29) landed **24 minutes after**
the seed binary was last written (05:33 UTC). The source files (`common_backend.rs`,
`helpers.rs`) contain the correct changes, but the deployed `bin/simple` seed binary
does not include them.

## Re-verification (2026-05-29, deployed seed)

The currently deployed `bin/simple` now contains the source fix. Focused native
core-C bootstrap repro:

```bash
bin/simple native-build --entry /tmp/string_method_repro.spl --entry-closure --backend cranelift --runtime-bundle core-c-bootstrap --output /tmp/string_method_repro_bin
/tmp/string_method_repro_bin
```

Observed output:

```text
3
bc
bc
```

This closes the deployment gap for `.len()`, `.slice()`, and `.substring()`.

## Files changed

- `src/compiler_rust/compiler/src/codegen/common_backend.rs` — add `"rt_len"` and `"rt_slice"` to `runtime_symbol_is_codegen_root`
- `src/compiler_rust/compiler/src/codegen/instr/helpers.rs` — fix `inline_runtime_len_value` to load `i32` for string kind check (landed earlier today)

## See also

- `doc/08_tracking/feature/editor_markdown_editing_subsystem_2026-05-28.md`
- `doc/08_tracking/bug/editor_jit_run_route_blockers_2026-05-28.md`
