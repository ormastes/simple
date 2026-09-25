# Single-file AOT compile with import-closure loading crashes in MIR prescan

**Status:** open. The fix is not landed; it is blocked on this crash. Owner: memory-corruption investigation (Fable agent).
**Host:** Windows x86_64-pc-windows-msvc. Stage-2 self-hosted `simple_cli.exe`, built from `716b6864a3d`+#1609 by the admitted stage-2 compiler.

## Context

`compile x.spl -o x.smf` loads only the named file, so HIR fails with
`missing module surface for <every import>`: `std.io_runtime` for a plain program,
`compiler.core.ast` for `ast_native_arena_spec`. The in-process `run` path
already fixed the same gap by routing a lone `.spl` input through the
entry-closure walk (`driver_source_pipeline_loading.spl`, `interpret_single_entry`).

The fix below is the reuse; it adds no second copy. It extends that walk to `CompileMode.Aot`, and only
`run` keeps the SSpec prelude:

```diff
--- a/src/compiler/80.driver/driver_source_pipeline_loading.spl
+++ b/src/compiler/80.driver/driver_source_pipeline_loading.spl
-        val interpret_single_entry =
-            if self.ctx.options.mode == CompileMode.Interpret and driver_inputs.len() == 1 and
-                    driver_inputs[0].ends_with(".spl"):
+        val single_source_entry =
+            if (self.ctx.options.mode == CompileMode.Interpret or
+                    self.ctx.options.mode == CompileMode.Aot) and
+                    driver_inputs.len() == 1 and driver_inputs[0].ends_with(".spl"):
                 driver_inputs[0]
             else:
                 ""
+        val interpret_single_entry =
+            if self.ctx.options.mode == CompileMode.Interpret: single_source_entry else: ""
         driver_set_spec_prelude_entry(interpret_single_entry)
         val native_entry_env = rt_env_get("SIMPLE_NATIVE_BUILD_ENTRY") ?? ""
-        val native_entry_input = if native_entry_env != "": native_entry_env else: interpret_single_entry
+        val native_entry_input = if native_entry_env != "": native_entry_env else: single_source_entry
```

## Repro

`iort.spl`:

```
use std.io_runtime.{env_get}

fn main():
    val h = env_get("HOME") ?? ""
    print "len {h.len()}"
```

`simple_cli compile iort.spl -o iort.smf`, with the patch applied, or without it and with
`SIMPLE_NATIVE_BUILD_ENTRY=iort.spl`. Environment: `SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NO_BOOTSTRAP_DELEGATE=1`
and the MSVC bootstrap env.

- A no-import file (`fn main(): print "hello"`) compiles: exit 0, 12.5 s warm, 745,808 KiB.
- `iort.spl` (18 closure sources) exits 0xC0000005 after 16–21 s warm, with a peak of about 950 MB. Stderr carries
  `[simple-runtime][error] rejected invalid array handle before dereference; probable compiler/FFI ABI mismatch`,
  plus 158 `hir-reexport-chase-unresolved` and `hir-callable-dep-origin-unresolved` lines for builtins
  (`text`, `i64`, `bool`, `Option`, `Result`) in `lib.common.io.types`,
  `lib.common.process.observation_v1`/`deadline_v4`, `lib.nogc_sync_mut.io.pipe` and others.

## Location

`SIMPLE_COMPILER_TRACE=1` and temporary markers place the crash after
`aot:lower_to_mir:start`, inside the cross-module prepass
(`driver_pipeline_lowering.spl`, the `direct_prescan_idx` loop, which calls
`MirLowering.prescan_module_struct_names` in `50.mir/_MirLowering/module_lowering.spl`).
Modules 0 (`iort`) and 1 (`lib.io_runtime`) pass. In module 2
(`lib.nogc_sync_mut.io_runtime`) the struct and class loops pass, and the crash is in the
per-function loop.

**The crash point moves when prints are added:** after `dir_list_optional` with one set of markers,
and after `rt_dir_list` finished `bootstrap_fn_ret_shape_register` with more markers. The loop logic is
therefore not the defect. This looks like value-lifetime or arena corruption of HIR data belonging to
closure-loaded modules, which the runtime's invalid-array-handle guard also reports. That cause is
unproven.

## Impact

No spec, and no program with an import, can compile to SMF with the self-hosted CLI. This blocks the
stage-2 `--mode=native` test lane.
