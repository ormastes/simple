# Frozen stage2 lowers field access on the reassigned `var hir_module` at offset 0 (stage3 hello AV)

- **ID:** stage2_var_hir_module_field_access_offset0_2026-11-03
- **Priority:** P1 (phase 3: every stage3 built by the frozen stage2 dies in the HIR loop of the first module)
- **Status:** open. Source workaround landed (typed accessors in
  `src/compiler/80.driver/driver_hir_pipeline_lowering.spl`); the stage2 miscompile itself is not fixed.

## Symptom
`C:/dev/p3new/s3new/s3.exe native-build --entry-closure --entry test/04_smoke/bootstrap_hello_world.spl ...`
passes source load, surface freeze and parse (1/1), prints
`[bootstrap-error-count] source_idx=0 point=post-store count=0`, then exits with 0xC0000005 after ~150-300 s.
The Application event log names the fault: `s3.exe` offset `0x568613` =
`compiler.semantics.value_struct_layout.value_struct_layout_declarations_v1 + 0xab3`, the
`movq (%rax), %rcx` that unboxes the `symbols` parameter and reads `symbols.symbols` right after
`rt_dict_new` (the `struct_symbols = {}` allocation). WER LocalDumps under HKCU is not honored on this host and
lldb makes the process idle, so the receipt is the event-log offset plus static disassembly.

## Evidence (static, object `C:/dev/p3new/aot-c73261...o` = driver_hir_pipeline_lowering, built 2026-11-02 by stage2 ef0681fc0e1)
In `CompilerDriver.lower_and_check_retained_owner_impl` every field access on the loop's
`var hir_module: HirModule = if hir_cache_hit: ... elif ...` compiles to a load at OFFSET 0 of the module:

```
622b: movq 0xe0(%rsp),%rax ... 6246: movq (%rdx),%rcx      ; driver_dict_entry_count(hir_module.functions)
7308: movq 0xe0(%rsp),%rax ... 7323: movq (%rdx),%rdx      ; hir_module.path
7326: movq 0x78(%rsp),%rcx ; 732b: movq %rdx,%r8 ; 732e: movq %rdx,%r9   ; structs = symbols = path = word 0
7331: call value_struct_layout_declarations_v1
```

`lower_and_check_streaming_surfaces_impl` shows the same shape on its `var hir_module: HirModule = nil`
(`3424: movq (%r9),%r8 ; movq %r8,%r9`, `351d: movq (%rdx),%rcx`), and that loop also WRITES
`hir_module.representation_declarations = ...` through the same mistyped var. The one site in the file that
uses a `val resolved_module: HirModule = ...` gets the real offsets (`path@0x8`, `symbols@0x28`, `structs@0x50`),
and the NEW combined3 constructor (`module_build.HirLowering.lower_module`: `rt_alloc(0xe0)`, snapshot stored at
`0x28`, functions at `0x30`, structs at `0x50`) agrees with those offsets, so this is not a layout mismatch
between the two object lineages: the stage2 lost the static type of a reassigned, annotated `var`.

Receipts: `C:/dev/p3new/s3new/fable_defs_lineage.txt`, `fable_dis_retained.txt`, `fable_dis_streaming.txt`,
`LINK_NOTES.md` (S3N-4).

## Workaround (source, tagged)
`driver_hir_module_{typed,path,structs,symbols,functions}_v1(m: HirModule)` accessors; every read of the var in
both loops goes through them and the one write rebinds through `driver_hir_module_typed_v1` first. Field
access through a typed PARAMETER lowers correctly in the same object (`value_struct_layout_declarations_v1`
reads `symbols.symbols` from its parameter). Spec:
`test/01_unit/compiler/driver/hir_loop_module_field_access_typed_spec.spl`.

## Removal condition
A stage2 that types reassigned annotated vars (any seed-built stage2 from release/1.0.0 at or after this
change) compiles the loops with real offsets; then the accessors can be inlined again.
