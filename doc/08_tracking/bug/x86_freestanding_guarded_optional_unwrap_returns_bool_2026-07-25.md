# x86 freestanding guarded optional unwrap returns the guard boolean

## Status

Open compiler defect; the SimpleOS Draw IR call site uses a source workaround.

## Reproducer

In a freestanding x86 native build, a nullable struct returned from a method is
guarded and then explicitly unwrapped:

```simple
val evidence = engine.vulkan_font_performance_evidence()
if evidence != nil:
    val value = evidence.?
    use(value.field)
```

The relevant production instance was
`_engine2d_draw_ir_adv_composition_with_images` in
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`.

## Evidence

The failing QEMU image reached RIP `0x851f342`, the `ud2` after a generated
nil-field assertion. In the retained ELF, `0x80037f0` is `rt_native_neq`.
Disassembly shows:

1. `rt_native_neq(evidence, nil)` correctly guards the branch.
2. The explicit `evidence.?` is lowered as a second call to
   `rt_native_neq(evidence, nil)`.
3. That comparison result is narrowed with `movzbq %al`, untagged, and then
   treated as the struct pointer for `value.field`.

The resulting boolean cannot be a valid evidence pointer and reaches the nil
assertion. This is distinct from FAT32 traversal and from the previously
documented zero-argument receiver reload defect.

## Workaround

Flow-sensitive narrowing already makes the guarded local non-null. Preserve the
local directly:

```simple
if evidence != nil:
    val value = evidence
```

This matches existing nullable backend handling in `Engine2D`. The focused
source contract is
`test/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.spl`.

## Required compiler fix

Audit optional-access lowering after a `NilCheck(negated: false)` narrowing
fact. `.?` must yield the original nullable payload (or a correctly unwrapped
payload), never the boolean result of the presence comparison. Add a native x86
MIR/codegen regression that asserts a guarded nullable struct field access does
not reuse `rt_native_neq` as the payload.
