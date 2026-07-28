# `text.index_of` returns nil in the SimpleOS x86_64 freestanding build

- **Filed:** 2026-07-28
- **Severity:** high (silent wrong answer, no diagnostic)
- **Component:** freestanding runtime symbol set / `index_of` lowering
- **Artifact:** `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`

## Evidence (PROVEN)

The one-shot divergence receipt in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:773`
prints, from a live guest run on 2026-07-28:

```
builtin-divergence k=15 np=24 seg_len=4 starts_with_builtin=0 starts_with_portable=0 index_of_builtin=-1 index_of_portable=3
```

`starts_with` agrees. `index_of` does not: on a 4-character segment whose `>`
sits at index 3, the portable `find_from` returns 3 while the builtin path
yields `-1`.

The `-1` is the `?? -1` default of `val gt_builtin = (seg.index_of(">") ?? -1) as i32`,
so the builtin returned **nil**, not `-1`.

`nm` on the kernel confirms why: there is no `rt_index_of` and no
`rt_string_index_of` symbol in the ELF at all. The only `index_of` symbols
present are unrelated pure-Simple ones:

```
0809cfcb T lib__common__ui__web_render_api___web_render_index_of_from
08125540 T lib__gc_async_mut__gpu__browser_engine__..._foundation__text_index_of
085b1d08 T lib__nogc_sync_mut__db__dbfs_engine__txn__TxnStepSequence_dot_index_of
```

Codegen routes the `index_of` method to `rt_index_of`
(`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1284`,
`llvm/emitter.rs:192`), and `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`
implements `rt_string_find` and `rt_string_index_of` but **not** `rt_index_of`.

## Impact

Not the cause of the current `guest-render-fault`: the HTML scan loop itself
uses the portable `find_from`, and the divergence receipt is diagnostic only.
But any other freestanding caller of `.index_of` on text or arrays silently
gets nil.

## Fix

Implement `rt_index_of` (receiver-polymorphic: array or text) in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`, delegating
to the existing `rt_string_index_of` / array path, as the freestanding
fabrication guard in
`src/compiler/70.backend/backend/llvm_native_link.spl` already instructs for
novel fabricated `rt_*` externs.
