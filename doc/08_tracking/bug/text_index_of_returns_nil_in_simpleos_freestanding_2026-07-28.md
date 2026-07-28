# `text.index_of` yields the `??` default for a genuine index of 3

- **Filed:** 2026-07-28
- **Root cause corrected:** 2026-07-28 (original "missing `rt_index_of` symbol"
  diagnosis is RETRACTED below -- it was true but not causal)
- **Severity:** high (silent wrong answer, no diagnostic)
- **Component:** `??` (null-coalesce) lowering vs raw-i64 runtime returns
- **Scope:** NOT freestanding-specific. Reproduced on the Linux x86_64 host.
- **Artifact:** `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`

## Symptom

The one-shot divergence receipt in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:773`
printed, from a live guest run on 2026-07-28:

```
builtin-divergence k=15 np=24 seg_len=4 starts_with_builtin=0 starts_with_portable=0 index_of_builtin=-1 index_of_portable=3
```

`starts_with` agrees. `index_of` does not: on a 4-character segment whose `>`
sits at index 3, the portable `find_from` returns 3 while
`(seg.index_of(">") ?? -1)` yields `-1`.

## RETRACTION of the original root cause

The original filing said the cause was that no `rt_index_of` /
`rt_string_index_of` symbol is linked into the kernel. Both halves of that are
true, and neither is causal:

- `nm` confirms neither symbol is **defined** in the ELF, and neither appears
  in the weak fail-open stub list (`nm kernel.elf | awk '$2=="W" && $3~/^rt_/'`
  returns 60 symbols, none of them `rt_index_of`).
- A symbol that is neither defined nor weakly stubbed is a symbol that is
  **never referenced**. `.index_of()` in this kernel does not call
  `rt_index_of` at all.

Implementing `rt_index_of` in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` would
therefore have been dead code and would have changed nothing.

## PROVEN root cause

`text.index_of` lowers to `rt_string_find`, which is **defined and correct** in
the freestanding runtime (`baremetal_stubs.c:8823`) and returns a **raw,
untagged** byte index, `-1` for not-found. `??` then lowers to a nil test that
compares that raw value against the nil sentinel `3`.

Disassembly of the exact receipt site in the shipped kernel
(`objdump -d -m i386:x86-64` -- the ELF header says ELF32/i386 while the code
is x86-64, so plain `objdump -d` produces garbage here; calls are
`movabs $addr,%reg; call *%reg`, so grepping `call <symbol>` finds nothing):

```
812bd4a: movabs $0x8011f70,%rcx   ; rt_string_new_literal(">", 1)
812bd54: call   *%rcx
812bd56: movabs $0x800c7b0,%rcx   ; rt_string_find(seg, ">")  -> RAW index
812bd67: call   *%rcx
812bd69: mov    $0x3,%esi         ; <-- nil sentinel
812bd6e: movabs $0x8005c70,%rcx   ; rt_native_neq(result, 3)
812bd7b: call   *%rcx
812bd88: test   %rax,%rax
812bd8b: jne    812bd9e
812bd91: mov    $0x1,%eax
812bd96: neg    %rax              ; <-- returns -1
...
812bdd8: call   *%r9              ; rt_unwrap_or_self on the non-nil path
812bde01: call   ..._foundation__find_from   ; gt_portable
```

A legitimate result of `3` is bit-identical to `nil`, so `?? -1` substitutes
the default. Every other `rt_string_find` call site in the kernel
(`_css_resolve_vars`, `parse_http_url`, `_css_first_function_arguments`,
`browser_font_face_source_from_family_value`, ...) consumes the result with a
`shr $0x3f` sign test (`< 0`), i.e. relies on the raw convention, and is
unaffected. Only the `??` site is wrong.

`rt_unwrap_or_self` (`src/runtime/simple_core/core_values.spl:45`) passes
non-enum values through unchanged, so the non-nil path is correct -- there is
no encoding that fixes this in the runtime alone. A tagged `ENCODE_INT(i)`
return would pass the nil test but come back 8x too large; a real Option enum
return would break the nine sign-test call sites.

## Differential test (host, `bin/simple run`)

`(s.index_of(n) ?? -1)` vs an in-Simple portable `find_from`:

| case | builtin | portable | |
|---|---|---|---|
| needle at 0 | 0 | 0 | agree |
| needle at 2 | 2 | 2 | agree |
| **needle at 3** | **-1** | **3** | **DIVERGE** |
| needle at 4 | 4 | 4 | agree |
| not found | -1 | -1 | agree |
| empty haystack | -1 | -1 | agree |
| empty needle | 0 | 0 | agree |
| needle longer than haystack | -1 | -1 | agree |
| repeated occurrences | 1 | 1 | agree |
| `"héllo>x"` | 6 | 5 | DIVERGE (byte vs char, see below) |
| `"日本語>"` | 9 | 3 | DIVERGE (byte vs char, see below) |

Index 3 is the only integer that collides, which is why this hid until a `>`
happened to land at offset 3.

## Second defect found: byte index vs character index

`rt_string_find` returns a **byte** offset (matching hosted
`collections.rs:2446`, which slices `&[u8]`, and matching `rt_string_len`,
which returns `s->len` in bytes). The portable `find_from` compares with
`char_code_at`, which decodes UTF-8 and indexes by **character**
(`baremetal_stubs.c:943`). The two therefore disagree on any multi-byte input.
This is the documented byte-vs-character bug family. The builtin's byte
semantics are the ones that compose correctly with `slice`/`substring`/`len`;
the portable helper is the one that is internally inconsistent (it bounds a
character loop with a byte length).

## Third defect found: `[T].index_of(v)` is universally broken

An `[i64]` receiver also lowers to `rt_string_find` -- the array handle is
passed where a string handle is expected. `decode_string` correctly rejects it
(`hdr.type != HEAP_STRING`), so there is no memory-safety issue, but the result
is `-1` for **every** element, present or not:

```
array index_of(xs[0]) = -1 expect 0
array index_of(xs[1]) = -1 expect 1
array index_of(xs[2]) = -1 expect 2
array index_of(xs[3]) = -1 expect 3
array index_of(xs[4]) = -1 expect 4
```

`rt_array_index_of` is implemented and correct in both the freestanding
(`baremetal_stubs.c:14028`) and hosted (`collections.rs:3019`) runtimes, and is
never emitted by the native-build lane. The receiver-polymorphic `rt_index_of`
that the Rust codegen tables name (`codegen/llvm/emitter.rs:192`,
`codegen/instr/calls.rs:3234`, `codegen/instr/closures_structs.rs:1284`) is not
reached on this path either.

## Fix (compiler lane, not runtime)

The runtime is not at fault. `baremetal_stubs.c` needs no change:
`rt_string_find`, `rt_array_index_of` and `decode_string` are all present,
nil-safe and type-checked.

1. **`??` on a statically non-Optional operand.** `hir/lower/expr/mod.rs:970`
   types `find | index_of | find_str | rfind | last_index_of` as plain
   `TypeId::I64`. Applying `??` to a plain `i64` must not emit a
   `rt_native_neq(v, 3)` nil test -- it should be a build error, or lower to a
   no-op. This kills the whole silent-wrong-answer class, not just index 3.
   The same collision reaches `rfind`/`last_index_of`, whose known-safe status
   is asserted in a comment at
   `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1824`
   ("Revisit if a closure site ever distinguishes them") -- this is that site.
2. **Receiver-polymorphic routing.** Route `index_of` to `rt_index_of` (or
   split array/text by receiver type) so `[T].index_of` reaches
   `rt_array_index_of` instead of `rt_string_find`.
3. Only after (2) does implementing `rt_index_of` in the freestanding stubs
   become live code rather than dead code.

## Immediate mitigation

Callers must not write `index_of(...) ?? default`. `index_of` already returns
`-1` for not-found on this path; the `??` is what manufactures the bug. The
divergence receipt itself
(`simple_web_html_layout_renderer_foundation.spl:773`) is diagnostic-only and
the HTML scan loop uses the portable `find_from`, so no rendering behaviour
depends on this today.
