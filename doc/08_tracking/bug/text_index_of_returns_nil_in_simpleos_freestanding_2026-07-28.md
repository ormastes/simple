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

---

## UPDATE 2026-08-09 — step (3) went live and FIXED; the retraction is superseded

**Status: FIXED** for the erased-receiver route. The 2026-07-28 retraction above

- **Verification 2026-08-21 (bug-status-consistency audit): PARTIAL, not fully fixed.** The erased-receiver fix is real (`rt_index_of` at `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:10462`; cranelift allowlist `("index_of", 1)` at `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:204`; commit `2c782cbfb76`; guard spec `test/01_unit/os/kernel/boot/baremetal_rt_index_of_not_fabricated_spec.spl` exists). Still open: (1) the NON-erased-receiver route in `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` is untouched; (2) `llvm_native_link.spl` refuses only *baselined* fabrications, so an unbaselined `rt_*` fabrication still passes fail-open. Two cited artefacts do not check out: the evidence ELF `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf` is absent, and the helper-form citation points at `..._foundation.spl:431` where the helper actually lives in `..._renderer_style.spl` (69 sites today, not 75). `bug_db.sdn` row is `fix-implemented-verification-pending`.
("implementing `rt_index_of` would be dead code") was correct *on that day* and
is now **superseded by a change that landed after it**, not wrong in hindsight.

### What changed between the two readings

`("index_of", 1)` was added to cranelift's
`is_bare_builtin_collection_method` allowlist on 2026-08-01
(`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:204`) to stop
a bare, erased-receiver `.index_of()` being STOLEN by a same-named user method
(census: 8 binds, all landing on `dbfs_engine.txn.TxnStepSequence.index_of` —
see `codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`).
That mitigation routes those calls to `rt_index_of`. It is exactly step (2) of
"Suggested next steps" above, and it made step (3) load-bearing — but step (3)
was never done, so on x86_64 the newly-live reference resolved to
`boot/auto_stubs.c`'s WEAK fabricated definition instead of failing to link.

### Measured evidence (guest kernel ELF, this repo)

`build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`:

```
$ nm  ... | grep rt_index_of
08699910 W rt_index_of                 # W, not T — fabricated

$ objdump -d --start-address=0x08699910 ...
08699910 <rt_index_of>:
  push %rbp ; mov %rsp,%rbp ; xor %eax,%eax ; pop %rbp ; ret
```

The entire body is `xor %eax,%eax; ret` — **constant 0**. `nm` reports every
other member of the erased-receiver builtin family as `T` (`rt_contains`,
`rt_slice`, `rt_index_get`, `rt_push`, `rt_array_pop`, `rt_string_rfind`,
`rt_string_starts_with`, `rt_string_ends_with`, `rt_to_string`); the rest of the
family (`rt_find`, `rt_len`, `rt_at`, `rt_map`, `rt_take`, `rt_drop`,
`rt_reverse`, `rt_collection_remove`, `rt_string_find`) is ABSENT, i.e. never
referenced. Of the 62 weak `rt_*` stubs in this kernel, `rt_index_of` is the
**only** one with text/collection semantics — every other is a GPU/DMA/virtio
"backend unavailable" stub where nil is the intended answer. **The family is
enumerated and closed: one victim, now fixed.**

Constant 0 reads as "match at byte offset 0". Callers guard with `if idx > 0:`,
so it reads as NOT FOUND. Guest receipt, both values on the SAME receiver in the
same run:

```
raw_len=15 line_len=15 colon_index_of=0 colon_find_from=11
```

That single wrong 0 dropped all 45 `:root` CSS custom properties (`prop_count`
0 -> 45 once the call site was routed to `find_from` by `2c782cbfb76`).

### The routing itself is NOT at fault

Reloc census on a freestanding probe archive (`native-build --entry-closure
--emit-archive --target x86_64-unknown-none --backend cranelift`) carrying
`props.trim().index_of(":")` next to a typed `Str.index_of`:

```
1 probe__Str_dot_index_of
1 rt_index_of
1 rt_string_trim
```

One reloc each — the erased call goes to the builtin and the typed call keeps
its own method. No theft. The host JIT oracle for the same probe prints `v=8`,
the correct index. **The defect was purely the missing definition.**

### Fix

`rt_index_of` implemented in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`, modelled on
the sibling `rt_find` directly above it (which carries the identical rationale,
verbatim: *"a weak 0-returning stub would have reported 'match at index 0' for
every call"*). Array receiver first, then text, **both branches returning a RAW
index** — deliberately NOT delegating to the neighbouring `rt_array_index_of`,
which returns a tagged `ENCODE_INT(i)`.

Only x86_64 needed it: no other arch's `baremetal_stubs.c` defines `rt_find` or
`rt_string_find` either, and only the x86_64 link pulls `auto_stubs.c`, so on
every other arch this fails CLOSED at link rather than fabricating a 0.

Regression guard:
`test/01_unit/os/kernel/boot/baremetal_rt_index_of_not_fabricated_spec.spl`
(3/3 green; sabotage-checked — renaming the C function turns 2 of 3 red).
Link-level sabotage also confirmed: linking only the weak stub reproduces
`xor %eax,%eax; ret`, while linking the real definition yields a strong `T`
that tail-jumps into `rt_string_find`.

### The guard that should have caught this, and did not

`config/simpleos_fabricated_rt_baseline.sdn` + the refusal in
`src/compiler/70.backend/backend/llvm_native_link.spl` are supposed to block
newly-fabricated `rt_*` symbols. `rt_index_of` is **not in that baseline** and
shipped anyway: the check compares the fabricated set against the baseline and
only fires on a *baselined* entry, so an entry that is fabricated but
UNBASELINED fails OPEN. That is a separate, still-OPEN defect and is the reason
this reached a guest at all. **Follow-up (not done here): make the fabricated-set
check fail closed on any `rt_*` fabrication that is absent from the baseline,
which is the strictly-stronger reading the "baseline is shrink-only" comment
already implies.**

### Helper form is NOT affected

`text_index_of(h, n)`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:431`)
is `find_from(h, n, 0)` — a pure-Simple byte scan over `.bytes()`, calling no
runtime search symbol. All 75 repo-wide `text_index_of(` sites (55 `src/lib`,
16 `src/compiler`, 4 `test`) were always safe, including the ~10 in
`simple_web_html_layout_renderer_core.spl`. Only the method form
`<receiver>.index_of(...)` was ever exposed, and only where the receiver type
was erased.
