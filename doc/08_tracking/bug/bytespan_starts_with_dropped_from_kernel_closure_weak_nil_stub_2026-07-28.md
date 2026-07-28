# ByteSpan.starts_with dropped from the SimpleOS kernel closure and silently replaced by a nil-returning WEAK stub

- **Filed:** 2026-07-28
- **Severity:** high (silent wrong answer, no diagnostic, in the WM render path)
- **Component:** native-build entry-closure / per-function emission + seed freestanding stub fail-open
- **Artifact:** `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`

## Symptom (PROVEN)

In the SimpleOS WM production desktop kernel ELF:

```
08023e4f T lib__common__bytes__span__ByteSpan_dot_get
08023e1a T lib__common__bytes__span__ByteSpan_dot_len
08023fa0 T lib__common__bytes__span__ByteSpan_dot_slice
08844960 W lib__common__bytes__span__ByteSpan_dot_starts_with
```

`ByteSpan_dot_starts_with` is an 8-byte WEAK body — `push rbp; mov rsp,rbp;
xor eax,eax; pop rbp; ret` — i.e. it unconditionally returns nil/false.
`ByteSpan_dot_equals`, which `starts_with` calls, is not present in the ELF at
all.

Three sibling methods from the SAME module (`src/lib/common/bytes/span.spl`)
ARE present as real `T` definitions, so the module was compiled — only
`starts_with` and `equals` were dropped from its object.

## It is reached (PROVEN)

21 references, all `movabs $0x8844960,%reg` (there is no relative
`call <symbol>` form, so a naive `grep 'call.*starts_with'` reports a false
"never called"). Enclosing functions:

| refs | caller |
|------|--------|
| 7 | `lib__gc_async_mut__gpu__browser_engine__style_block_parse__sb_background_shorthand_color_value` |
| 4 | `lib__gc_async_mut__gpu__browser_engine__simple_web_html_layout_renderer_style___bg_layer_is_direction` |
| 4 | `lib__gc_async_mut__gpu__browser_engine__dom_color__parse_color_value` |
| 3 | `os__tools__pkg__pkg_repository__load_repositories` |
| 2 | `lib__gc_async_mut__gpu__browser_engine__simple_web_html_layout_renderer_declarations__apply_decls` |
| 1 | `lib__nogc_sync_mut__ui__theme_package___wm_window_gradient_from_css` |

Every CSS colour / background-gradient decision on the desktop path therefore
takes the "prefix does not match" branch unconditionally.

Disassembly note: the kernel ELF header says `ELF32 / Intel 80386` but the code
is x86-64. `objdump -d` MUST be given `-m i386:x86-64`; without it the REX
prefixes decode as `dec %esp` and the output is plausible-looking garbage.

## The source is fine (PROVEN)

Compiled on its own the same source emits real bodies for both:

```
bin/simple native-build --emit-archive --target x86_64-unknown-none \
  --source src/lib/common/bytes --entry src/lib/common/bytes/span.spl -o span.a
nm span.a | grep ByteSpan_dot
  ... T span__ByteSpan_dot_equals
  ... T span__ByteSpan_dot_starts_with
```

So this is not a source bug and not a "chained method on an erased receiver"
limitation — it is a kernel-build closure/emission miss.

## Why nothing failed the build (root cause of the silence)

`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` fabricates a
weak nil-returning definition for **any** symbol left undefined in the link
set. Its filters exclude system, dyld, C++, compiler-rt and linker-provided
names, but nothing excludes pure-Simple `lib__*` / `os__*` symbols.

The freestanding fabrication guard that would otherwise catch this —
`simpleos_check_no_fabricated_rt_stubs` in
`src/compiler/70.backend/backend/llvm_native_link.spl` (approx. lines
2266-2433) — is scoped to `rt_*` externs only. A fabricated pure-Simple method
body is outside its remit, so the link succeeds and the guest silently gets
`false` from 21 call sites.

`ByteSpan_dot_starts_with` is the only `lib__` weak symbol in this ELF, so the
blast radius today is exactly this one method — but the fail-open is general.

## Hypotheses already refuted

- **Not an entry-closure file-level miss.** Rebuilding the same module with
  `--emit-archive --entry-closure --target x86_64-unknown-none` still emits
  real `T` bodies for both `starts_with` and `equals`. The drop needs the full
  kernel context to reproduce.
- **Not the second `ByteSpan`.** `src/lib/nogc_sync_mut/db/accel.spl:31`
  declares a same-named `ByteSpan`, but no `db__accel` symbol appears anywhere
  in this ELF, so a global struct-registry collision with that module is not
  the mechanism here.

## Suggested fixes

1. **Root:** find why the kernel entry-closure records the 21 calls to
   `starts_with` yet never schedules its body (and consequently never
   discovers `equals`). Bare-method-name collision is the leading suspect:
   `starts_with` also exists as `rt_string_starts_with`,
   `Path_dot_starts_with`, `_text_starts_with_slash` and
   `_bytes_starts_with` in this same ELF.
2. **Guard (defence in depth):** extend the fabrication refusal so that a
   `lib__*` / `os__*` symbol resolving to a fabricated weak nil body fails the
   freestanding link, exactly as a novel fabricated `rt_*` extern already does.
   A pure-Simple method must never be papered over by a stub.
