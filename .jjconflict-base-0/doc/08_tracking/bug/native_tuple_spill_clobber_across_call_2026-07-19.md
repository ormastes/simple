# Native codegen: tuple stack-spill clobbered by intervening method call

- **ID:** native_tuple_spill_clobber_across_call_2026-07-19
- **Status:** SOURCE FIXED (staged platform execution pending; workaround remains)
- **Severity:** high (silent memory corruption → wild pointer dereference)
- **Lane:** native-build (cranelift, x86_64-unknown-none, --entry-closure --mode dynload)

## Symptom
`FontRasterizer._rasterize_selected_outline` faulted dereferencing a pointer
whose bytes were ASCII text from `self.font_cache_identity` (cr2 =
0x3733626461326263 = "cb2adb37", bytes 2–9 of the font sha256). 79,403
exception frames per boot on the SimpleOS desktop (-kernel lane); quiet
glyph skip under OVMF.

## Root cause
Code shape:

```
val parts = sfnt_rasterize_codepoint_parts(...)   # (ptr, [i64], bool) tuple
if not parts.2: return nil
if not self.is_current(): return nil              # <-- intervening call
val metrics: [i64] = parts.1                      # faults here
```

Cranelift's fallback aggregate branch stored tuple literals in a stack slot
and returned that slot's address unchanged. The pointer therefore referred to
the dead callee frame. `is_current()` later built another tuple and reused the
same frame, replacing `parts.1` with `self.font_cache_identity`. No reload rule
could recover the already-dangling pointer. LLVM already avoided this by
allocating tuple words with `rt_alloc`.

Cranelift now mirrors that ownership: tuple words are heap allocated and the
raw base pointer is returned. Tuple locals are runtime handles, so copies and
control-flow reloads carry that pointer instead of inline tuple storage.
Unlike structs, tuples are not heap-tagged.

## Workaround (landed)
Snapshot every `parts.N` / `metrics[N]` into locals immediately after the
`parts.2` check, before any further call — both in
`_rasterize_selected_outline` and its twin `rasterize_glyph_index`
(src/lib/nogc_sync_mut/sffi/spl_fonts.spl). Post-fix disassembly confirms all
tuple reads complete before `is_current()`; runtime confirms 79,403 → 0
exception frames, first-frame-rendered, desktop-ready.

## Repro / evidence
- Kernel: build/os/_wkheap/desktop.elf via seed native-build (see
  scratchpad build_e2d.sh recipe in session notes), boot via -kernel or OVMF.
- Disassembly: faulting rip +0x480 in `_rasterize_selected_outline`;
  before/after dumps preserved in session scratchpad rasterfix2_backup/.

## Regression
The native smoke and shared cross-target fixtures return `(17, 37, true)`, then
call a same-sized tuple producer returning `(91, 99, false)` before rereading
the first tuple. Both producers are multi-block so MIR inlining cannot erase
the call boundary; hosted Cranelift also uses aggressive optimization. Existing
gates run this on hosted Linux/macOS/Windows/FreeBSD and AArch64/RV64 QEMU;
ARM32/RV32 and Windows ARM64 retain compile-only receipts. Output succeeds only
when the first tuple survives the intervening call.

Local verification on 2026-07-19 linked and ran the preserved focused
Cranelift object successfully (`run_rc=1`, the probe's true result). A bounded
current-source one-case rebuild with a newer pure-Simple Stage3 compiler hit
its 180-second cap with an empty build log and no artifact, so it was not
retried and is not counted as staged platform execution.
