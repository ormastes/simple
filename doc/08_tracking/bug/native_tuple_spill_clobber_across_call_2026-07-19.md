# Native codegen: tuple stack-spill clobbered by intervening method call

- **ID:** native_tuple_spill_clobber_across_call_2026-07-19
- **Status:** OPEN (workaround landed in spl_fonts.spl; root cause in compiler)
- **Severity:** high (silent memory corruption → wild pointer dereference)
- **Lane:** native-build (cranelift, x86_64-unknown-none, --entry-closure --mode dynload)

## Symptom
`FontRasterizer._rasterize_selected_outline` faulted dereferencing a pointer
whose bytes were ASCII text from `self.font_cache_identity` (cr2 =
0x3733626461326263 = "cb2adb37", bytes 2–9 of the font sha256). 79,403
exception frames per boot on the SimpleOS desktop (-kernel lane); quiet
glyph skip under OVMF.

## Root cause (disassembly-verified, compiler defect suspected)
Code shape:

```
val parts = sfnt_rasterize_codepoint_parts(...)   # (ptr, [i64], bool) tuple
if not parts.2: return nil
if not self.is_current(): return nil              # <-- intervening call
val metrics: [i64] = parts.1                      # faults here
```

The tuple was spilled to stack (0x60/0x68(rsp)). `is_current()` internally
builds its own `(i64, text)` tuple whose slot 1 holds
`self.font_cache_identity`. After the call, the inlined constant-index read
of `parts.1` (`rt_tuple_get(parts, 1)` → untag → items ptr at +0x18 →
`mov (%r10),%r12`) yielded the identity string's data pointer instead of the
metrics array — i.e. the spilled tuple value was not preserved across the
call boundary. No `free()` exists anywhere on the path (premature-free ruled
out). Heap-layout dependent, not per-glyph deterministic.

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

## Fix direction
Audit native-lane tuple spill/reload around call boundaries: a spilled
tuple-typed SSA value (or its element pointers) must be reloaded from its
spill slot after a call, not from a register/slot the callee's own tuple
construction may have reused.
