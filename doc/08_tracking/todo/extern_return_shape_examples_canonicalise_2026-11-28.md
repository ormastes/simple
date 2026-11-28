# TODO: canonicalise extern rt_* return shapes declared under examples/

**Filed:** 2026-11-28 | **Area:** examples/tooling | **Type:** consistency gap
**Status:** OPEN

`scripts/check/check-extern-return-shape.shs` scans `examples/**/*.spl` since
PR #12364. 18 conflicting names that only conflict through `examples/`
declarations stay in `scripts/check/extern_return_shape_baseline.txt` (the four
t32 stdio names were fixed in the follow-up PR and removed).

## Work
Make each `examples/` declaration use the canonical shape declared in `src/`,
then delete its baseline row. Remaining names (width/handle shapes):
rt_alloc, rt_array_new (`[u32]` in gui_entry_browser.spl), rt_fb_fill32,
rt_gui_begin_frame, rt_gui_blend_fill, rt_gui_present, rt_gui_set_fb,
rt_mmio_read_u16, rt_port_inb, rt_port_inl, rt_port_inw,
rt_riscv_noalloc_pmm_init_default, rt_rv32_probe_load8,
rt_sosix_collector_nonce_echo, rt_string_char_at, rt_string_starts_with,
rt_text_to_bytes, rt_x86_32_install_int80_probe.

Needs the freestanding SimpleOS examples to be buildable to verify callers
after a width change, which is why they were baselined rather than rewritten.
