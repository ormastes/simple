# SimpleOS WM Freestanding ByteSpan CSS Scanner Fault

## Status

Source fix implemented; live SimpleOS verification remains open. Fresh OVMF
boot reaches the production desktop compositor and scanout, but the bounded
run made before the final compiler fix faults during the first Simple Web CSS
scan and therefore produced no framebuffer capture.

## Evidence

The final bounded run is:

`doc/09_report/wm_glass_theme_qemu_span_fix_2026-07-24.md`

The serial log reaches font registration, shell initialization, application
spawn, software-render fallback, NVMe/FAT32 setup, and the 3840x2160 scanout.
It then repeatedly page-faults with the first return address inside:

`simple_web_html_layout_renderer._css_scan_rules_simple`

The faulting instruction is inside:

`common.bytes.span.ByteSpan.starts_with`

Disassembly of the guest kernel proved this was a compiler dispatch error, not
corrupted `ByteSpan` data. `_css_scan_rules_simple` passed its trimmed text
receiver and the literal `"@"` to the address of
`ByteSpan.starts_with`. Many unrelated text call sites had the same target.
The HIR method resolution could retain a stale aggregate owner, while MIR's
text fallback only corrected `Unresolved` calls.

`method_calls_literals.spl` now treats MIR/HIR-proven text as authoritative for
`starts_with`, `ends_with`, and `contains`, even when HIR supplied a stale
resolved instance method. Genuine custom struct receivers retain their normal
dispatch.

A fresh pure-Simple Cranelift bootstrap compiler was built at:

`build/bootstrap-wm-text-dispatch/stage4-cranelift/aarch64-apple-darwin/simple`

Its CSS-shaped collision fixture emitted
`exercise_css_text_owner -> rt_string_starts_with`; the same object separately
defines and calls `CustomPrefixOwner.starts_with`. It has no `ByteSpan`
predicate reference. The executable link was blocked by an existing
`libsimple_runtime.a` Metal-framework linkage gap, after object generation.

## Required next scope

In a fresh session, run one new SimpleOS QEMU evidence cycle with a compiler
containing the text-owner override. Confirm that CSS parsing passes this site,
then collect the themed framebuffer and maximize/restore evidence. Do not
bypass the canonical parser or replace the themed document with direct
rectangles. The full Aetheric package CSS must remain intact through computed
style and layout.

The QEMU verify/fix cap was reached in this session; do not rerun here.
