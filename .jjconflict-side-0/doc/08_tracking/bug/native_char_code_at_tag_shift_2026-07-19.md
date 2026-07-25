# Native codegen: text.char_code_at returns value >>3 (tag-shift corruption) on freestanding lane

- **ID:** native_char_code_at_tag_shift_2026-07-19
- **Status:** SOURCE FIXED in pure Simple (503c075464fc, 2026-07-19) and seed
  parity (c97697506aa, 2026-07-19). The pure MIR path calls a reserved raw-i64
  runtime alias after custom-method lookup; the seed fallback types builtin
  string scalar methods as I64. Seed freestanding verification returned U=88
  (was 11). Pure-Simple x86_64-unknown-none redeploy/QEMU proof remains pending.
- **Severity:** high (silent wrong value; broke all baremetal WM chrome text)
- **Lane:** native-build (cranelift, x86_64-unknown-none, --entry-closure --mode dynload)

## Symptom
In the SimpleOS desktop kernel, `"X:58".char_code_at(0)` returns **11**.
Expected 88 ('X'). 88 >> 3 == 11 exactly — the BoxInt <<3 tag-shift
signature (same family as the seed ANY-channel enum-handle mangling,
doc'd 2026-07-04), not random garbage.

Serial evidence (gated probe, 2026-07-19 boot):
```
[glyph-probe] slen=4 cc0=11
```
`len()` on the same literal is correct (4). `get_glyph_8x16(0x58u8)` with a
literal argument returns correct rows (glen=16 g4=108 g8=124), so the
corruption is exactly at the char_code_at call/return boundary.

## Impact
`SharedWmPixelBufferBackend._px_draw_text` (window_scene_draw_ir.spl) feeds
`char_code_at(ti) as u8` into the glyph table: every lookup misses its
branch, chrome text is wrong for all labels/titles/clock in-guest.
(Full text blankness additionally involves the u8 `!=` bit-test suspect —
tracked separately once probe-confirmed.)

## Repro
Gated `_probe_debug()` serial probe in gui_entry_desktop.spl; seed
native-build to x86_64-unknown-none; boot -kernel or OVMF; grep serial for
`glyph-probe`. Hosted lane (seed interpreter) returns the correct 88 —
freestanding-native only.

## Fix
Pure MIR lowers text-owned `char_code_at(index)` to
`__simple_rt_string_char_code_at(i64, i64) -> i64` after custom-method
dispatch, so neither the index nor result crosses an `Any` boxing boundary.
Pure and hosted C runtimes accept raw literals and validated tagged text and
decode UTF-8 by codepoint index. The seed applies the same raw-I64 result
contract in its builtin method fallback. HIR rejects user definitions of the
compiler-owned alias, and the public C runtime header declares its exact ABI.

## Update 2026-07-19 (later): three tag-shifted views of one value
Deeper probing in FontRenderer showed the SAME logical codepoint 88 ('X')
reads as **0** (= 88 & 7) at one site, **11** (= 88 >> 3) at another, and
the true **88** at a third — per-read-site views of one boxed value, not
independent corruptions. WARNING for workaround authors: two miscompiled
reads can cancel and "work" by coincidence (a bytes()-based read feeding a
downstream that re-applies the shift produced correct-looking results and
was retracted). Fix must be at the boxing/untag layer, not by compensating
at call sites.
