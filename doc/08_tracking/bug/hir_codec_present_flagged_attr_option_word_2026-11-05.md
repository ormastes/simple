# hir_codec_present_flagged_attr_option_word_2026-11-05

- ID: hir_codec_present_flagged_attr_option_word_2026-11-05
- Priority: P2
- Status: fixed (codec generator, work/hir-attrflag)
- File: src/compiler/20.hir/generated/hir_codec.spl (hc_dec_hir_function, line 4795)

## Symptom
The generated HIR decoder still reads three has_*-flagged fields, export_attr
(ExportAttr), driver_manifest_attr (DriverManifestAttr) and vhdl_metadata
(VhdlHardwareMetadata), into `var f_x: T? = nil` locals and stores them into the
non-optional HirFunction fields. An ABSENT attr decodes to nil exactly as fresh
lowering stores it (safe on stage3). A PRESENT one (an @export, driver-manifest
or vhdl function) carries the Option transport word, so the next by-value
HirFunction copy (e.g. representation_observe_function_v1) faults on the stage3
lane. Same class as #6661 / #6760.

## History (fault offset +0x31d -> +0xa26)
- #6661 fixed HirType / SymbolId / Span placeholders (fault at +0x31d).
- #6760 fixed every other non-optional struct/enum field (fault moved to +0xa26).
- This row is the remainder: the three flagged attrs.

## Why these three were excluded
A bare placeholder for a has_*-flagged field would re-encode as PRESENT (the
encoder writes the payload word, not the flag), breaking byte-identical
round-trips (hir_cfg_select_codec_spec). The Option local keeps absent == nil.

## Fix direction
Make the encoder consult the has_<field> flag (write 0 when the flag is false
regardless of the payload word) so the decoder can use bare placeholders for
these three too. Add a round-trip spec with a PRESENT export_attr (plus
driver_manifest_attr / vhdl_metadata siblings).

## Verification
- File-worker hello canary on stage3 (same binary/settings/root), HIR/MIR/OBJ/link/run.
- An @export function built through the same lane (copies HirFunction by value).
- hir_cfg_select_codec_spec stays byte-identical.

## Fix (2026-11-06)
`src/app/compiler_schema/codec_gen.spl`: `_presence_flag_of` finds the `has_<field>`
bool flag of a non-legacy NODE field; the encoder now writes the presence word
from that flag (`if not node.has_x: w.put_i64(0) else: <payload>`), and the
decoder reads such fields into bare placeholder locals. Applies to every
flag-gated node field (HirFunction export_attr / driver_manifest_attr /
vhdl_metadata, HirClass export_attr / layout_attr, asm spec/asm_body, pattern).
Flagged scalar/text fields and legacy HirType/SymbolId/Span are unchanged.
Codec regenerated. Specs (seed release100-7a0e6fe516f): 
hir_codec_bare_struct_field_locals_spec 14/14, hir_codec_roundtrip_spec 4/4,
hir_cfg_select_codec_spec 4/4 (byte-identical round-trip).
Not verified: stage3 file-worker canary / @export by-value lane (needs bootstrap).
Note: `bin/simple run src/app/compiler_schema/main.spl codec` fails on this seed
("HirModule declared 0 times"); regenerated via generate_codec_into under the test runner.
