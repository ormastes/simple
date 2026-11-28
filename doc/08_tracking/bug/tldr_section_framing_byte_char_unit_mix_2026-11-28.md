# TLDR section framing mixes character and byte counts

**Found:** 2026-11-28, aspect plan stage AW-1/AW-2 (seed `simple-local-20261128f`).
**Status:** open. Not fixed in the AW-1/AW-2 change (wire-format change of an existing reader).
**Severity:** silent data loss. **Must be fixed before the `aspect-decl|` /
`join-point|` writers are wired into TLDR publication** (plan stage AW-1w).

## 1. Module TLDR companion record (`module_tldr_sections_v1.spl`)

`module_tldr_sections_render_v1` writes `section: <kind> <body.len()>`, a
**character** count. `module_tldr_sections_parse_v1` cuts the body with
`rest.substring(body_start, body_start + count)`, a **byte** range, and then
only checks that the byte after it is a newline.

The reader is **not fail-closed**. Two outcomes, both reproduced:

```simple
# (a) whole companion rejected
val wire = module_tldr_sections_render_v1(["const|val X = 결제", "type|type A = i64"])
val (entries, consumed) = module_tldr_sections_parse_v1(wire)
# consumed == -1, entries == []

# (b) truncated entry accepted, later sections silently dropped
val wire = module_tldr_sections_render_v1(["type|type A = 결a\nx", "const|val X = 1"])
val (entries, consumed) = module_tldr_sections_parse_v1(wire)
# consumed == 31 (wire is 60 bytes), entries == ["type|type A = 결a"]
```

In (b) the short byte range happens to end just before a newline that is part
of the body, so the record verifies; the scan then stops at the body's
remaining text (`x`), which does not start a record. The caller gets one
truncated entry, a positive `consumed`, and no sign that the `const` section
existed. A reader that looks for one section kind would report "absent".

Effect on the aspect sections: `aspect-decl|` and `join-point|` section texts
are byte-framed and sealed internally and contain no newline of their own, so a
truncated aspect section is rejected by its seal. But a non-ASCII body in any
EARLIER section of the same companion can drop the aspect entries as in (b),
and the aspect reader would then answer `miss: section-absent`, which for
`aspect-decl|` means "recompute", not "no advice". That is safe only as long
as no consumer treats an absent section as an empty one.

Fix direction: write `body.byte_len()`, bound the scan with `byte_len()`, and
make the reader reject input whose remaining text is neither empty nor the
expected next part; check every caller that uses the returned `consumed` as an
offset.

## 2. Generic template section (`generic_tldr_view_v1.spl`)

`_read_frame_v1` scans frame widths with `data.char_code_at(i)` where `i` is
bounded by `byte_len()` and the value is cut with `substring` (bytes).
`char_code_at` is **character** indexed on this seed
(`"결제:ab".char_code_at(2) == 58`, `byte_at(6) == 58`), and `_frame_v1` writes
`value.len()`. By reading, a non-ASCII value before a later frame is misread;
this second case was not reproduced with a run.
`aspect_decl_section_v1.spl` uses `byte_at` / `byte_len` / `substring` only and
has a non-ASCII round-trip scenario.
