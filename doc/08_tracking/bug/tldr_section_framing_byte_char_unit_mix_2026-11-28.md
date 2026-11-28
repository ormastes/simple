# TLDR section framing mixes character and byte counts

**Found:** 2026-11-28, aspect plan stage AW-1/AW-2 (seed `simple-local-20261128f`).
**Status:** open. Not fixed in the AW-1/AW-2 change (wire-format change of an existing reader).

## 1. Module TLDR companion record (`module_tldr_sections_v1.spl`)

`module_tldr_sections_render_v1` writes `section: <kind> <body.len()>` — a
**character** count. `module_tldr_sections_parse_v1` cuts the body with
`rest.substring(body_start, body_start + count)` — a **byte** range. One
non-ASCII character in any section body makes the whole companion unreadable:

```simple
val wire = module_tldr_sections_render_v1(["const|val X = 결제", "type|type A = i64"])
val (entries, consumed) = module_tldr_sections_parse_v1(wire)
# consumed == -1, entries == []
```

Effect: fail closed (the TLDR is a miss), never a wrong section. It reaches the
`aspect-decl|` and `join-point|` sections when a handler name, selector,
attribute or path is not ASCII; those sections are byte-framed internally and
round trip on their own.

Fix direction: write `body.byte_len()` and bound the scan with `byte_len()`;
check every caller that uses the returned `consumed` as an offset.

## 2. Generic template section (`generic_tldr_view_v1.spl`)

`_read_frame_v1` scans frame widths with `data.char_code_at(i)` where `i` is
bounded by `byte_len()` and the value is cut with `substring` (bytes).
`char_code_at` is **character** indexed on this seed
(`"결제:ab".char_code_at(2) == 58`, `byte_at(6) == 58`), and `_frame_v1` writes
`value.len()`. By reading, a non-ASCII value before a later frame is misread; this second case was not reproduced with a run.
`aspect_decl_section_v1.spl` uses `byte_at` / `byte_len` / `substring` only and
has a non-ASCII round-trip scenario.
