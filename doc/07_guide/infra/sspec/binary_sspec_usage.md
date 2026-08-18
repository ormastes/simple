# Binary SSpec Usage Guide

Practical guide to the binary/bitfield evidence infra in
`src/lib/common/spec/evidence/format/binary_layout.spl` (432 lines). This is
the **implemented** surface (mask-aware comparator + stacked word table) that
today's specs actually call — not the frozen `reference Type` / `.to_binary()`
authoring sugar described in the design doc, which has not landed yet. See
`doc/05_design/infra/sspec/binary_reference_stacked_design.md` for the target
surface and `doc/03_plan/infra/binary_runtime_hardening/plan.md` (Wave 2) for
where this sits in the larger initiative.

## When to use word-table evidence vs plain `assert_equal`

Use `BinaryLayout` + `compare_word` when a value is a **packed multi-field
word** (protocol header, register, cipher block, capability token) where:
- a failure needs to name *which field* broke, not just "values differ"
  (`compare_word` returns `WordDiff.failing_fields`, `binary_layout.spl:359-363`);
- some bits are legitimately don't-care per call site (`policy_dont_care`,
  `binary_layout.spl:310-311`) while others (reserved) must never be ignored;
  a plain `assert_equal` can't express that asymmetry;
- you want a human-readable stacked reference table
  (`stacked_rows`/`stacked_compare_rows`, lines 406/417) instead of a raw hex
  diff.

Use plain `assert_equal`/`assert_true` for scalar values, opaque byte blobs
compared whole (e.g. `gzip_decompress(z) == nil` in
`binary_domains_spec.spl:142`), or single-field values with no bit structure.

## Defining a layout

```
val layout = BinaryLayout(
    layout_id: "tcp_w3_fixture",
    total_bits: 32,
    byte_order: ByteOrder.big,       # little | big | unspecified
    bit_order: BitOrder.lsb0,        # lsb0 | msb0 | unspecified
    fields: [
        binary_field("window", 0, 16, "receive window"),   # name, lsb, width, description
        binary_field("flags", 16, 6, "TCP flags"),
        reserved_field("reserved", 22, 6),                 # name, lsb, width — always reserved:true
        binary_field("data_offset", 28, 4, "header length in words")
    ],
    source_ref: "RFC 9293 fixture"    # cite the spec/kernel file this mirrors
)
```

Fields: `struct BinaryFieldSpec { name, lsb, width, reserved, description }`
(`binary_layout.spl:54-59`). `binary_field(...)` sets `reserved: false`;
`reserved_field(name, lsb, width)` sets `reserved: true` and
`description: "reserved"` (lines 61-65).

**`ByteOrder.unspecified` / `BitOrder.unspecified` are validation failures,
not defaults.** `layout_errors` (lines 88-107) rejects an unspecified order,
a field whose `lsb + width` exceeds `total_bits`, non-positive width, and
overlapping fields (`fields_overlap`, line 81-82: `not (a.lsb+a.width <= b.lsb
or b.lsb+b.width <= a.lsb)`). `decode_u64` calls `layout_errors` first and
returns a `canonical_evidence_parse_error` instead of decoding on any
violation (`binary_layout.spl:204-207`) — an invalid layout fails closed, it
does not silently decode garbage.

## Mask policy semantics — exact precedence (verify against `compare_word`)

`compare_word(expected, actual, layout, policies) -> WordDiff`, implemented
`binary_layout.spl:340-372`. Per-field policy defaults to `"exact"`
(`_policy_for`, line 328) when no `ComparePolicy` entry names that field.

Policy kinds (`ComparePolicy { field, policy, mask }`, lines 302-314):
- `policy_exact(field)` → `"exact"`
- `policy_dont_care(field)` → `"dont_care"`
- `policy_masked(field, mask)` → `"masked"`, field-relative `mask`
- there is no `policy_reserved_*` constructor — reserved status comes only
  from the layout's `reserved_field`, never from a policy the caller passes.

**Precedence rule, exactly as coded (lines 343-357), evaluated per field in
layout order:**
1. `pol = _policy_for(field.name, policies)` — the caller's requested policy,
   default `"exact"`.
2. `if field.reserved: pol = "reserved_zero"` (line 346-347) — **this
   unconditionally overrides step 1**. A `reserved_field` in the layout is
   ALWAYS compared as `reserved_zero`, even if the caller passed
   `policy_dont_care(that_field)` or `policy_masked(...)`. Locked by spec
   `binary_compare_spec.spl:61-63` ("reserved overrides a dont_care request").
3. `if pol == "dont_care": continue` (line 348-349) — contributes **zero**
   bits to `compare_mask`; the field cannot fail regardless of value.
4. `if pol == "masked": compare_mask |= (mask << lsb) & field_bits` (350-351)
   — only the caller-selected sub-bits (field-relative) are added to the mask.
5. else (`"exact"` or `"reserved_zero"` or `"reserved_one"`):
   `compare_mask |= field_bits` (352-353) — the whole field is checked.
6. `if pol == "reserved_zero": effective_expected &= ~field_bits` (354-355)
   — the expected value in that range is forced to 0 regardless of what the
   caller passed as `expected`, so ANY nonzero actual bit in a reserved field
   fails, even if `expected` also carried that bit set (locked by
   `binary_compare_spec.spl:50-59`: "checks reserved bits even when expected
   also has them set" — a naive XOR would pass, `reserved_zero` does not).
7. `if pol == "reserved_one": effective_expected |= field_bits` — symmetric,
   forces expected to all-ones in that range.

Final: `delta = (actual XOR effective_expected) AND compare_mask` (line 358).
`status`: `"ignored"` if `compare_mask == 0` (a genuinely all-dont_care word,
not merely a passing one — `binary_compare_spec.spl:71-92`), else `"pass"` if
`delta == 0`, else `"fail"` (line 364). `failing_fields` is recomputed by
re-walking fields and checking `(delta & field_bits) != 0` (lines 360-363) —
it is **field-precision even under `masked`**, i.e. a masked sub-bit mismatch
still reports the whole field name, not just the failing bit.

**Summary table (precedence high → low):**
| condition | effective policy | mask contribution | expected forced |
|---|---|---|---|
| `field.reserved == true` | `reserved_zero` (always) | full field | expected&~field |
| explicit `policy_dont_care` (non-reserved) | `dont_care` | none | — |
| explicit `policy_masked(mask)` | `masked` | `mask` bits only | — |
| explicit `policy_exact` or no entry | `exact` | full field | — |

## Reading a `stacked_compare_rows` failure

`stacked_compare_rows(diffs, layout, word_label, first_word)` (line 417-432)
produces, per word: one compact line via `render_word_line` (line 376-385) —
`"W0 expected 0x... actual 0x... FAIL [flags]"` (fields comma-joined) or
`"...ok"` / `"...~ don't care"` for pass/ignored. **On `status == "fail"`
only**, it appends two more rows: `"  expected  <bits>"` and
`"  actual    <bits>"` from `_bin_group` (8-bit-grouped binary, line
395-403), then `"  ^ FAIL in: <names>"`. A passing or ignored word never
expands — only the failing word gets the bit-level breakdown, so a long
stacked table stays short except at the actual defect.

`stacked_rows(values, word_label, first_word)` (line 406-413) is the
plain reference-only form (no expected/actual, no diff) — one line per word,
`"<label><index>  0x<le-bytes-hex>"`.

## Domain recipes

- **Protocol header** — one `BinaryLayout` per header word, `byte_order:
  ByteOrder.big` for network order; `reserved_field` for RFC-reserved bit
  ranges so an unexpected flag surfaces as a named FAIL, not silence. Worked
  example: `test/01_unit/lib/common/spec/evidence/binary_domains_spec.spl`
  `tcp_word_layout()` (lines 31-44) — see also `binary_layout_spec.spl` in
  the same directory for the layout-validity/decode path.
- **Cipher KAT** — pack the known-answer ciphertext into one or more 64-bit
  `BinaryLayout` words (e.g. `ct_hi`/`ct_lo` 32-bit halves), compare with
  `compare_word` against the NIST/RFC vector, and separately assert a single
  flipped bit produces `status == "fail"` with a nonempty `failing_fields` —
  this proves the comparator, not just the crypto, catches corruption.
  Worked example: `binary_domains_spec.spl` AES-128-OFB block (lines 76-104,
  NIST SP 800-38A F.4.1).
- **Checksum/compression** — when the artifact is an opaque byte stream
  (gzip container) rather than a fixed bitfield word, `BinaryLayout` doesn't
  apply; assert on the whole-buffer contract instead (roundtrip equality,
  `gzip_validate`, `gzip_decompress(...) == nil` on corruption). Worked
  example: `binary_domains_spec.spl` compression block (lines 109-143) — note
  the recorded bug there, `gzip_validate` is structural-only and does not
  catch a corrupted deflate body; only `gzip_decompress` returning `nil` on
  CRC mismatch is load-bearing (see
  `doc/08_tracking/bug/gzip_validate_structural_only_no_crc_2026-08-18.md`).
- **Register dump** — mirror the real bitfield accessor file in `source_ref`
  (never hand-invent field boundaries) and cover all bits, including
  reserved ranges, so `layout_errors` sees `total_bits` fully accounted for.
  Reference example: `pte_layout()` (`binary_layout.spl:265-281`), which
  mirrors `src/os/kernel/types/bitfield.spl` field-for-field including two
  reserved gaps.
- **Parallel domains landing alongside this guide**: protocol (UDP/IPv4),
  algorithm (SHA-256/CRC32), and embedded (register bit-table) domain suites
  are being added concurrently in
  `test/01_unit/lib/common/spec/evidence/` by sibling sessions under this
  same plan; at the time of writing only `binary_compare_spec.spl` and
  `binary_domains_spec.spl` (protocol/cipher/compression) exist in that
  directory — check that directory listing for newly landed files before
  assuming a specific path exists.

## Pitfalls (verified against source, not assumed)

- **Word width is fixed at 64 bits for the hex/binary renderers.**
  `u64_to_le_bytes` always emits exactly 8 bytes regardless of
  `layout.total_bits` (`binary_layout.spl:167-173`), and `render_word_line`
  hex-renders through it unconditionally (line 378-379). A 16-bit or 32-bit
  layout still prints as a zero-padded 64-bit hex value in
  `render_word_line`'s expected/actual — only `_bin_group(value,
  layout.total_bits)` (used by `stacked_compare_rows`'s expanded bit rows)
  respects the layout's actual width. Don't read the top zero bytes of a
  narrow-word `render_word_line` output as meaningful.
- **`binary_field_table`'s hex column truncates wide fields.** The doc
  comment on `field_value_hex` (lines 228-230) states this explicitly: a
  40-bit field like `phys_addr` renders as `ceil(width/8)` bytes computed
  from the field's OWN width, so a 40-bit field is fine (5 bytes), but any
  reader assuming a fixed byte width across rows is wrong — row width varies
  per field.
- **Endianness only affects the declared metadata field, not the
  extraction math.** `field_extract`/`field_insert` (lines 137-143) operate
  purely on the `i64` value's bit positions via shift/mask — `byte_order`
  and `bit_order` are recorded as decoded evidence nodes (`decode_u64`, lines
  210-213) but are **not consulted** by `field_extract`, `compare_word`, or
  any renderer in this file. If your source bytes are big-endian on the wire,
  you must pack them into the `i64` value yourself before calling
  `compare_word` (see `pack_word`'s big-endian pack helper in
  `binary_domains_spec.spl:17-24`) — the layout's `byte_order` field
  documents intent but performs no conversion.
- **`reserved_field` cannot be made lenient at a call site.** There is no
  escape hatch (no `policy_reserved_zero`/`ignore` override reaches a
  `reserved: true` field) — see precedence rule step 2 above. If a field is
  sometimes legitimately nonzero, it must not be declared `reserved` in the
  layout; make it an ordinary `binary_field` with an explicit policy per call.
- **`ignored` status requires `compare_mask == 0` across the WHOLE word**,
  not per-field — a word with one `dont_care` field and one `exact` field
  that happens to match still reports `"pass"`, not `"ignored"`
  (`binary_compare_spec.spl:71-92` isolates this with a reserved-free layout
  specifically to get a true `compare_mask == 0`).
