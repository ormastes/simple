# Sfnt Specification

> Tests covering default glyf sfnt validation, sfnt manifest names, sfnt name-table decode on a real staged font.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sfnt Specification

## Scenarios

### default glyf sfnt validation

#### accepts static/default-variable fonts and rejects malformed or excluded data

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts static/default-variable fonts and rejects malformed or excluded data
   - Expected: result.reason equals `scenario.3`
   - Expected: result.reason equals `unsupported-sfnt-table`
   - Expected: validate_default_glyf_font(_sfnt([(1668112752, [1u8])])).reason equals `missing-required-table`
   - Expected: read_fixed_1616([255u8, 255u8, 0u8, 0u8], 0) equals `-1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts static/default-variable fonts and rejects malformed or excluded data")
val static_font = _valid_font([])
val variable_font = _valid_font([(1719034226, _valid_fvar())])
var out_of_range = static_font
out_of_range = _set_u32_be(out_of_range, 20, out_of_range.len() + 1)
var duplicate = static_font
duplicate = _set_u32_be(duplicate, 28, 1735162214)
var directory_overlap = static_font
directory_overlap = _set_u32_be(directory_overlap, 20, 12)
var table_overlap = static_font
table_overlap = _set_u32_be(table_overlap, 36, read_u32_be(table_overlap, 20))
val fvar_base = read_u32_be(variable_font, 12 + 7 * 16 + 8) as i64
var malformed_fvar = variable_font
malformed_fvar = _set_u16_be(malformed_fvar, fvar_base + 10, 19)
var malformed_fvar_header = variable_font
malformed_fvar_header = _set_u16_be(malformed_fvar_header, fvar_base + 6, 0)
val cases: [(text, [u8], bool, text)] = [
    ("static glyf", static_font, true, "supported-default-glyf"),
    ("default variable glyf", variable_font, true, "supported-default-glyf"),
    ("out-of-range table", out_of_range, false, "invalid-sfnt-directory"),
    ("duplicate table", duplicate, false, "invalid-sfnt-directory"),
    ("directory overlap", directory_overlap, false, "invalid-sfnt-directory"),
    ("table overlap", table_overlap, false, "invalid-sfnt-directory"),
    ("missing glyf", _sfnt([(1668112752, [1u8])]), false, "missing-required-table"),
    ("excluded CFF2", _valid_font([(1128678962, [1u8])]), false, "unsupported-sfnt-table"),
    ("malformed fvar", malformed_fvar, false, "invalid-fvar-default"),
    ("malformed fvar header", malformed_fvar_header, false, "invalid-fvar-default")
]
# `case` cannot be a binding name here: the parser reserves it
# unconditionally, so `for case in …` fails the whole file with
# "expected pattern, found Case" before any example runs. See
# doc/08_tracking/bug/case_is_reserved_outside_match_2026-08-04.md.
for scenario in cases:
    val result = validate_default_glyf_font(scenario.1)
    expect(result.supported).to_be(scenario.2)
    expect(result.reason).to_equal(scenario.3)
    expect(font_runtime_ttf_default_supported(scenario.1)).to_be(scenario.2)
val excluded: [i64] = [1128678944, 1128678962, 1129270354, 1129333068, 1398163232, 1128416340, 1128418371, 1161970772, 1161972803, 1161974595, 1935829368, 1650745716, 1651273571]
for tag in excluded:
    val result = validate_default_glyf_font(_valid_font([(tag, [1u8])]))
    expect(result.supported).to_be(false)
    expect(result.reason).to_equal("unsupported-sfnt-table")
expect(validate_default_glyf_font(_sfnt([(1668112752, [1u8])])).reason).to_equal("missing-required-table")
expect(parse_offset_table(out_of_range)).to_be_nil()
expect(read_fixed_1616([255u8, 255u8, 0u8, 0u8], 0)).to_equal(-1.0)
expect(sfnt_manifest_tables_match(static_font, "cmap,glyf,head,hhea,hmtx,loca,maxp")).to_be(true)
expect(sfnt_manifest_tables_match(static_font, "cmap,glyf")).to_be(false)
expect(sfnt_manifest_default_axes_match(static_font, "static")).to_be(true)
expect(sfnt_manifest_default_axes_match(variable_font, "wght=400")).to_be(true)
```

</details>

#### accepts only the unchanged default font instance

- accepts only the unchanged default font instance
   - Expected: validate_glyf_font_instance(static_font, "wght=400").reason equals `unsupported-variation-instance`
   - Expected: validate_glyf_font_instance(variable_font, "wght=500").reason equals `unsupported-variation-instance`
   - Expected: validate_glyf_font_instance(variable_font, "static").reason equals `unsupported-variation-instance`
   - Expected: validate_glyf_font_instance(_valid_font([(1128678962, [1u8])]), "static").reason equals `unsupported-sfnt-table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only the unchanged default font instance")
val static_font = _valid_font([])
val variable_font = _valid_font([(1719034226, _valid_fvar())])
expect(validate_glyf_font_instance(static_font, "static").supported).to_be(true)
expect(validate_glyf_font_instance(static_font, "wght=400").reason).to_equal("unsupported-variation-instance")
expect(validate_glyf_font_instance(variable_font, "wght=400").supported).to_be(true)
expect(validate_glyf_font_instance(variable_font, "wght=500").reason).to_equal("unsupported-variation-instance")
expect(validate_glyf_font_instance(variable_font, "static").reason).to_equal("unsupported-variation-instance")
expect(validate_glyf_font_instance(_valid_font([(1128678962, [1u8])]), "static").reason).to_equal("unsupported-sfnt-table")
```

</details>

### sfnt manifest names

#### matches preferred bounded Windows English names and rejects malformed records

- matches preferred bounded Windows English names and rejects malformed records


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches preferred bounded Windows English names and rejects malformed records")
val fallback = _sfnt([(1851878757, _name_table([
    (1, "Simple Sans"), (2, "Regular"), (4, "Simple Sans Regular"),
    (6, "SimpleSans-Regular"), (5, "Version 1.0")
]))])
expect(sfnt_manifest_names_match(fallback, "Simple Sans", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(true)
val preferred = _name_table([
    (1, "Legacy"), (16, "Simple Sans"), (2, "Roman"), (17, "Regular"),
    (4, "Simple Sans Regular"), (6, "SimpleSans-Regular"), (5, "Version 1.0")
])
val valid = _sfnt([(1851878757, preferred)])
expect(sfnt_manifest_names_match(valid, "Simple Sans", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(true)
val unicode = _replace_name_units(valid, 1, [0x4E2D, 0xD83D, 0xDE00])
expect(sfnt_manifest_names_match(unicode, 0x4E2D.chr() + 0x1F600.chr(), "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(true)
val lone_high = _replace_name_units(valid, 1, [0xD800])
expect(sfnt_manifest_names_match(lone_high, "", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(false)
val lone_low = _replace_name_units(valid, 1, [0xDC00])
expect(sfnt_manifest_names_match(lone_low, "", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(false)
val bad_pair = _replace_name_units(valid, 1, [0xD800, 0x0041])
expect(sfnt_manifest_names_match(bad_pair, "", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(false)
val missing = _sfnt([(1851878757, _name_table([(1, "Simple Sans"), (2, "Regular")]))])
expect(sfnt_manifest_names_match(missing, "Simple Sans", "Regular", "", "", "")).to_be(false)
var truncated = valid
val name_base = read_u32_be(truncated, 20) as i64
truncated = _set_u16_be(truncated, name_base + 6 + 10, preferred.len())
expect(sfnt_manifest_names_match(truncated, "Simple Sans", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(false)
var odd = valid
odd = _set_u16_be(odd, name_base + 6 + 8, 1)
expect(sfnt_manifest_names_match(odd, "Simple Sans", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(false)
var early_storage = valid
early_storage = _set_u16_be(early_storage, name_base + 4, 6)
expect(sfnt_manifest_names_match(early_storage, "Simple Sans", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(false)
val conflict = _sfnt([(1851878757, _name_table([
    (16, "Simple Sans"), (16, "Other Sans"), (17, "Regular"),
    (4, "Simple Sans Regular"), (6, "SimpleSans-Regular"), (5, "Version 1.0")
]))])
expect(sfnt_manifest_names_match(conflict, "Simple Sans", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(false)
val style_conflict = _sfnt([(1851878757, _name_table([
    (16, "Simple Sans"), (17, "Regular"), (17, "Bold"),
    (4, "Simple Sans Regular"), (6, "SimpleSans-Regular"), (5, "Version 1.0")
]))])
expect(sfnt_manifest_names_match(style_conflict, "Simple Sans", "Regular", "Simple Sans Regular", "SimpleSans-Regular", "Version 1.0")).to_be(false)
```

</details>

### sfnt name-table decode on a real staged font

#### decodes the five manifest name slots for the checked-in NotoSansMono variable font

- decodes the five manifest name slots for the checked-in NotoSansMono variable font
   - Expected: blob.len() equals `1708408`
   - Expected: decoded equals `|Noto Sans Mono|Regular|Noto Sans Mono Regular|NotoSansMono-Regular|Version 2... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes the five manifest name slots for the checked-in NotoSansMono variable font")
# Hermetic regression for the desktop boot decode bug: all five slots
# (family/style/full/postscript/version) previously read back as the
# same nameID-5 version string ("Version 2.014" x5) on the freestanding
# native lane. The font is checked into the repo, so this needs no VFS
# boot and no network fetch.
val blob = file_read_bytes("assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf")
expect(blob.len()).to_equal(1708408)
val decoded = sfnt_debug_selected_names(blob)
expect(decoded).to_equal("|Noto Sans Mono|Regular|Noto Sans Mono Regular|NotoSansMono-Regular|Version 2.014")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/sfnt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering default glyf sfnt validation, sfnt manifest names, sfnt name-table decode on a real staged font.
- default glyf sfnt validation
- sfnt manifest names
- sfnt name-table decode on a real staged font

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42cfcc2c8ba6eaaeee32963b8dacda6c3dd012c4c7da79542ca9833553e8ea2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42cfcc2c8ba6eaaeee32963b8dacda6c3dd012c4c7da79542ca9833553e8ea2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42cfcc2c8ba6eaaeee32963b8dacda6c3dd012c4c7da79542ca9833553e8ea2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/encoding/sfnt_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/sfnt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/sfnt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/sfnt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/sfnt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/encoding/sfnt_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts static/default-variable fonts and rejects malformed or excluded data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/sfnt_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only the unchanged default font instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/sfnt_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches preferred bounded Windows English names and rejects malformed records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
