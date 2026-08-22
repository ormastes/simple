# simpleos_font_bundle_spec

> Verifies the simpleos font bundle behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_font_bundle_spec

Verifies the simpleos font bundle behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/simpleos_font_bundle_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the simpleos font bundle behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS font legal bundle

#### should project the closed Google Fonts and legal payload without collisions

- Verify: should project the closed Google Fonts and legal payload without collisions
- Load the pinned multilingual font manifest
   - Expected: entries.len() equals `53)  # oracle: pinned constant asserted by this scenario`
   - Expected: ttf_entries equals `16)  # oracle: pinned constant asserted by this scenario`
   - Expected: metadata_entries equals `16)  # oracle: pinned constant asserted by this scenario`
   - Expected: google_entries equals `50)  # oracle: pinned constant asserted by this scenario`
   - Expected: cldr_license_entries equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: root_notice_entries equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: pinned_entries equals `51)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005
step("Verify: should project the closed Google Fonts and legal payload without collisions")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the pinned multilingual font manifest")
val entries = simpleos_font_bundle_entries()
expect(entries.len()).to_equal(53)  # oracle: pinned constant asserted by this scenario
var guest_paths = "|"
var short_names = "|"
var pinned_entries: i64 = 0
var ttf_entries: i64 = 0
var metadata_entries: i64 = 0
var google_entries: i64 = 0
var cldr_license_entries: i64 = 0
var root_notice_entries: i64 = 0
for entry in entries:
    expect(entry.guest_long_path).to_start_with("/SYS/FONTS/")
    expect(short_leaf_is_83(entry.guest_short_name)).to_be(true)
    expect(guest_paths.contains("|" + entry.guest_long_path + "|")).to_be(false)
    expect(short_names.contains("|" + entry.guest_short_name + "|")).to_be(false)
    guest_paths = guest_paths + entry.guest_long_path + "|"
    short_names = short_names + entry.guest_short_name + "|"
    if entry.source_path.ends_with(".ttf"): ttf_entries = ttf_entries + 1
    if entry.source_path.ends_with("/METADATA.pb"): metadata_entries = metadata_entries + 1
    if entry.source_path.starts_with("assets/fonts/google-fonts/"): google_entries = google_entries + 1
    if entry.source_path == "assets/fonts/cldr/release-48-2/LICENSE": cldr_license_entries = cldr_license_entries + 1
    if entry.source_path == "LICENSE" or entry.source_path == "THIRD_PARTY_NOTICES.md": root_notice_entries = root_notice_entries + 1
    if pin_match_count(entry.source_path) == 1: pinned_entries = pinned_entries + 1
expect(ttf_entries).to_equal(16)  # oracle: pinned constant asserted by this scenario
expect(metadata_entries).to_equal(16)  # oracle: pinned constant asserted by this scenario
expect(google_entries).to_equal(50)  # oracle: pinned constant asserted by this scenario
expect(cldr_license_entries).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(root_notice_entries).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(pinned_entries).to_equal(51)  # oracle: pinned constant asserted by this scenario
expect(guest_paths).to_contain("|/SYS/FONTS/NOTICES.MD|")
expect(_selected_font_bundle_asset_physical_path_from_root(
    "assets/fonts/google-fonts/CORPUS.sdn", "C:\\Simple\\"
)).to_equal("C:/Simple/assets/fonts/google-fonts/CORPUS.sdn")
expect(_selected_font_bundle_asset_physical_path_from_root(
    "THIRD_PARTY_NOTICES.md", "/opt/simple-package/"
)).to_equal("/opt/simple-package/THIRD_PARTY_NOTICES.md")
expect(_selected_font_bundle_asset_physical_path_from_root(
    "tmp/unmanaged.txt", "/opt/simple-package"
)).to_equal("tmp/unmanaged.txt")
```

</details>

#### should preserve font registry paths and exclude build-time CLDR evidence

- Verify: should preserve font registry paths and exclude build-time CLDR evidence
- Load the pinned multilingual font manifest
   - Expected: mono_long equals `/SYS/FONTS/NotoSansMono[wdth,wght].ttf`
   - Expected: mono_short equals `NOTOSANS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005
step("Verify: should preserve font registry paths and exclude build-time CLDR evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the pinned multilingual font manifest")
val entries = simpleos_font_bundle_entries()
var sources = "|"
var mono_long = ""
var mono_short = ""
for entry in entries:
    sources = sources + entry.source_path + "|"
    if entry.source_path.contains("notosansmono/") and entry.source_path.ends_with(".ttf"):
        mono_long = entry.guest_long_path
        mono_short = entry.guest_short_name
expect(mono_long).to_equal("/SYS/FONTS/NotoSansMono[wdth,wght].ttf")
expect(mono_short).to_equal("NOTOSANS")
expect(sources).to_contain("|assets/fonts/cldr/release-48-2/LICENSE|")
expect(sources.contains("supplementalData.xml")).to_be(false)
expect(sources.contains("supplementalMetadata.xml")).to_be(false)
expect(sources.contains("likelySubtags.xml")).to_be(false)
expect(sources.contains("/RANKING.sdn|")).to_be(false)
expect(sources.contains("/SOURCE.sdn|")).to_be(false)
expect(sources.contains("/TAG.txt|")).to_be(false)
```

</details>

#### should validate pinned bytes and reject missing or unpinned payloads

- Verify: should validate pinned bytes and reject missing or unpinned payloads
- Load the pinned multilingual font manifest
   - Expected: corpus.reason equals `valid`
- Reject missing and unmanaged payload sources
   - Expected: missing.reason equals `missing`
   - Expected: unpinned.reason equals `unpinned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005
step("Verify: should validate pinned bytes and reject missing or unpinned payloads")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the pinned multilingual font manifest")
val corpus = load_simpleos_font_bundle_entry(SimpleOsFontBundleEntry(
    source_path: "assets/fonts/google-fonts/CORPUS.sdn",
    guest_long_path: "/SYS/FONTS/CORPUS.SDN",
    guest_short_name: "CORPUS.SDN",
))
expect(corpus.valid).to_be(true)
expect(corpus.reason).to_equal("valid")
expect(corpus.data.len()).to_be_greater_than(0)

step("Reject missing and unmanaged payload sources")
val missing = load_simpleos_font_bundle_entry(SimpleOsFontBundleEntry(
    source_path: "/tmp/simpleos-font-bundle-does-not-exist",
    guest_long_path: "/SYS/FONTS/MISSING.LIC",
    guest_short_name: "MISSING.LIC",
))
expect(missing.valid).to_be(false)
expect(missing.reason).to_equal("missing")
val unpinned = load_simpleos_font_bundle_entry(SimpleOsFontBundleEntry(
    source_path: "test/01_unit/os/port/simpleos_font_bundle_spec.spl",
    guest_long_path: "/SYS/FONTS/UNPINNED.TXT",
    guest_short_name: "UNPINNED.TXT",
))
expect(unpinned.valid).to_be(false)
expect(unpinned.reason).to_equal("unpinned")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `46b04c9039240f0a5f372d853a9e0b253e2c13735115f0384a9e61c3f2cb65d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46b04c9039240f0a5f372d853a9e0b253e2c13735115f0384a9e61c3f2cb65d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46b04c9039240f0a5f372d853a9e0b253e2c13735115f0384a9e61c3f2cb65d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/port/simpleos_font_bundle_spec.spl
mirror: doc/06_spec/01_unit/os/port/simpleos_font_bundle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/port/simpleos_font_bundle_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/port/simpleos_font_bundle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/simpleos_font_bundle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/simpleos_font_bundle_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should project the closed Google Fonts and legal payload without collisions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/port/simpleos_font_bundle_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve font registry paths and exclude build-time CLDR evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/port/simpleos_font_bundle_spec.spl:111:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate pinned bytes and reject missing or unpinned payloads' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
