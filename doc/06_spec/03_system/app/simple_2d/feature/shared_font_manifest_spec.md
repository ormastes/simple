# Shared Multilingual Font Manifest

> Verifies the shared font manifest behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Multilingual Font Manifest

Verifies the shared font manifest behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the shared font manifest behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### shared multilingual font manifest

#### should pin the CLDR source, selected top ten, and cutoff evidence

- Verify: should pin the CLDR source, selected top ten, and cutoff evidence
- Load the pinned multilingual font manifest
   - Expected: source.release equals `release-48-2`
   - Expected: source.tag_object equals `fc1fd058cc6f50544a450a3b15a4bba0e0c1e653`
   - Expected: source.source_commit equals `11299982335beb974c1c63c45265184e759c0f41`
   - Expected: source.supplemental_data_sha256 equals `font_bundle_pin_sha256(bundle_pins, CLDR_DATA)`
   - Expected: source.supplemental_metadata_sha256 equals `font_bundle_pin_sha256(bundle_pins, CLDR_METADATA)`
   - Expected: source.likely_subtags_sha256 equals `font_bundle_pin_sha256(bundle_pins, CLDR_LIKELY)`
   - Expected: package_sha256(path) equals `"sha256:" + font_bundle_pin_sha256(bundle_pins, path)`
   - Expected: source.license equals `Unicode-3.0`
   - Expected: selected.len() equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: evidence.len() equals `11)  # oracle: pinned constant asserted by this scenario`
   - Expected: selected[0].language equals `en`
   - Expected: selected[8].language equals `ur`
   - Expected: selected[9].language equals `id`
   - Expected: evidence[10].language equals `bn`
- Regenerate the top eleven twice from the exact pinned XML bytes
   - Expected: rows.len() equals `1589)  # oracle: pinned constant asserted by this scenario`
   - Expected: row.contribution equals `expected_cldr_contribution(row)`
   - Expected: first_bytes equals `second_bytes`
   - Expected: first_bytes equals `file_read_text(CLDR_RANKING)`
   - Expected: first_rows[i].language equals `evidence[i].language`
   - Expected: first_rows[i].likely_script equals `evidence[i].likely_script`
   - Expected: first_rows[i].total equals `evidence[i].literate_functional_total`
   - Expected: script_totals equals `evidence[i].script_totals`


<details>
<summary>Executable SSpec</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-009 REQ-008 REQ-003
step("Verify: should pin the CLDR source, selected top ten, and cutoff evidence")
step("Load the pinned multilingual font manifest")
val source = selected_font_language_ranking_source()
val bundle_pins = selected_font_bundle_asset_pins()
val selected = selected_font_language_ranks()
val evidence = font_language_ranking_evidence()
expect(source.release).to_equal("release-48-2")
expect(source.tag_object).to_equal("fc1fd058cc6f50544a450a3b15a4bba0e0c1e653")
expect(source.source_commit).to_equal("11299982335beb974c1c63c45265184e759c0f41")
expect(source.supplemental_data_sha256).to_equal(font_bundle_pin_sha256(bundle_pins, CLDR_DATA))
expect(source.supplemental_metadata_sha256).to_equal(font_bundle_pin_sha256(bundle_pins, CLDR_METADATA))
expect(source.likely_subtags_sha256).to_equal(font_bundle_pin_sha256(bundle_pins, CLDR_LIKELY))
for path in [CLDR_DATA, CLDR_METADATA, CLDR_LIKELY, CLDR_ROOT + "LICENSE", CLDR_ROOT + "TAG.txt", CLDR_ROOT + "SOURCE.sdn", CLDR_RANKING]:
    expect(package_sha256(path)).to_equal("sha256:" + font_bundle_pin_sha256(bundle_pins, path))
expect(file_read_text(CLDR_ROOT + "TAG.txt")).to_contain("object " + source.source_commit)
expect(source.license).to_equal("Unicode-3.0")
expect(selected.len()).to_equal(10)  # oracle: pinned constant asserted by this scenario
expect(evidence.len()).to_equal(11)  # oracle: pinned constant asserted by this scenario
expect(selected[0].language).to_equal("en")
expect(selected[8].language).to_equal("ur")
expect(selected[9].language).to_equal("id")
expect(evidence[10].language).to_equal("bn")
expect(selected[9].literate_functional_total).to_be_greater_than(evidence[10].literate_functional_total)

step("Regenerate the top eleven twice from the exact pinned XML bytes")
val population_xml = file_read_text(CLDR_DATA)
val metadata_xml = file_read_text(CLDR_METADATA)
val likely_xml = file_read_text(CLDR_LIKELY)
val first = cldr_rank_languages(population_xml, metadata_xml, likely_xml)
val second = cldr_rank_languages(population_xml, metadata_xml, likely_xml)
val contributions = cldr_scan_language_population(population_xml)
match contributions:
    case Ok(rows):
        expect(rows.len()).to_equal(1589)  # oracle: pinned constant asserted by this scenario
        for row in rows:
            expect(row.contribution).to_equal(expected_cldr_contribution(row))
    case Err(message):
        fail("pinned CLDR contribution replay failed: {message}")
match first:
    case Ok(first_rows):
        match second:
            case Ok(second_rows):
                val first_bytes = cldr_serialize_language_totals(first_rows, 11)
                val second_bytes = cldr_serialize_language_totals(second_rows, 11)
                expect(first_bytes).to_equal(second_bytes)
                expect(first_bytes).to_equal(file_read_text(CLDR_RANKING))
                var i: i64 = 0
                while i < 11:
                    expect(first_rows[i].language).to_equal(evidence[i].language)
                    expect(first_rows[i].likely_script).to_equal(evidence[i].likely_script)
                    expect(first_rows[i].total).to_equal(evidence[i].literate_functional_total)
                    var script_totals = ""
                    var j: i64 = 0
                    while j < first_rows[i].script_totals.len():
                        if j > 0:
                            script_totals = script_totals + ","
                        val script = first_rows[i].script_totals[j]
                        script_totals = script_totals + script.script + "=" + script.total.to_text()
                        j = j + 1
                    expect(script_totals).to_equal(evidence[i].script_totals)
                    i = i + 1
            case Err(message):
                fail("second pinned CLDR regeneration failed: {message}")
    case Err(message):
        fail("first pinned CLDR regeneration failed: {message}")
```

</details>

#### should verify every immutable bundled font and adjacent notice

- Verify: should verify every immutable bundled font and adjacent notice
   - Expected: package_sha256(FONT_CORPUS_PATH) equals `"sha256:" + corpus_sha256`
   - Expected: total_bytes equals `51764704)  # oracle: pinned constant asserted by this scenario`
   - Expected: distribution_paths.len() equals `57)  # oracle: pinned constant asserted by this scenario`
   - Expected: distribution_paths.len() + 2 equals `59)  # oracle: pinned constant asserted by this scenario`
   - Expected: distribution_bytes equals `53433279)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-008 REQ-003
step("Verify: should verify every immutable bundled font and adjacent notice")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val assets = setup_shared_font_fixture()
val bundle_pins = selected_font_bundle_asset_pins()
val corpus_sha256 = font_bundle_pin_sha256(bundle_pins, FONT_CORPUS_PATH)
val corpus_ref = FONT_CORPUS_PATH + "#sha256:" + corpus_sha256
expect_font_bundle(bundle_pins)
expect(file_exists(FONT_CORPUS_PATH)).to_be(true)
expect(package_sha256(FONT_CORPUS_PATH)).to_equal("sha256:" + corpus_sha256)
var total_bytes: i64 = 0
var paths = "|"
var hashes = "|"
for asset in assets:
    expect_font_license(asset, corpus_ref)
    expect(paths.contains("|" + asset.upstream_path + "|")).to_be(false)
    expect(hashes.contains("|" + asset.sha256 + "|")).to_be(false)
    paths = paths + asset.upstream_path + "|"
    hashes = hashes + asset.sha256 + "|"
    total_bytes = total_bytes + asset.byte_len
val distribution_paths = dir_walk("assets/fonts")
var distribution_bytes = (file_read_bytes("LICENSE").len() +
    file_read_bytes("THIRD_PARTY_NOTICES.md").len())
for path in distribution_paths:
    distribution_bytes = distribution_bytes + file_read_bytes(path).len()
expect(total_bytes).to_equal(51764704)  # oracle: pinned constant asserted by this scenario
expect(distribution_paths.len()).to_equal(57)  # oracle: pinned constant asserted by this scenario
expect(distribution_paths.len() + 2).to_equal(59)  # oracle: pinned constant asserted by this scenario
expect(distribution_bytes).to_equal(53433279)  # oracle: pinned constant asserted by this scenario
expect(distribution_bytes).to_be_less_than(80 * 1024 * 1024 + 1)
```

</details>

#### should fail closed when a second selected face stales the first wrapper

- Verify: should fail closed when a second selected face stales the first wrapper
- Reject a stale global-face wrapper after loading a second selected face
   - Expected: first.cache_identity() equals `sha256={first_asset.sha256};axes={first_asset.default_axes}`
   - Expected: second.cache_identity() equals `sha256={second_asset.sha256};axes={second_asset.default_axes}`
   - Expected: first.cache_identity() equals ``
   - Expected: first.layout_text("A", 24, 0).len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: first.horizontal_kern(65, 86, 24) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: first.horizontal_line_metric(24, 0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-009 REQ-008 REQ-003
step("Verify: should fail closed when a second selected face stales the first wrapper")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject a stale global-face wrapper after loading a second selected face")
val assets = setup_shared_font_fixture()
val first_asset = assets[13]
val second_asset = assets[14]
var dylib_available = false
var exercised = false
for dylib_path in browser_font_dylib_candidates():
    if file_exists(dylib_path) and not exercised:
        dylib_available = true
        val first_loaded = FontRasterizer.load(dylib_path, first_asset.local_path)
        if first_loaded.loaded_generation <= 0:
            fail("font rasterizer dylib exists but selected face A could not load")
        var first = first_loaded
        defer:
            if first.lib_handle != 0:
                first.close()
        expect(first.is_current()).to_be(true)
        expect(first.cache_identity()).to_equal("sha256={first_asset.sha256};axes={first_asset.default_axes}")

        val second_loaded = FontRasterizer.load(dylib_path, second_asset.local_path)
        if second_loaded.loaded_generation <= 0:
            first.close()
            fail("font rasterizer dylib exists but selected face B could not load")
        var second = second_loaded
        defer:
            if second.lib_handle != 0:
                second.close()
        expect(second.is_current()).to_be(true)
        expect(second.cache_identity()).to_equal("sha256={second_asset.sha256};axes={second_asset.default_axes}")
        expect(first.is_current()).to_be(false)
        expect(first.cache_identity()).to_equal("")
        expect(first.has_glyph(65)).to_be(false)
        expect(first.rasterize(65, 24)).to_be_nil()
        expect(first.rasterize_subpixel(65, 24)).to_be_nil()
        expect(first.layout_text("A", 24, 0).len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
        expect(first.horizontal_kern(65, 86, 24)).to_equal(0)  # oracle: pinned constant asserted by this scenario
        expect(first.horizontal_line_metric(24, 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
        first.close()
        expect(second.is_current()).to_be(true)
        expect(second.has_glyph(65)).to_be(true)
        expect(second.rasterize(65, 24) == nil).to_be(false)
        second.close()
        exercised = true
if not dylib_available:
    fail("unavailable: no font rasterizer dylib exists; stale-wrapper evidence did not run")
expect(exercised).to_be(true)
```

</details>

#### should bind accepted-simple policy to the exact candidate corpus

- Verify: should bind accepted-simple policy to the exact candidate corpus
- Check every candidate against its exact CORPUS codepoints and accepted-simple policy
   - Expected: accepted_simple equals `12)  # oracle: pinned constant asserted by this scenario`
   - Expected: candidate equals `4)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-009 REQ-003
step("Verify: should bind accepted-simple policy to the exact candidate corpus")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Check every candidate against its exact CORPUS codepoints and accepted-simple policy")
val assets = setup_shared_font_fixture()
var accepted_simple: i64 = 0
var candidate: i64 = 0
for asset in assets:
    if asset.coverage_state.starts_with("accepted-simple:"):
        accepted_simple = accepted_simple + 1
    elif asset.coverage_state.starts_with("candidate:"):
        candidate = candidate + 1
    else:
        fail("unknown coverage state: " + asset.coverage_state)
expect(accepted_simple).to_equal(12)  # oracle: pinned constant asserted by this scenario
expect(candidate).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect_candidate_witness(assets, "Noto Sans SC", "English中文EspañolfrançaisPortuguêsРусскийIndonesia")
expect_candidate_witness(assets, "Noto Sans Devanagari", "EnglishEspañolहिन्दीfrançaisPortuguêsIndonesia")
expect_candidate_witness(assets, "Noto Sans Arabic", "EnglishEspañolالعربيةfrançaisPortuguêsاردوIndonesia")
expect_candidate_witness(assets, "Noto Sans Bengali", "বাংলা")
expect_candidate_witness(assets, "Noto Serif SC", "English中文EspañolfrançaisPortuguêsРусскийIndonesia")
expect_candidate_witness(assets, "Noto Serif Devanagari", "EnglishEspañolहिन्दीfrançaisPortuguêsIndonesia")
expect_candidate_witness(assets, "Noto Naskh Arabic", "EnglishEspañolالعربيةfrançaisPortuguêsاردوIndonesia")
expect_candidate_witness(assets, "Noto Serif Bengali", "বাংলা")
expect_candidate_witness(assets, "Noto Sans Mono", "EnglishEspañolfrançaisPortuguêsРусскийIndonesia")
expect_candidate_witness(assets, "Bungee", "EnglishEspañolfrançaisPortuguêsIndonesia")
expect_candidate_witness(assets, "Nunito", "EnglishEspañolfrançaisPortuguêsРусскийIndonesia")
expect_candidate_witness(assets, "Caveat", "EnglishEspañolfrançaisPortuguêsРусскийIndonesia")
expect_candidate_witness(assets, "Roboto Slab", "EnglishEspañolfrançaisPortuguêsРусскийIndonesia")
expect_candidate_witness(assets, "UnifrakturCook", "EnglishEspañolfrançaisPortuguêsIndonesia")
expect_candidate_witness(assets, "Pixelify Sans", "EnglishEspañolfrançaisPortuguêsРусскийIndonesia")
expect_candidate_witness(assets, "Noto Emoji", "😀")
```

</details>

#### should reconstruct every compound outline reached by exact corpus mappings

- Verify: should reconstruct every compound outline reached by exact corpus mappings
- Replay exact CORPUS mappings through the bounded Pure Simple glyf parser


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-009 REQ-008 REQ-003
step("Verify: should reconstruct every compound outline reached by exact corpus mappings")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Replay exact CORPUS mappings through the bounded Pure Simple glyf parser")
expect_compound_corpus(setup_shared_font_fixture())
```

</details>

#### should preserve the separate Roboto Slab copyright notice

- Verify: should preserve the separate Roboto Slab copyright notice


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-009 REQ-008
step("Verify: should preserve the separate Roboto Slab copyright notice")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val copyright_path = FONT_ASSET_ROOT + "apache/robotoslab/COPYRIGHT.txt"
expect(file_exists(copyright_path)).to_be(true)
val copyright_text = file_read_text(copyright_path)
expect(copyright_text.len()).to_be_greater_than(0)
expect(copyright_text).to_contain("Copyright 2018 The Roboto Slab Project Authors")
```

</details>

#### should provide one honest status for all one hundred sparse cells

- Verify: should provide one honest status for all one hundred sparse cells
   - Expected: cells[10].status equals `native`
   - Expected: cells[10].witness_family equals `Noto Sans SC`
   - Expected: cells[31].status equals `unavailable`
   - Expected: cells[32].status equals `fallback`
   - Expected: cells[32].witness_family equals `Noto Sans Devanagari`
   - Expected: cells[41].status equals `unavailable`
   - Expected: cells[42].status equals `fallback`
   - Expected: cells[42].witness_family equals `Noto Sans Arabic`
   - Expected: cells[73].status equals `not-designed-for-script`
   - Expected: cells[81].status equals `unavailable`
   - Expected: cells[82].status equals `fallback`
   - Expected: cells[82].witness_family equals `Noto Sans Arabic`
   - Expected: cells[9].status equals `native`
   - Expected: cells[9].witness_family equals `Noto Emoji`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-009 REQ-008 REQ-003
step("Verify: should provide one honest status for all one hundred sparse cells")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cells = selected_font_coverage_matrix()
expect_language_coverage(cells)
expect(cells[10].status).to_equal("native")
expect(cells[10].witness_family).to_equal("Noto Sans SC")
expect(cells[31].status).to_equal("unavailable")
expect(cells[32].status).to_equal("fallback")
expect(cells[32].witness_family).to_equal("Noto Sans Devanagari")
expect(cells[41].status).to_equal("unavailable")
expect(cells[42].status).to_equal("fallback")
expect(cells[42].witness_family).to_equal("Noto Sans Arabic")
expect(cells[73].status).to_equal("not-designed-for-script")
expect(cells[81].status).to_equal("unavailable")
expect(cells[82].status).to_equal("fallback")
expect(cells[82].witness_family).to_equal("Noto Sans Arabic")
expect(cells[9].status).to_equal("native")
expect(cells[9].witness_family).to_equal("Noto Emoji")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed7220c29b28d3506f41ade539d13bcc068cca5da4deda0c8abdbab066da7ef0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed7220c29b28d3506f41ade539d13bcc068cca5da4deda0c8abdbab066da7ef0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed7220c29b28d3506f41ade539d13bcc068cca5da4deda0c8abdbab066da7ef0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/shared_font_manifest_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/shared_font_manifest_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/shared_font_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/shared_font_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl:296:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin the CLDR source, selected top ten, and cutoff evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl:366:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should verify every immutable bundled font and adjacent notice' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl:399:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed when a second selected face stales the first wrapper' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl:451:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind accepted-simple policy to the exact candidate corpus' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl:486:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reconstruct every compound outline reached by exact corpus mappings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl:494:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the separate Roboto Slab copyright notice' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
