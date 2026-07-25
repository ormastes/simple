# Shared Multilingual Font Manifest

> Checks the selected CLDR ranking, immutable bundled assets, and complete sparse

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Multilingual Font Manifest

Checks the selected CLDR ranking, immutable bundled assets, and complete sparse

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the selected CLDR ranking, immutable bundled assets, and complete sparse
coverage matrix through the canonical Simple registry. No renderer or native
GPU claim is made here.

## Scenarios

### shared multilingual font manifest

#### should pin the CLDR source, selected top ten, and cutoff evidence

- Load the pinned multilingual font manifest
   - Expected: source.release equals `release-48-2`
   - Expected: source.tag_object equals `fc1fd058cc6f50544a450a3b15a4bba0e0c1e653`
   - Expected: source.source_commit equals `11299982335beb974c1c63c45265184e759c0f41`
   - Expected: source.supplemental_data_sha256 equals `font_bundle_pin_sha256(bundle_pins, CLDR_DATA)`
   - Expected: source.supplemental_metadata_sha256 equals `font_bundle_pin_sha256(bundle_pins, CLDR_METADATA)`
   - Expected: source.likely_subtags_sha256 equals `font_bundle_pin_sha256(bundle_pins, CLDR_LIKELY)`
   - Expected: package_sha256(path) equals `"sha256:" + font_bundle_pin_sha256(bundle_pins, path)`
   - Expected: source.license equals `Unicode-3.0`
   - Expected: selected.len() equals `10`
   - Expected: evidence.len() equals `11`
   - Expected: selected[0].language equals `en`
   - Expected: selected[8].language equals `ur`
   - Expected: selected[9].language equals `id`
   - Expected: evidence[10].language equals `bn`
- Regenerate the top eleven twice from the exact pinned XML bytes
   - Expected: rows.len() equals `1589`
   - Expected: row.contribution equals `expected_cldr_contribution(row)`
- fail
   - Expected: first_bytes equals `second_bytes`
   - Expected: first_bytes equals `file_read_text(CLDR_RANKING)`
   - Expected: first_rows[i].language equals `evidence[i].language`
   - Expected: first_rows[i].likely_script equals `evidence[i].likely_script`
   - Expected: first_rows[i].total equals `evidence[i].literate_functional_total`
- script totals = script totals + script script + "=" + script total to text
   - Expected: script_totals equals `evidence[i].script_totals`
- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(selected.len()).to_equal(10)
expect(evidence.len()).to_equal(11)
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
        expect(rows.len()).to_equal(1589)
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

- expect font bundle
   - Expected: package_sha256(FONT_CORPUS_PATH) equals `"sha256:" + corpus_sha256`
- expect font license
- var distribution bytes =
- file read bytes
- distribution bytes = distribution bytes + file read bytes
   - Expected: total_bytes equals `51764704`
   - Expected: distribution_paths.len() equals `57`
   - Expected: distribution_paths.len() + 2 equals `59`
   - Expected: distribution_bytes equals `53433272`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(total_bytes).to_equal(51764704)
expect(distribution_paths.len()).to_equal(57)
expect(distribution_paths.len() + 2).to_equal(59)
expect(distribution_bytes).to_equal(53433272)
expect(distribution_bytes).to_be_less_than(80 * 1024 * 1024 + 1)
```

</details>

#### should fail closed when a second selected face stales the first wrapper

- Reject a stale global-face wrapper after loading a second selected face
- fail
- first close
   - Expected: first.cache_identity() equals `sha256={first_asset.sha256};axes={first_asset.default_axes}`
- first close
- fail
- second close
   - Expected: second.cache_identity() equals `sha256={second_asset.sha256};axes={second_asset.default_axes}`
   - Expected: first.cache_identity() equals ``
   - Expected: first.layout_text("A", 24, 0).len() equals `0`
   - Expected: first.horizontal_kern(65, 86, 24) equals `0`
   - Expected: first.horizontal_line_metric(24, 0) equals `0`
- first close
- assert not equal
- second close
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        if first_loaded == nil:
            fail("font rasterizer dylib exists but selected face A could not load")
        var first = first_loaded.?
        defer:
            if first.lib_handle != 0:
                first.close()
        expect(first.is_current()).to_be(true)
        expect(first.cache_identity()).to_equal("sha256={first_asset.sha256};axes={first_asset.default_axes}")

        val second_loaded = FontRasterizer.load(dylib_path, second_asset.local_path)
        if second_loaded == nil:
            first.close()
            fail("font rasterizer dylib exists but selected face B could not load")
        var second = second_loaded.?
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
        expect(first.layout_text("A", 24, 0).len()).to_equal(0)
        expect(first.horizontal_kern(65, 86, 24)).to_equal(0)
        expect(first.horizontal_line_metric(24, 0)).to_equal(0)
        first.close()
        expect(second.is_current()).to_be(true)
        expect(second.has_glyph(65)).to_be(true)
        assert_not_equal(second.rasterize(65, 24), nil)
        second.close()
        exercised = true
if not dylib_available:
    fail("unavailable: no font rasterizer dylib exists; stale-wrapper evidence did not run")
expect(exercised).to_be(true)
```

</details>

#### should bind accepted-simple policy to the exact candidate corpus

- Check every candidate against its exact CORPUS codepoints and accepted-simple policy
- fail
   - Expected: accepted_simple equals `12`
   - Expected: candidate equals `4`
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness
- expect candidate witness


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(accepted_simple).to_equal(12)
expect(candidate).to_equal(4)
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

- Replay exact CORPUS mappings through the bounded Pure Simple glyf parser
- expect compound corpus


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replay exact CORPUS mappings through the bounded Pure Simple glyf parser")
expect_compound_corpus(setup_shared_font_fixture())
```

</details>

#### should preserve the separate Roboto Slab copyright notice

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val copyright_path = FONT_ASSET_ROOT + "apache/robotoslab/COPYRIGHT.txt"
expect(file_exists(copyright_path)).to_be(true)
val copyright_text = file_read_text(copyright_path)
expect(copyright_text.len()).to_be_greater_than(0)
expect(copyright_text).to_contain("Copyright 2018 The Roboto Slab Project Authors")
```

</details>

#### should provide one honest status for all one hundred sparse cells

- expect language coverage
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

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
