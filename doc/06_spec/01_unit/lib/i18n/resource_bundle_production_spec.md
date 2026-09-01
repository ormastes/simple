# resource_bundle_production_spec

> Exercises `std.i18n.bundle` directly. Placeholder fixtures are assembled from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# resource_bundle_production_spec

Exercises `std.i18n.bundle` directly. Placeholder fixtures are assembled from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/i18n/resource_bundle_production_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Production i18n resource-bundle coverage

Exercises `std.i18n.bundle` directly. Placeholder fixtures are assembled from
literal brace fragments so the Simple parser does not interpret them as source
interpolation.

## Scenarios

### production i18n parser

#### parses values, empty values, comments, and first-colon semantics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses values, empty values, comments, and first-colon semantics
   - Expected: parsed["greeting"] equals `Hello: world`
   - Expected: parsed["empty"] equals ``
   - Expected: parsed["spaced.key"] equals `값`
   - Expected: parsed.contains_key("invalid") is false
   - Expected: parsed.keys().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses values, empty values, comments, and first-colon semantics")
val content = "# comment\n\n greeting : Hello: world \nempty:\ninvalid\n spaced.key : 값 "
val parsed = parse_i18n_file(content)
expect(parsed["greeting"]).to_equal("Hello: world")
expect(parsed["empty"]).to_equal("")
expect(parsed["spaced.key"]).to_equal("값")
expect(parsed.contains_key("invalid")).to_equal(false)
expect(parsed.keys().len()).to_equal(3)
```

</details>

#### returns an empty dictionary for comments and blank lines

- returns an empty dictionary for comments and blank lines
   - Expected: parse_i18n_file("\n# only\n   \n").keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns an empty dictionary for comments and blank lines")
expect(parse_i18n_file("\n# only\n   \n").keys().len()).to_equal(0)
```

</details>

### production resource lookup

#### prefers locale values then fallback values

- prefers locale values then fallback values
   - Expected: bundle.get("greeting") equals `안녕하세요`
   - Expected: bundle.get("shared") equals `지역`
   - Expected: bundle.get("farewell") equals `Goodbye`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("prefers locale values then fallback values")
val bundle = production_bundle()
expect(bundle.get("greeting")).to_equal("안녕하세요")
expect(bundle.get("shared")).to_equal("지역")
expect(bundle.get("farewell")).to_equal("Goodbye")
```

</details>

#### returns an explicit missing marker

- returns an explicit missing marker
   - Expected: production_bundle().get("unknown") equals `{missing:unknown}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns an explicit missing marker")
expect(production_bundle().get("unknown")).to_equal("{missing:unknown}")
```

</details>

#### reports key presence across both dictionaries

- reports key presence across both dictionaries
   - Expected: bundle.has_key("greeting") is true
   - Expected: bundle.has_key("farewell") is true
   - Expected: bundle.has_key("unknown") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports key presence across both dictionaries")
val bundle = production_bundle()
expect(bundle.has_key("greeting")).to_equal(true)
expect(bundle.has_key("farewell")).to_equal(true)
expect(bundle.has_key("unknown")).to_equal(false)
```

</details>

#### merges keys without duplicating locale overrides

- merges keys without duplicating locale overrides
   - Expected: keys.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges keys without duplicating locale overrides")
val keys = production_bundle().keys()
expect(keys.len()).to_equal(5)
expect(keys).to_contain("greeting")
expect(keys).to_contain("farewell")
expect(keys).to_contain("shared")
```

</details>

#### returns the configured locale

- returns the configured locale
   - Expected: production_bundle().current_locale() equals `ko-KR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the configured locale")
expect(production_bundle().current_locale()).to_equal("ko-KR")
```

</details>

### production message substitution

#### substitutes multilingual arguments and repeated placeholders

- substitutes multilingual arguments and repeated placeholders
   - Expected: repeated.get_fmt("message", {"name": "김민수"}) equals `김민수 / 김민수`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("substitutes multilingual arguments and repeated placeholders")
val repeated = ResourceBundle(
    locale: "en",
    messages: {"message": placeholder("name") + " / " + placeholder("name")},
    fallback_messages: {})
expect(repeated.get_fmt("message", {"name": "김민수"})).to_equal("김민수 / 김민수")
```

</details>

#### leaves undeclared placeholders unchanged

- leaves undeclared placeholders unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves undeclared placeholders unchanged")
expect(production_bundle().get_fmt("welcome", {})).to_equal(
    "환영합니다, " + placeholder("name") + "!")
```

</details>

#### formats fallback messages

- formats fallback messages
   - Expected: production_bundle().get_fmt("count", {"count": "٣"}) equals `٣ files`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats fallback messages")
expect(production_bundle().get_fmt("count", {"count": "٣"})).to_equal("٣ files")
```

</details>

### production locale helpers

#### extracts language from region and script forms

- extracts language from region and script forms
   - Expected: _language_from_locale("ko_KR") equals `ko`
   - Expected: _language_from_locale("zh-Hant") equals `zh`
   - Expected: _language_from_locale("ja") equals `ja`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts language from region and script forms")
expect(_language_from_locale("ko_KR")).to_equal("ko")
expect(_language_from_locale("zh-Hant")).to_equal("zh")
expect(_language_from_locale("ja")).to_equal("ja")
```

</details>

#### normalizes surrounding whitespace without changing identity

- normalizes surrounding whitespace without changing identity
   - Expected: _normalize_locale("  ko-KR  ") equals `ko-KR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes surrounding whitespace without changing identity")
expect(_normalize_locale("  ko-KR  ")).to_equal("ko-KR")
```

</details>

#### extracts LANG values and platform fallbacks

- extracts LANG values and platform fallbacks
   - Expected: _extract_lang_code("en_US.UTF-8") equals `en`
   - Expected: _extract_lang_code("ko-KR.EUC-KR") equals `ko`
   - Expected: _extract_lang_code("C") equals `en`
   - Expected: _extract_lang_code("POSIX") equals `en`
   - Expected: _extract_lang_code("  ") equals `en`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts LANG values and platform fallbacks")
expect(_extract_lang_code("en_US.UTF-8")).to_equal("en")
expect(_extract_lang_code("ko-KR.EUC-KR")).to_equal("ko")
expect(_extract_lang_code("C")).to_equal("en")
expect(_extract_lang_code("POSIX")).to_equal("en")
expect(_extract_lang_code("  ")).to_equal("en")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-I18N`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `51fecc93cfdbd9744dd72202ccb5db9bd539d168364f02c8c3a2568717c3ac19`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51fecc93cfdbd9744dd72202ccb5db9bd539d168364f02c8c3a2568717c3ac19`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51fecc93cfdbd9744dd72202ccb5db9bd539d168364f02c8c3a2568717c3ac19`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/i18n/resource_bundle_production_spec.spl
mirror: doc/06_spec/01_unit/lib/i18n/resource_bundle_production_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/i18n/resource_bundle_production_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/i18n/resource_bundle_production_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/i18n/resource_bundle_production_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/i18n/resource_bundle_production_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/i18n/resource_bundle_production_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses values, empty values, comments, and first-colon semantics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/i18n/resource_bundle_production_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an empty dictionary for comments and blank lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/i18n/resource_bundle_production_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers locale values then fallback values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
