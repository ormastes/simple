# i18n_cli_branch_spec

> Focused behavior and branch matrix for the legacy Simple i18n CLI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# i18n_cli_branch_spec

Focused behavior and branch matrix for the legacy Simple i18n CLI.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/i18n/i18n_cli_branch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused behavior and branch matrix for the legacy Simple i18n CLI.

## Scenarios

### i18n CLI branch matrix

#### removes every logging option form and its split value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- removes every logging option form and its split value
- Verify flags, key-value options, and ordinary arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("removes every logging option form and its split value")
step("Verify flags, key-value options, and ordinary arguments")
expect(clean_args(["extract", "--human", "--json", "--tui", "--stdout",
    "--quiet", "--verbose", "--dots", "--count", "--no-progress",
    "--log-mode", "llm", "--surface", "stderr", "--progress", "count",
    "--log-mode=json", "--surface=stdout", "--progress=dots",
    "--dir=src", "--output=out"])).to_equal(
        ["extract", "--dir=src", "--output=out"])
```

</details>

#### classifies identifier characters and rejects punctuation and Unicode

- classifies identifier characters and rejects punctuation and Unicode
- Verify all ASCII identifier ranges and fallthrough


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("classifies identifier characters and rejects punctuation and Unicode")
step("Verify all ASCII identifier ranges and fallthrough")
expect(is_ident_char("a")).to_be(true)
expect(is_ident_char("Z")).to_be(true)
expect(is_ident_char("5")).to_be(true)
expect(is_ident_char("_")).to_be(true)
expect(is_ident_char("-")).to_be(false)
expect(is_ident_char("한")).to_be(false)
```

</details>

#### extracts keys lines escapes and ignores malformed patterns

- extracts keys lines escapes and ignores malformed patterns
- Verify scanner success, escaping, unterminated input, and empty key
   - Expected: found.len() equals `2`
   - Expected: found[0].key equals `Welcome`
   - Expected: found[0].default_text equals `Hello`
   - Expected: found[0].line equals `1`
   - Expected: found[1].key equals `Prefix_Key`
   - Expected: found[1].default_text equals `A \\"quote\\"`
   - Expected: found[1].line equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts keys lines escapes and ignores malformed patterns")
step("Verify scanner success, escaping, unterminated input, and empty key")
val source = "Welcome_\"Hello\"\n" +
    "val x = Prefix_Key_\"A \\\"quote\\\"\"\n" +
    "_\"empty key\"\n" +
    "Broken_\"unterminated\n" +
    "val ordinary = \"not localized\""
val found = extract_i18n_strings(source, "fixture.spl")
expect(found.len()).to_equal(2)
expect(found[0].key).to_equal("Welcome")
expect(found[0].default_text).to_equal("Hello")
expect(found[0].line).to_equal(1)
expect(found[1].key).to_equal("Prefix_Key")
expect(found[1].default_text).to_equal("A \\\"quote\\\"")
expect(found[1].line).to_equal(2)
```

</details>

#### deduplicates catalogs and locale templates by stable key

- deduplicates catalogs and locale templates by stable key
- Verify first occurrence wins and output stays deterministic


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("deduplicates catalogs and locale templates by stable key")
step("Verify first occurrence wins and output stays deterministic")
val catalog = generate_locale_catalog(fixture_strings())
expect(catalog).to_contain("Welcome, \"Hello\", a.spl, 1")
expect(catalog.contains("Duplicate")).to_be(false)
expect(catalog).to_contain("Farewell, \"Bye\", b.spl, 3")
val template = generate_locale_template("ko-KR", fixture_strings())
expect(template).to_contain("# Locale: ko-KR")
expect(template).to_contain("Welcome = \"Hello\"")
expect(template.contains("Duplicate")).to_be(false)
```

</details>

#### handles missing empty and populated source directories

- handles missing empty and populated source directories
- Verify filesystem errors, no-message success, and generated artifacts
   - Expected: handle_extract("build/test/i18n_cli_branch/missing", OUTPUT_DIR) equals `1`
   - Expected: handle_generate("ko-KR", "build/test/i18n_cli_branch/missing", OUTPUT_DIR) equals `1`
   - Expected: handle_extract(EMPTY_FIXTURE_DIR, OUTPUT_DIR) equals `0`
   - Expected: handle_generate("ko-KR", EMPTY_FIXTURE_DIR, OUTPUT_DIR) equals `0`
   - Expected: handle_extract(POPULATED_FIXTURE_DIR, OUTPUT_DIR) equals `0`
   - Expected: handle_generate("ko-KR", POPULATED_FIXTURE_DIR, OUTPUT_DIR) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles missing empty and populated source directories")
step("Verify filesystem errors, no-message success, and generated artifacts")
expect(handle_extract("build/test/i18n_cli_branch/missing", OUTPUT_DIR)).to_equal(1)
expect(handle_generate("ko-KR", "build/test/i18n_cli_branch/missing", OUTPUT_DIR)).to_equal(1)
dir_create(EMPTY_FIXTURE_DIR, true)
file_write("{EMPTY_FIXTURE_DIR}/ignore.txt", "Ignored_\"Not Simple\"")
file_write("{EMPTY_FIXTURE_DIR}/empty.spl", "val ordinary = \"plain\"")
expect(handle_extract(EMPTY_FIXTURE_DIR, OUTPUT_DIR)).to_equal(0)
expect(handle_generate("ko-KR", EMPTY_FIXTURE_DIR, OUTPUT_DIR)).to_equal(0)
dir_create(POPULATED_FIXTURE_DIR, true)
file_write("{POPULATED_FIXTURE_DIR}/ignore.txt", "Ignored_\"Not Simple\"")
file_write("{POPULATED_FIXTURE_DIR}/messages.spl", "Welcome_\"안녕하세요\"\nFarewell_\"Bye\"")
expect(handle_extract(POPULATED_FIXTURE_DIR, OUTPUT_DIR)).to_equal(0)
expect(handle_generate("ko-KR", POPULATED_FIXTURE_DIR, OUTPUT_DIR)).to_equal(0)
expect(file_exists("{OUTPUT_DIR}/strings.sdn")).to_be(true)
expect(file_exists("{OUTPUT_DIR}/__init__.ko-KR.spl")).to_be(true)
expect(file_read("{OUTPUT_DIR}/strings.sdn")).to_contain("Welcome")
expect(file_read("{OUTPUT_DIR}/strings.sdn")).to_contain("안녕하세요")
expect(file_read("{OUTPUT_DIR}/__init__.ko-KR.spl")).to_contain("안녕하세요")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-TEXT-I18N-CLI-001`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8f7eeec9a1a892ccdd9f5cd9f791adc08148fec5fc6234ab35daebd76d8e7ce6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f7eeec9a1a892ccdd9f5cd9f791adc08148fec5fc6234ab35daebd76d8e7ce6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f7eeec9a1a892ccdd9f5cd9f791adc08148fec5fc6234ab35daebd76d8e7ce6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/i18n/i18n_cli_branch_spec.spl
mirror: doc/06_spec/01_unit/app/i18n/i18n_cli_branch_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/i18n/i18n_cli_branch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/i18n/i18n_cli_branch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/i18n/i18n_cli_branch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/i18n/i18n_cli_branch_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/i18n/i18n_cli_branch_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes every logging option form and its split value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/i18n/i18n_cli_branch_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies identifier characters and rejects punctuation and Unicode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/i18n/i18n_cli_branch_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts keys lines escapes and ignores malformed patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
