# text_advanced escape_json aliased-import regression

> `src/lib/common/text_advanced.spl` delegated `escape_json` to

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# text_advanced escape_json aliased-import regression

`src/lib/common/text_advanced.spl` delegated `escape_json` to

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-TEXT-ADV-ESCAPE-JSON |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/text_advanced_escape_json_alias_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`src/lib/common/text_advanced.spl` delegated `escape_json` to
`use std.text.{escape_json as _shared_escape_json}`. The aliased binding is
dropped when the module is reached through a wildcard re-export chain
(`use app.cli.query_visibility.*`), so the whole CLI died with
`error[E1002]: function `_shared_escape_json` not found` (rc=1, empty stdout).
Direct imports of the module resolved fine, which is why it stayed hidden.

Doc: doc/08_tracking/bug/text_advanced_aliased_import_dropped_escape_json_2026-08-17.md

## Scenarios

### text_advanced.escape_json

#### the function resolves and escapes correctly

#### escapes a double quote

- escapes a double quote
   - Expected: escape_json("a\"b") equals `a\\"b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes a double quote")
expect(escape_json("a\"b")).to_equal("a\\\"b")
```

</details>

#### escapes a backslash

- escapes a backslash
   - Expected: escape_json("a\\b") equals `a\\\\b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes a backslash")
expect(escape_json("a\\b")).to_equal("a\\\\b")
```

</details>

#### escapes newline, carriage return and tab

- escapes newline, carriage return and tab
   - Expected: escape_json("a\nb") equals `a\\nb`
   - Expected: escape_json("a\rb") equals `a\\rb`
   - Expected: escape_json("a\tb") equals `a\\tb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes newline, carriage return and tab")
expect(escape_json("a\nb")).to_equal("a\\nb")
expect(escape_json("a\rb")).to_equal("a\\rb")
expect(escape_json("a\tb")).to_equal("a\\tb")
```

</details>

#### leaves a clean string untouched

- leaves a clean string untouched
   - Expected: escape_json("plain text") equals `plain text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a clean string untouched")
expect(escape_json("plain text")).to_equal("plain text")
```

</details>

#### the CLI module graph resolves every symbol

#### query_visibility runs without an unresolved-function error

- query_visibility runs without an unresolved-function error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query_visibility runs without an unresolved-function error")
val r = shell("bin/simple run src/app/cli/query_visibility.spl symbols src/lib/common/text.spl --requester src/lib/common/text.spl 2>&1")
expect(r.stdout.contains("E1002")).to_be_false()
expect(r.stdout.contains("not found")).to_be_false()
```

</details>

#### no owned stdlib module keeps an unusable aliased self-import

- no owned stdlib module keeps an unusable aliased self-import


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no owned stdlib module keeps an unusable aliased self-import")
# Generalises the defect class: any `use ... as NAME` in a module
# that also declares the un-aliased name is the shape that broke.
val r = shell("/usr/bin/grep -rn 'escape_json as ' src/lib/ 2>&1; true")
expect(r.stdout.contains("escape_json as ")).to_be_false()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `12f3116d394aa3026922658d209c65b4ad2312977b0b43235170e82a395b57a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `12f3116d394aa3026922658d209c65b4ad2312977b0b43235170e82a395b57a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `12f3116d394aa3026922658d209c65b4ad2312977b0b43235170e82a395b57a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/text_advanced_escape_json_alias_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_advanced_escape_json_alias_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_advanced_escape_json_alias_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_advanced_escape_json_alias_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_advanced_escape_json_alias_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes a double quote' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_advanced_escape_json_alias_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes a backslash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_advanced_escape_json_alias_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes newline, carriage return and tab' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
