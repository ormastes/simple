# scv_commit_parse_policy_spec

> Purpose: This spec proves SCV-IMPL-G-01 — the explicit-commit parse policy:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_commit_parse_policy_spec

Purpose: This spec proves SCV-IMPL-G-01 — the explicit-commit parse policy:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_commit_parse_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-G-01 — the explicit-commit parse policy:
supported source requires a LOCKED, AVAILABLE parser plus a successful parse
(no silent fallback green); unsupported text commits in `text_only` line
mode; binary content commits as bytes/chunks; a missing file is an honest
ERROR.
Audience: Maintainers of the SCV commit gates.

## Scenarios

### scv explicit-commit parse policy (G-01)

#### errors on a missing file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- errors on a missing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("errors on a missing file")
val root = _repo("missing")
val out = scv_commit_parse_policy(root, "{root}/nope.foo")
expect(out.starts_with("ERROR")).to_be(true)
```

</details>

#### classifies binary content as bytes/chunks

- classifies binary content as bytes/chunks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("classifies binary content as bytes/chunks")
val root = _repo("binary")
file_write_bytes("{root}/blob.bin", [1u8, 0u8, 2u8, 3u8])
val out = scv_commit_parse_policy(root, "{root}/blob.bin")
expect(out).to_contain("policy: binary")
expect(out).to_contain("mode: bytes-chunks")
```

</details>

#### classifies unsupported text as text_only line mode

- classifies unsupported text as text_only line mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("classifies unsupported text as text_only line mode")
val root = _repo("textonly")
file_write("{root}/notes.zzz", "plain notes\nno language\n")
val out = scv_commit_parse_policy(root, "{root}/notes.zzz")
expect(out).to_contain("policy: text_only")
expect(out).to_contain("mode: line")
```

</details>

#### refuses supported source without a locked available parser

- refuses supported source without a locked available parser
- A default-supported language (.py) with no locked parser is an ERROR


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses supported source without a locked available parser")
step("A default-supported language (.py) with no locked parser is an ERROR")
val root = _repo("noparser")
file_write("{root}/tool.py", "print('hello')\n")
val out = scv_commit_parse_policy(root, "{root}/tool.py")
expect(out.starts_with("ERROR")).to_be(true)
expect(out).to_contain("requires a locked available parser")
```

</details>

#### passes supported source with a locked parser and a clean parse

- passes supported source with a locked parser and a clean parse
- Install a locked parser for a mapped language, then classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("passes supported source with a locked parser and a clean parse")
step("Install a locked parser for a mapped language, then classify")
val root = _repo("parsed")
_fake_wasm("{root}/parser.wasm")
val installed = scv_parser_install(root, "foolang", "tree-sitter-foo", "1.0.0", "{root}/parser.wasm", "wasm32")
expect(installed.starts_with("parser-install")).to_be(true)
scv_langmap_set(root, "foo", "foolang", "tree-sitter-foo", "1.0.0")
file_write("{root}/main.foo", "block {\n  value\n}\n")
val out = scv_commit_parse_policy(root, "{root}/main.foo")
expect(out).to_contain("policy: parsed")
expect(out).to_contain("language: foolang")
expect(out).to_contain("parser: tree-sitter-foo@1.0.0")
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-COMMIT-PARSE-POLICY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ef15da9c2b9edc1b79142786b7746f08921ac215040698c37cd1dd1fad0780e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef15da9c2b9edc1b79142786b7746f08921ac215040698c37cd1dd1fad0780e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef15da9c2b9edc1b79142786b7746f08921ac215040698c37cd1dd1fad0780e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_commit_parse_policy_spec.spl
mirror: doc/06_spec/integration/app/scv_commit_parse_policy_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_commit_parse_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_commit_parse_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_commit_parse_policy_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_commit_parse_policy_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'errors on a missing file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_commit_parse_policy_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies binary content as bytes/chunks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_commit_parse_policy_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies unsupported text as text_only line mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
