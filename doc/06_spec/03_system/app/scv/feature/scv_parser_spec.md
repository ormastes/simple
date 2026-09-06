# Scv Parser Specification

> Tests covering REQ-008 REQ-009 parser index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Specification

## Scenarios

### REQ-008 REQ-009 parser index

#### records fallback syntax and semantic hashes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-008
# @req REQ-009
```

</details>

#### locks local WASM parser artifacts without executing them

- locks local WASM parser artifacts without executing them


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("locks local WASM parser artifacts without executing them")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-parser-install.XXXXXX)\nprintf '\\\\000asmx' > \"$TMP/parser.wasm\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install simple tree-sitter-simple 0.1.0 parser.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-verify\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parsers\n"
val out = _scv_parser_doc_script(script)
expect(out).to_contain("parser-install simple tree-sitter-simple 0.1.0")
expect(out).to_contain("parser-verify checked=1")
expect(out).to_contain("simple|tree-sitter-simple|0.1.0|wasm32|wasm|sha256_")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-008 REQ-009 parser index.
- REQ-008 REQ-009 parser index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-009`
- `REQ-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c2aba2bf0f84694e47931d7adce7586460491f13980898f8bc200f05d06439d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c2aba2bf0f84694e47931d7adce7586460491f13980898f8bc200f05d06439d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c2aba2bf0f84694e47931d7adce7586460491f13980898f8bc200f05d06439d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/scv/feature/scv_parser_spec.spl
mirror: doc/06_spec/03_system/app/scv/feature/scv_parser_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/scv/feature/scv_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/scv/feature/scv_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/scv/feature/scv_parser_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records fallback syntax and semantic hashes' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/scv/feature/scv_parser_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'locks local WASM parser artifacts without executing them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
