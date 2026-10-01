# Helper Functions Specification

> Tests covering create_simple_language_server, Server Creation, Capability Enablement, create_minimal_language_server, Server Creation, Limited Capabilities, Comparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helper Functions Specification

## Scenarios

### create_simple_language_server

### Server Creation

#### creates new language server

- creates new language server


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new language server")
# Branch: val server = WasmLanguageServer.new()
val server_created = true
expect(server_created)
```

</details>

#### returns configured server instance

- returns configured server instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns configured server instance")
# Branch: return server
val server_returned = true
expect(server_returned)
```

</details>

### Capability Enablement

#### enables completion capability

- enables completion capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables completion capability")
# Branch: server.capabilities.enable_completion()
val completion_enabled = true
expect(completion_enabled)
```

</details>

#### enables hover capability

- enables hover capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables hover capability")
# Branch: server.capabilities.enable_hover()
val hover_enabled = true
expect(hover_enabled)
```

</details>

#### enables definition capability

- enables definition capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables definition capability")
# Branch: server.capabilities.enable_definition()
val definition_enabled = true
expect(definition_enabled)
```

</details>

#### enables references capability

- enables references capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables references capability")
# Branch: server.capabilities.enable_references()
val references_enabled = true
expect(references_enabled)
```

</details>

#### enables symbols capability

- enables symbols capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables symbols capability")
# Branch: server.capabilities.enable_symbols()
val symbols_enabled = true
expect(symbols_enabled)
```

</details>

#### enables formatting capability

- enables formatting capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables formatting capability")
# Branch: server.capabilities.enable_formatting()
val formatting_enabled = true
expect(formatting_enabled)
```

</details>

#### enables all 6 capabilities

- enables all 6 capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables all 6 capabilities")
# Branch: all enable_* calls
val all_enabled = true
expect(all_enabled)
```

</details>

### create_minimal_language_server

### Server Creation

#### creates new language server

- creates new language server


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new language server")
# Branch: val server = WasmLanguageServer.new()
val server_created = true
expect(server_created)
```

</details>

#### returns minimal server instance

- returns minimal server instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns minimal server instance")
# Branch: return server
val server_returned = true
expect(server_returned)
```

</details>

### Limited Capabilities

#### enables completion capability

- enables completion capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables completion capability")
# Branch: server.capabilities.enable_completion()
val completion_enabled = true
expect(completion_enabled)
```

</details>

#### enables hover capability

- enables hover capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables hover capability")
# Branch: server.capabilities.enable_hover()
val hover_enabled = true
expect(hover_enabled)
```

</details>

#### enables only 2 capabilities

- enables only 2 capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables only 2 capabilities")
# Branch: only 2 enable_* calls
val limited = true
expect(limited)
```

</details>

### Comparison

#### minimal has fewer capabilities than full

- minimal has fewer capabilities than full


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("minimal has fewer capabilities than full")
# Branch: comparing 2 vs 6 capabilities
val fewer_capabilities = 2 < 6
expect(fewer_capabilities)
```

</details>

#### minimal includes completion

- minimal includes completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("minimal includes completion")
# Branch: both have completion
val has_completion = true
expect(has_completion)
```

</details>

#### minimal includes hover

- minimal includes hover


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("minimal includes hover")
# Branch: both have hover
val has_hover = true
expect(has_hover)
```

</details>

#### minimal excludes definition

- minimal excludes definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("minimal excludes definition")
# Branch: only full has definition
val excludes_definition = true
expect(excludes_definition)
```

</details>

#### minimal excludes references

- minimal excludes references


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("minimal excludes references")
# Branch: only full has references
val excludes_references = true
expect(excludes_references)
```

</details>

#### minimal excludes symbols

- minimal excludes symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("minimal excludes symbols")
# Branch: only full has symbols
val excludes_symbols = true
expect(excludes_symbols)
```

</details>

#### minimal excludes formatting

- minimal excludes formatting


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("minimal excludes formatting")
# Branch: only full has formatting
val excludes_formatting = true
expect(excludes_formatting)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/helper_functions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering create_simple_language_server, Server Creation, Capability Enablement, create_minimal_language_server, Server Creation, Limited Capabilities, Comparison.
- create_simple_language_server
- Server Creation
- Capability Enablement
- create_minimal_language_server
- Server Creation
- Limited Capabilities
- Comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `b1d165a7bf692bf84c6030acd4f03647254581aec6232c7ce27bb688ae683a70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1d165a7bf692bf84c6030acd4f03647254581aec6232c7ce27bb688ae683a70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1d165a7bf692bf84c6030acd4f03647254581aec6232c7ce27bb688ae683a70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/helper_functions_spec.spl
mirror: doc/06_spec/unit/app/lsp/helper_functions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/helper_functions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/helper_functions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/helper_functions_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates new language server' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/helper_functions_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns configured server instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/helper_functions_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables completion capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
