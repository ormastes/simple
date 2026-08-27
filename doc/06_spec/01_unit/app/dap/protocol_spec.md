# Protocol Specification

> Tests covering Source, SourceBreakpoint, Breakpoint, StackFrame, Scope, Variable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Specification

## Scenarios

### Source

#### creates source with path via Source.new()

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates source with path via Source.new()


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates source with path via Source.new()")
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("fn new(path: String) -> Source:")
expect(protocol).to_contain("Source(name: nil, path: Some(path))")
```

</details>

#### exposes an optional display name field

- exposes an optional display name field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes an optional display name field")
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("name: Option<String>")
expect(protocol).to_contain("path: Option<String>")
```

</details>

### SourceBreakpoint

#### parses a source breakpoint line from the request JSON

- parses a source breakpoint line from the request JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a source breakpoint line from the request JSON")
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("fn from_json(data: Dict) -> Result<SourceBreakpoint, String>:")
expect(protocol).to_contain("val line = data.get(\"line\")?")
```

</details>

#### parses an optional condition from the request JSON

- parses an optional condition from the request JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses an optional condition from the request JSON")
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("val condition = data.get_optional(\"condition\")")
```

</details>

### Breakpoint

#### creates a breakpoint carrying the requested verified flag

- creates a breakpoint carrying the requested verified flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a breakpoint carrying the requested verified flag")
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("fn new(id: Int, verified: Bool, line: Int) -> Breakpoint:")
expect(protocol).to_contain("verified: verified,")
```

</details>

#### models verified/unverified via a plain Bool field, not a separate type

- models verified/unverified via a plain Bool field, not a separate type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("models verified/unverified via a plain Bool field, not a separate type")
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("verified: Bool")
expect(protocol).to_contain("line: Option<Int>")
```

</details>

### StackFrame

#### creates stack frame

- creates stack frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates stack frame")
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("fn new(id: Int, name: String, line: Int, column: Int) -> StackFrame:")
expect(protocol).to_contain("source: nil,")
```

</details>

#### creates stack frame with source

- creates stack frame with source


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates stack frame with source")
# NOTE: the stub described "with module information", but StackFrame
# has no module field -- the real builder attaches a Source, not a
# module. Asserting the real with_source() builder instead.
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("fn with_source(source: Source) -> StackFrame:")
expect(protocol).to_contain("source: Some(source),")
```

</details>

### Scope

#### creates local scope

- creates local scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates local scope")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("protocol.Scope.new(\"Local\", 1)")
```

</details>

#### creates arguments scope

- creates arguments scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates arguments scope")
# KNOWN GAP: handle_scopes only ever emits Local/Global/Registers
# scopes -- there is no distinct "Arguments" Scope anywhere in the
# DAP server, even though handle_variables' scope==2 comment
# acknowledges "arguments" semantics for remote backends. Asserting
# the described behaviour honestly so this fails until a real
# Arguments scope is added.
# See doc/08_tracking/bug/dap_spec_stubs_reported_green_without_asserting_2026-08-08.md
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("protocol.Scope.new(\"Arguments\"")
```

</details>

#### creates global scope

- creates global scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates global scope")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("protocol.Scope.new(\"Global\", 2)")
```

</details>

### Variable

#### creates simple variable

- creates simple variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple variable")
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("fn new(name: String, value: String) -> DapVariable:")
expect(protocol).to_contain("variables_reference: 0")
```

</details>

#### creates variable with children

- creates variable with children


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates variable with children")
# KNOWN GAP: dap_handlers.spl's handle_variables calls
# pvar.with_children(...) on a protocol.DapVariable, but DapVariable
# never defines with_children() -- only the unrelated
# dap_types.VariableInfo class does. Asserting the described
# behaviour on the real DapVariable class so this fails honestly
# until DapVariable grows its own with_children() (or the caller is
# fixed to use a method that exists).
# See doc/08_tracking/bug/dap_spec_stubs_reported_green_without_asserting_2026-08-08.md
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")
expect(protocol).to_contain("fn with_children(variables_reference: Int) -> DapVariable:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Source, SourceBreakpoint, Breakpoint, StackFrame, Scope, Variable.
- Source
- SourceBreakpoint
- Breakpoint
- StackFrame
- Scope
- Variable

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `789ceea3fa797763c6bb12188bcf0d1b85e5b29796dfe2eff9f864db9637855f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `789ceea3fa797763c6bb12188bcf0d1b85e5b29796dfe2eff9f864db9637855f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `789ceea3fa797763c6bb12188bcf0d1b85e5b29796dfe2eff9f864db9637855f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/dap/protocol_spec.spl
mirror: doc/06_spec/01_unit/app/dap/protocol_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/dap/protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/dap/protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/dap/protocol_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates source with path via Source.new()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/protocol_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes an optional display name field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/protocol_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a source breakpoint line from the request JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
