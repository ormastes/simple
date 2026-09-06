# Text For Iteration Lowering Source Specification

> Tests covering native text for-iteration lowering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text For Iteration Lowering Source Specification

## Scenarios

### native text for-iteration lowering

<details>
<summary>Advanced: splits text into Unicode characters before the counted loop</summary>

#### splits text into Unicode characters before the counted loop

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- splits text into Unicode characters before the counted loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("splits text into Unicode characters before the counted loop")
val source = file_read("src/compiler/50.mir/mir_lowering_stmts.spl")
expect(source).to_contain("if self.local_is_str(collection_local):")
expect(source).to_contain("val tagged_text = self.ensure_tagged_str(collection_local)")
expect(source).to_contain("MirConstValue.Str(\"rt_string_chars\")")
expect(source).to_contain("MirType(kind: MirTypeKind.Opaque(\"str\"))")
expect(source).to_contain("return self.lower_for_array_indexed(")
```

</details>


</details>

#### keeps unsupported non-text iterables loud

- keeps unsupported non-text iterables loud


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps unsupported non-text iterables loud")
val source = file_read("src/compiler/50.mir/mir_lowering_stmts.spl")
expect(source).to_contain("for-in over non-array iterables is not supported by native codegen yet (#143); iterate an array or use while")
```

</details>

#### rejects non-Unicode four-byte leaders in the hosted runtime

- rejects non-Unicode four-byte leaders in the hosted runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects non-Unicode four-byte leaders in the hosted runtime")
val source = file_read("src/runtime/runtime_native.c")
expect(source).to_contain("lead >= 0xf0 && lead <= 0xf4")
expect(source.contains("lead >= 0xf0 && lead <= 0xf7")).to_be(false)
```

</details>

#### keeps every baremetal character splitter codepoint-sized

- keeps every baremetal character splitter codepoint-sized


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every baremetal character splitter codepoint-sized")
val owners = [
    "examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c",
    "examples/09_embedded/simple_os/arch/x86_32/boot/baremetal_stubs.c",
    "examples/09_embedded/simple_os/arch/arm32/boot/baremetal_stubs.c",
    "examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c",
    "examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_stubs.c",
    "src/os/kernel/arch/riscv64/boot/freestanding_runtime.c"
]
for owner in owners:
    val source = file_read(owner)
    expect(source).to_contain("rt_string_chars(")
    expect(source).to_contain("lead >= 0xC2")
    expect(source).to_contain("lead >= 0xE0")
    expect(source).to_contain("lead >= 0xF0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native text for-iteration lowering.
- native text for-iteration lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e541163d3fe5e3b7ed7c1328e30776fdcb117b71aba5a865abd50797ae8d1a2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e541163d3fe5e3b7ed7c1328e30776fdcb117b71aba5a865abd50797ae8d1a2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e541163d3fe5e3b7ed7c1328e30776fdcb117b71aba5a865abd50797ae8d1a2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits text into Unicode characters before the counted loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps unsupported non-text iterables loud' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/text_for_iteration_lowering_source_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-Unicode four-byte leaders in the hosted runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
