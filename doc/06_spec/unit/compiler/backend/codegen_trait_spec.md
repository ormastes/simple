# Codegen Trait Specification

> Tests covering CodegenOutputKind concepts, CodegenOutput patterns, CodegenFactory backend mapping, Codegen adapter target support.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codegen Trait Specification

## Scenarios

### CodegenOutputKind concepts

#### has four output kinds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has four output kinds
   - Expected: kinds.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has four output kinds")
val kinds = ["ObjectCode", "TextSource", "AcceleratorCode", "InterpretedResult"]
expect(kinds.len()).to_equal(4)
```

</details>

#### ObjectCode is for native compilation

- ObjectCode is for native compilation
   - Expected: kind equals `ObjectCode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ObjectCode is for native compilation")
val kind = "ObjectCode"
expect(kind).to_equal("ObjectCode")
```

</details>

#### TextSource is for C/transpiled output

- TextSource is for C/transpiled output
   - Expected: kind equals `TextSource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TextSource is for C/transpiled output")
val kind = "TextSource"
expect(kind).to_equal("TextSource")
```

</details>

#### InterpretedResult is for interpreter mode

- InterpretedResult is for interpreter mode
   - Expected: kind equals `InterpretedResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("InterpretedResult is for interpreter mode")
val kind = "InterpretedResult"
expect(kind).to_equal("InterpretedResult")
```

</details>

### CodegenOutput patterns

#### text output has name and source

- text output has name and source
   - Expected: name equals `test_module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text output has name and source")
val name = "test_module"
val source = "int main() {}"
expect(name).to_equal("test_module")
expect(source).to_contain("main")
```

</details>

#### object output has name and bytes

- object output has name and bytes
   - Expected: name equals `native_mod`
   - Expected: bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("object output has name and bytes")
val name = "native_mod"
val bytes = [0x7f, 0x45, 0x4c, 0x46]
expect(name).to_equal("native_mod")
expect(bytes.len()).to_equal(4)
```

</details>

#### interpreted output has only name

- interpreted output has only name
   - Expected: name equals `interp_mod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpreted output has only name")
val name = "interp_mod"
expect(name).to_equal("interp_mod")
```

</details>

### CodegenFactory backend mapping

#### maps backend names correctly

- maps backend names correctly
   - Expected: backends.len() equals `10`
   - Expected: backends[0] equals `llvm`
   - Expected: backends[1] equals `c`
   - Expected: backends[2] equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps backend names correctly")
val backends = ["llvm", "c", "native", "interpreter", "cranelift", "wasm", "cuda", "vulkan", "lean", "vhdl"]
expect(backends.len()).to_equal(10)
expect(backends[0]).to_equal("llvm")
expect(backends[1]).to_equal("c")
expect(backends[2]).to_equal("native")
```

</details>

#### LLVM produces object code

- LLVM produces object code
   - Expected: backend equals `llvm`
   - Expected: output_kind equals `ObjectCode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LLVM produces object code")
val backend = "llvm"
val output_kind = "ObjectCode"
expect(backend).to_equal("llvm")
expect(output_kind).to_equal("ObjectCode")
```

</details>

#### C backend produces text source

- C backend produces text source
   - Expected: backend equals `c`
   - Expected: output_kind equals `TextSource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C backend produces text source")
val backend = "c"
val output_kind = "TextSource"
expect(backend).to_equal("c")
expect(output_kind).to_equal("TextSource")
```

</details>

#### Interpreter produces interpreted result

- Interpreter produces interpreted result
   - Expected: backend equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Interpreter produces interpreted result")
val backend = "interpreter"
val output_kind = "InterpretedResult"
expect(backend).to_equal("interpreter")
```

</details>

### Codegen adapter target support

#### LLVM supports all CPU targets

- LLVM supports all CPU targets
   - Expected: targets.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LLVM supports all CPU targets")
val targets = ["x86_64", "aarch64", "riscv64"]
expect(targets.len()).to_equal(3)
```

</details>

#### Native supports CPU targets

- Native supports CPU targets
   - Expected: targets.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Native supports CPU targets")
val targets = ["x86_64", "aarch64", "riscv64"]
expect(targets.len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/codegen_trait_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CodegenOutputKind concepts, CodegenOutput patterns, CodegenFactory backend mapping, Codegen adapter target support.
- CodegenOutputKind concepts
- CodegenOutput patterns
- CodegenFactory backend mapping
- Codegen adapter target support

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

- Canonical SPipe generation for source `0d7e658cd6dadb61f400e842ce4e07b7f1257fbd60e74296bd91fe51f73c7661`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d7e658cd6dadb61f400e842ce4e07b7f1257fbd60e74296bd91fe51f73c7661`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d7e658cd6dadb61f400e842ce4e07b7f1257fbd60e74296bd91fe51f73c7661`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/codegen_trait_spec.spl
mirror: doc/06_spec/unit/compiler/backend/codegen_trait_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/codegen_trait_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/codegen_trait_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/codegen_trait_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/codegen_trait_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has four output kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/codegen_trait_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ObjectCode is for native compilation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/codegen_trait_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TextSource is for C/transpiled output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
