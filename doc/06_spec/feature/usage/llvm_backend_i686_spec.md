# LLVM Backend i686 (x86 32-bit) Specification

> Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend i686 (x86 32-bit) Specification

Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4001 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_i686_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.
This includes target triple generation, datalayout, native integer types, and CPU defaults.

## Scenarios

### LLVM Backend i686

#### env_skip: LLVM not available

- env_skip: LLVM not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("env_skip: LLVM not available")
val reason = test_env_gate_skip("SIMPLE_LLVM_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### target triple

#### generates correct i686 triple

- generates correct i686 triple
   - Expected: triple.arch equals `i686`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates correct i686 triple")
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
expect(triple.arch).to_equal("i686")
expect(triple.to_text()).to_contain("i686")
```

</details>

#### includes correct OS in triple

- includes correct OS in triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes correct OS in triple")
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
val text = triple.to_text()
# Should have linux-gnu or similar env
expect(text).to_contain("i686")
```

</details>

#### datalayout

#### contains 32-bit pointer specification

- contains 32-bit pointer specification


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("contains 32-bit pointer specification")
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
val dl = triple.datalayout()
expect(dl).to_contain("p:32:32")
```

</details>

#### emits datalayout in module header

- emits datalayout in module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("emits datalayout in module header")
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
var builder = LlvmIRBuilder__create("test_i686", triple)
builder.emit_module_header()
val ir = builder.build()
expect(ir).to_contain("target datalayout")
expect(ir).to_contain("p:32:32")
```

</details>

#### type mapping

#### uses 32-bit target_bits

- uses 32-bit target_bits
   - Expected: mapper.target_bits equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses 32-bit target_bits")
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86)
expect(mapper.target_bits).to_equal(32)
```

</details>

#### native integer type

#### native_int_type is i32

- native_int_type is i32
   - Expected: translator.native_int() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("native_int_type is i32")
var translator = MirToLlvm__create("test", CodegenTarget.X86, nil)
expect(translator.native_int()).to_equal("i32")
```

</details>

#### CPU defaults

#### defaults to i686 CPU

- defaults to i686 CPU
   - Expected: config.cpu equals `i686`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defaults to i686 CPU")
val config = LlvmTargetConfig__for_target(CodegenTarget.X86, nil)
expect(config.cpu).to_equal("i686")
```

</details>

#### includes sse2 feature

- includes sse2 feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes sse2 feature")
val config = LlvmTargetConfig__for_target(CodegenTarget.X86, nil)
expect(config.features).to_contain("+sse2")
```

</details>

#### compatibility build

#### works for i686

- works for i686
   - Expected: config.cpu equals `i686`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works for i686")
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86)
expect(config.cpu).to_equal("i686")
```

</details>

#### builder size type

#### uses i32 size type for memcpy/memset

- uses i32 size type for memcpy/memset
   - Expected: builder.size_type equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses i32 size type for memcpy/memset")
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
var builder = LlvmIRBuilder__create("test", triple)
expect(builder.size_type).to_equal("i32")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f139ed77a289898de2d378b1195070a3cb03f1b50709ff6b1edd940471e51f7d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f139ed77a289898de2d378b1195070a3cb03f1b50709ff6b1edd940471e51f7d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f139ed77a289898de2d378b1195070a3cb03f1b50709ff6b1edd940471e51f7d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/usage/llvm_backend_i686_spec.spl
mirror: doc/06_spec/feature/usage/llvm_backend_i686_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/llvm_backend_i686_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/llvm_backend_i686_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/llvm_backend_i686_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/llvm_backend_i686_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: LLVM not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/llvm_backend_i686_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates correct i686 triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/llvm_backend_i686_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes correct OS in triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
