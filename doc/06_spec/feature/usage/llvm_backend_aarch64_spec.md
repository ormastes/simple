# LLVM Backend AArch64 Specification

> Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend AArch64 Specification

Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4002 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_aarch64_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

## Scenarios

### LLVM Backend AArch64

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

#### generates correct aarch64 triple

- generates correct aarch64 triple
   - Expected: triple.arch equals `aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates correct aarch64 triple")
val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
expect(triple.arch).to_equal("aarch64")
expect(triple.to_text()).to_contain("aarch64")
```

</details>

#### datalayout

#### contains correct aarch64 layout

- contains correct aarch64 layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("contains correct aarch64 layout")
val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
val dl = triple.datalayout()
expect(dl).to_contain("n32:64-S128")
```

</details>

#### emits datalayout in module header

- emits datalayout in module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("emits datalayout in module header")
val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
var builder = LlvmIRBuilder__create("test_aarch64", triple)
builder.emit_module_header()
val ir = builder.build()
expect(ir).to_contain("target datalayout")
```

</details>

#### CPU defaults

#### defaults to cortex-a53

- defaults to cortex-a53
   - Expected: config.cpu equals `cortex-a53`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defaults to cortex-a53")
val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
expect(config.cpu).to_equal("cortex-a53")
```

</details>

#### includes neon feature

- includes neon feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes neon feature")
val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
expect(config.features).to_contain("+neon")
```

</details>

#### includes fp-armv8 feature

- includes fp-armv8 feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes fp-armv8 feature")
val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
expect(config.features).to_contain("+fp-armv8")
```

</details>

#### native integer type

#### native_int_type is i64

- native_int_type is i64
   - Expected: translator.native_int() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("native_int_type is i64")
var translator = MirToLlvm__create("test", CodegenTarget.AArch64, nil)
expect(translator.native_int()).to_equal("i64")
```

</details>

#### type mapping

#### uses 64-bit target_bits

- uses 64-bit target_bits
   - Expected: mapper.target_bits equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses 64-bit target_bits")
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.AArch64)
expect(mapper.target_bits).to_equal(64)
```

</details>

#### bare-metal entry

#### uses wfi instruction for halt

- uses wfi instruction for halt
   - Expected: halt equals `wfi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses wfi instruction for halt")
val halt = halt_instruction_for_target(CodegenTarget.AArch64)
expect(halt).to_equal("wfi")
```

</details>

#### builder size type

#### uses i64 size type

- uses i64 size type
   - Expected: builder.size_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses i64 size type")
val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
var builder = LlvmIRBuilder__create("test", triple)
expect(builder.size_type).to_equal("i64")
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

- Canonical SPipe generation for source `27402800eddbd8b3ef876221341dfcacf20c11c00c3e27bdb85dccec6aaf47a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27402800eddbd8b3ef876221341dfcacf20c11c00c3e27bdb85dccec6aaf47a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27402800eddbd8b3ef876221341dfcacf20c11c00c3e27bdb85dccec6aaf47a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/usage/llvm_backend_aarch64_spec.spl
mirror: doc/06_spec/feature/usage/llvm_backend_aarch64_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/llvm_backend_aarch64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/llvm_backend_aarch64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/llvm_backend_aarch64_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/llvm_backend_aarch64_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: LLVM not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/llvm_backend_aarch64_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates correct aarch64 triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/llvm_backend_aarch64_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains correct aarch64 layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
