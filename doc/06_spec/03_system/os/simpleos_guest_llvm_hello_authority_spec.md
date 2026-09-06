# simpleos_guest_llvm_hello_authority_spec

> Behavioral acceptance for process-manager-owned guest LLVM execution evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_guest_llvm_hello_authority_spec

Behavioral acceptance for process-manager-owned guest LLVM execution evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_guest_llvm_hello_authority_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Behavioral acceptance for process-manager-owned guest LLVM execution evidence.

## Scenarios

### SimpleOS guest LLVM hello-world execution evidence

#### admits the shared x86_64 ARM64 and RV64 guest authority contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits the shared x86_64 ARM64 and RV64 guest authority contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("admits the shared x86_64 ARM64 and RV64 guest authority contract")
for target in [
    "x86_64-unknown-simpleos",
    "aarch64-unknown-simpleos",
    "riscv64gc-unknown-simpleos",
]:
    val want = expected_for(target)
    val clang = result_for(ProcessExecutionStageV1.ClangCompile)
    val lld = result_for(ProcessExecutionStageV1.LldLink)
    val hello = result_for(ProcessExecutionStageV1.HelloRun)
    expect(guest_toolchain_hello_execution_chain_v1_validate(
        want, clang, lld, hello)).to_be(true)
```

</details>

#### rejects a host Linux target on the guest authority route

- rejects a host Linux target on the guest authority route


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a host Linux target on the guest authority route")
val want = expected_for("aarch64-unknown-linux-gnu")
expect(guest_toolchain_hello_execution_chain_v1_validate(
    want,
    result_for(ProcessExecutionStageV1.ClangCompile),
    result_for(ProcessExecutionStageV1.LldLink),
    result_for(ProcessExecutionStageV1.HelloRun))).to_be(false)
```

</details>

#### accepts an exact process-manager child chain as diagnostic input

- accepts an exact process-manager child chain as diagnostic input


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts an exact process-manager child chain as diagnostic input")
val clang = result_for(ProcessExecutionStageV1.ClangCompile)
val lld = result_for(ProcessExecutionStageV1.LldLink)
val hello = result_for(ProcessExecutionStageV1.HelloRun)
expect(process_execution_result_v1_validate(clang)).to_be(true)
expect(process_execution_result_v1_validate(lld)).to_be(true)
expect(process_execution_result_v1_validate(hello)).to_be(true)
expect(guest_toolchain_hello_execution_chain_v1_validate(
    expected(), clang, lld, hello)).to_be(true)
```

</details>

#### rejects caller-substituted stdout exit and executable identity

- rejects caller-substituted stdout exit and executable identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects caller-substituted stdout exit and executable identity")
val clang = result_for(ProcessExecutionStageV1.ClangCompile)
val lld = result_for(ProcessExecutionStageV1.LldLink)
var hello = result_for(ProcessExecutionStageV1.HelloRun)
hello.captured_stdout = "claimed by host\n"
expect(guest_toolchain_hello_execution_chain_v1_validate(
    expected(), clang, lld, hello)).to_be(false)
hello = result_for(ProcessExecutionStageV1.HelloRun)
hello.exit_code = 1
expect(guest_toolchain_hello_execution_chain_v1_validate(
    expected(), clang, lld, hello)).to_be(false)
hello = result_for(ProcessExecutionStageV1.HelloRun)
hello.executable_sha256 = sha256_text("host-elf")
expect(guest_toolchain_hello_execution_chain_v1_validate(
    expected(), clang, lld, hello)).to_be(false)
```

</details>

#### rejects stale filesystem generation and child substitution

- rejects stale filesystem generation and child substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects stale filesystem generation and child substitution")
val clang = result_for(ProcessExecutionStageV1.ClangCompile)
var lld = result_for(ProcessExecutionStageV1.LldLink)
val hello = result_for(ProcessExecutionStageV1.HelloRun)
lld.filesystem_generation = 41u64
expect(guest_toolchain_hello_execution_chain_v1_validate(
    expected(), clang, lld, hello)).to_be(false)
lld = result_for(ProcessExecutionStageV1.LldLink)
lld.child_id = clang.child_id
expect(guest_toolchain_hello_execution_chain_v1_validate(
    expected(), clang, lld, hello)).to_be(false)
```

</details>

#### rejects a different process tree and substituted link output

- rejects a different process tree and substituted link output


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a different process tree and substituted link output")
val clang = result_for(ProcessExecutionStageV1.ClangCompile)
val lld = result_for(ProcessExecutionStageV1.LldLink)
var hello = result_for(ProcessExecutionStageV1.HelloRun)
hello.parent_id = 8u64
expect(guest_toolchain_hello_execution_chain_v1_validate(
    expected(), clang, lld, hello)).to_be(false)
hello = result_for(ProcessExecutionStageV1.HelloRun)
var changed_lld = lld
changed_lld.result_sha256 = sha256_text("different-elf")
expect(guest_toolchain_hello_execution_chain_v1_validate(
    expected(), clang, changed_lld, hello)).to_be(false)
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

- `REQ-SSPEC-SYSTEM`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b35b0157f56c4e421a69372b1c3a7d1626241abd3f4abd34864b4b662b275e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b35b0157f56c4e421a69372b1c3a7d1626241abd3f4abd34864b4b662b275e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b35b0157f56c4e421a69372b1c3a7d1626241abd3f4abd34864b4b662b275e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos_guest_llvm_hello_authority_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_guest_llvm_hello_authority_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos_guest_llvm_hello_authority_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_guest_llvm_hello_authority_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_guest_llvm_hello_authority_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/simpleos_guest_llvm_hello_authority_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits the shared x86_64 ARM64 and RV64 guest authority contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_guest_llvm_hello_authority_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a host Linux target on the guest authority route' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_guest_llvm_hello_authority_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an exact process-manager child chain as diagnostic input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
