# Toolchains, userland, and server protocols

> Defines fail-closed live acceptance for target-native Simple and LLVM/C++, expanded userland, bounded lifecycle, HTTP/DB/RESP/SSH, and security policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Toolchains, userland, and server protocols

Defines fail-closed live acceptance for target-native Simple and LLVM/C++, expanded userland, bounded lifecycle, HTTP/DB/RESP/SSH, and security policy.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Defines fail-closed live acceptance for target-native Simple and LLVM/C++, expanded userland, bounded lifecycle, HTTP/DB/RESP/SSH, and security policy.

This is an explicit BLOCKED traceability spec. Each checker validates a
structurally complete blocked candidate through the production capability-ledger
owner and reports its executable owner, exact expected receipt, and resume
command. A row cannot pass until that receipt is produced and admitted.

## Scenarios

### REQ-009: target-native Simple roles

#### should accept complete live evidence for target-native Simple roles

- should accept complete live evidence for target-native Simple roles
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for target-native Simple roles")
step_compile_and_run_hello()
check_simpleos_toolchain_fs("REQ-009", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for target-native Simple roles</summary>

#### should preserve the selected boundary for target-native Simple roles

- should preserve the selected boundary for target-native Simple roles


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for target-native Simple roles")
step_compile_and_run_hello()
check_simpleos_toolchain_fs("REQ-009", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for target-native Simple roles</summary>

#### should reject missing stale substituted or invalid evidence for target-native Simple roles

- should reject missing stale substituted or invalid evidence for target-native Simple roles


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for target-native Simple roles")
step_compile_and_run_hello()
check_simpleos_toolchain_fs("REQ-009", "rejection")
```

</details>


</details>

### REQ-010: full target-native LLVM and Clang profile

#### should accept complete live evidence for full target-native LLVM and Clang profile

- should accept complete live evidence for full target-native LLVM and Clang profile
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for full target-native LLVM and Clang profile")
step_compile_and_run_hello()
check_simpleos_toolchain_fs("REQ-010", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for full target-native LLVM and Clang profile</summary>

#### should preserve the selected boundary for full target-native LLVM and Clang profile

- should preserve the selected boundary for full target-native LLVM and Clang profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for full target-native LLVM and Clang profile")
step_compile_and_run_hello()
check_simpleos_toolchain_fs("REQ-010", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for full target-native LLVM and Clang profile</summary>

#### should reject missing stale substituted or invalid evidence for full target-native LLVM and Clang profile

- should reject missing stale substituted or invalid evidence for full target-native LLVM and Clang profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for full target-native LLVM and Clang profile")
step_compile_and_run_hello()
check_simpleos_toolchain_fs("REQ-010", "rejection")
```

</details>


</details>

### REQ-011: expanded Simple userland

#### should accept complete live evidence for expanded Simple userland

- should accept complete live evidence for expanded Simple userland
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for expanded Simple userland")
step_launch_from_filesystem()
check_simpleos_toolchain_fs("REQ-011", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for expanded Simple userland</summary>

#### should preserve the selected boundary for expanded Simple userland

- should preserve the selected boundary for expanded Simple userland


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for expanded Simple userland")
step_launch_from_filesystem()
check_simpleos_toolchain_fs("REQ-011", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for expanded Simple userland</summary>

#### should reject missing stale substituted or invalid evidence for expanded Simple userland

- should reject missing stale substituted or invalid evidence for expanded Simple userland


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for expanded Simple userland")
step_launch_from_filesystem()
check_simpleos_toolchain_fs("REQ-011", "rejection")
```

</details>


</details>

### REQ-012: unified bounded server lifecycle

#### should accept complete live evidence for unified bounded server lifecycle

- should accept complete live evidence for unified bounded server lifecycle
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for unified bounded server lifecycle")
step_launch_from_filesystem()
check_simpleos_server_protocols("REQ-012", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for unified bounded server lifecycle</summary>

#### should preserve the selected boundary for unified bounded server lifecycle

- should preserve the selected boundary for unified bounded server lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for unified bounded server lifecycle")
step_launch_from_filesystem()
check_simpleos_server_protocols("REQ-012", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for unified bounded server lifecycle</summary>

#### should reject missing stale substituted or invalid evidence for unified bounded server lifecycle

- should reject missing stale substituted or invalid evidence for unified bounded server lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for unified bounded server lifecycle")
step_launch_from_filesystem()
check_simpleos_server_protocols("REQ-012", "rejection")
```

</details>


</details>

### REQ-013: full modern web protocols

#### should accept complete live evidence for full modern web protocols

- should accept complete live evidence for full modern web protocols
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for full modern web protocols")
step_probe_protocol()
check_simpleos_server_protocols("REQ-013", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for full modern web protocols</summary>

#### should preserve the selected boundary for full modern web protocols

- should preserve the selected boundary for full modern web protocols


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for full modern web protocols")
step_probe_protocol()
check_simpleos_server_protocols("REQ-013", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for full modern web protocols</summary>

#### should reject missing stale substituted or invalid evidence for full modern web protocols

- should reject missing stale substituted or invalid evidence for full modern web protocols


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for full modern web protocols")
step_probe_protocol()
check_simpleos_server_protocols("REQ-013", "rejection")
```

</details>


</details>

### REQ-014: database protocols

#### should accept complete live evidence for database protocols

- should accept complete live evidence for database protocols
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for database protocols")
step_probe_protocol()
check_simpleos_server_protocols("REQ-014", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for database protocols</summary>

#### should preserve the selected boundary for database protocols

- should preserve the selected boundary for database protocols


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for database protocols")
step_probe_protocol()
check_simpleos_server_protocols("REQ-014", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for database protocols</summary>

#### should reject missing stale substituted or invalid evidence for database protocols

- should reject missing stale substituted or invalid evidence for database protocols


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for database protocols")
step_probe_protocol()
check_simpleos_server_protocols("REQ-014", "rejection")
```

</details>


</details>

### REQ-015: production SSH v2

#### should accept complete live evidence for production SSH v2

- should accept complete live evidence for production SSH v2
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for production SSH v2")
step_probe_protocol()
check_simpleos_server_protocols("REQ-015", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for production SSH v2</summary>

#### should preserve the selected boundary for production SSH v2

- should preserve the selected boundary for production SSH v2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for production SSH v2")
step_probe_protocol()
check_simpleos_server_protocols("REQ-015", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for production SSH v2</summary>

#### should reject missing stale substituted or invalid evidence for production SSH v2

- should reject missing stale substituted or invalid evidence for production SSH v2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for production SSH v2")
step_probe_protocol()
check_simpleos_server_protocols("REQ-015", "rejection")
```

</details>


</details>

### REQ-016: server confinement and malformed-input safety

#### should accept complete live evidence for server confinement and malformed-input safety

- should accept complete live evidence for server confinement and malformed-input safety
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for server confinement and malformed-input safety")
step_probe_protocol()
check_simpleos_server_protocols("REQ-016", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for server confinement and malformed-input safety</summary>

#### should preserve the selected boundary for server confinement and malformed-input safety

- should preserve the selected boundary for server confinement and malformed-input safety


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for server confinement and malformed-input safety")
step_probe_protocol()
check_simpleos_server_protocols("REQ-016", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for server confinement and malformed-input safety</summary>

#### should reject missing stale substituted or invalid evidence for server confinement and malformed-input safety

- should reject missing stale substituted or invalid evidence for server confinement and malformed-input safety


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for server confinement and malformed-input safety")
step_probe_protocol()
check_simpleos_server_protocols("REQ-016", "rejection")
```

</details>


</details>

### NFR-010: protocol and security policy

#### should accept complete live evidence for protocol and security policy

- should accept complete live evidence for protocol and security policy
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for protocol and security policy")
step_probe_protocol()
check_simpleos_server_protocols("NFR-010", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for protocol and security policy</summary>

#### should preserve the selected boundary for protocol and security policy

- should preserve the selected boundary for protocol and security policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for protocol and security policy")
step_probe_protocol()
check_simpleos_server_protocols("NFR-010", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for protocol and security policy</summary>

#### should reject missing stale substituted or invalid evidence for protocol and security policy

- should reject missing stale substituted or invalid evidence for protocol and security policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for protocol and security policy")
step_probe_protocol()
check_simpleos_server_protocols("NFR-010", "rejection")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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
- `REQ-011`
- `REQ-012`
- `REQ-013`
- `REQ-014`
- `REQ-015`
- `REQ-016`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d8a169c94af0a08292b219d3cd5f5a38cde4569251739783ecaa848fc654d23d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d8a169c94af0a08292b219d3cd5f5a38cde4569251739783ecaa848fc654d23d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d8a169c94af0a08292b219d3cd5f5a38cde4569251739783ecaa848fc654d23d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete live evidence for target-native Simple roles' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept complete live evidence for target-native Simple roles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected boundary for target-native Simple roles' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the selected boundary for target-native Simple roles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale substituted or invalid evidence for target-native Simple roles' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing stale substituted or invalid evidence for target-native Simple roles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete live evidence for full target-native LLVM and Clang profile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected boundary for full target-native LLVM and Clang profile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale substituted or invalid evidence for full target-native LLVM and Clang profile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
