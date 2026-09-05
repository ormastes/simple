# User Hello Exec Probe Contract Specification

> Tests covering Phase-1 user-exec USEROK acceptance contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# User Hello Exec Probe Contract Specification

## Scenarios

### Phase-1 user-exec USEROK acceptance contract

#### defines USEROK as the exec-handoff proof marker

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines USEROK as the exec-handoff proof marker
   - Expected: user_hello_exec_marker() equals `USEROK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines USEROK as the exec-handoff proof marker")
expect(user_hello_exec_marker()).to_equal("USEROK")
```

</details>

#### accepts serial that contains USEROK

- accepts serial that contains USEROK
   - Expected: user_hello_exec_serial_accepts_completion(synthetic_user_serial()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts serial that contains USEROK")
expect(user_hello_exec_serial_accepts_completion(synthetic_user_serial())).to_equal(true)
```

</details>

#### rejects serial without USEROK so there is no false green before Phase 1

- rejects serial without USEROK so there is no false green before Phase 1
   - Expected: user_hello_exec_serial_accepts_completion(boot_only_serial()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects serial without USEROK so there is no false green before Phase 1")
expect(user_hello_exec_serial_accepts_completion(boot_only_serial())).to_equal(false)
```

</details>

#### emits USEROK on real serial once Phase 1 exec lands

- emits USEROK on real serial once Phase 1 exec lands
   - Expected: user_hello_exec_serial_accepts_completion(synthetic_user_serial()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits USEROK on real serial once Phase 1 exec lands")
# Flip run_live() -> true after Phase 1, then wire the real QEMU boot in
# place of synthetic_user_serial(): build hello.elf, boot the lane,
# capture serial, and assert USEROK on it.
if run_live():
    expect(user_hello_exec_serial_accepts_completion(synthetic_user_serial())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/user_hello_exec_probe_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Phase-1 user-exec USEROK acceptance contract.
- Phase-1 user-exec USEROK acceptance contract

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `065b15a8c6d1efc76266a6a1d68bf24255e44056b047bfb74ba4586df4da7abe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `065b15a8c6d1efc76266a6a1d68bf24255e44056b047bfb74ba4586df4da7abe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `065b15a8c6d1efc76266a6a1d68bf24255e44056b047bfb74ba4586df4da7abe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/user_hello_exec_probe_contract_spec.spl
mirror: doc/06_spec/01_unit/os/user_hello_exec_probe_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/user_hello_exec_probe_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/user_hello_exec_probe_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/user_hello_exec_probe_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines USEROK as the exec-handoff proof marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/user_hello_exec_probe_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts serial that contains USEROK' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/user_hello_exec_probe_contract_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects serial without USEROK so there is no false green before Phase 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
