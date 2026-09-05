# rustc_static_e2e_spec

> Lint-only: validates symbol resolution + IF-08 marker conventions for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rustc_static_e2e_spec

Lint-only: validates symbol resolution + IF-08 marker conventions for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/system/os/port/rustc_static_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Lint-only: validates symbol resolution + IF-08 marker conventions for
    Phase 3 rustc_static smoke. Disk paths and markers referenced without
    invocation. Behavioural body env-gated until Team B static binary lands.
    Markers: [phase-2-rustc-version] [phase-2-rustc-compile-ok]

## Scenarios

### rustc_static in-guest QEMU e2e contract

#### rustc_static binary paths and spawn symbol resolve at lint time

- rustc_static binary paths and spawn symbol resolve at lint time


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rustc_static binary paths and spawn symbol resolve at lint time")
"""
Confirms import path os.kernel.loader.x86_64_fs_exec_spawn is lint-clean.
Phase 3 contract: /usr/bin/rustc_static --target x86_64-unknown-simpleos hello.rs -o /tmp/hello_rs
exits 0, then /tmp/hello_rs runs via fs-exec-spawn. Not invoked here.
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set — lint-only validation passed"
if false:
    val _pid = x86_64_fs_exec_spawn_hello_world_smf()
    val _p = "/usr/bin/rustc_static"
    val _fb = "/sys/apps/rustc_static"
    val _m1 = "[phase-2-rustc-version]"
    val _m2 = "[phase-2-rustc-compile-ok]"
return "skip: behavioural run blocked on Phase 3 Team B binary"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f62dbe6a426b4b673346ccc3353358855a756867aceb14fc01a8750a6c93f434`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f62dbe6a426b4b673346ccc3353358855a756867aceb14fc01a8750a6c93f434`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f62dbe6a426b4b673346ccc3353358855a756867aceb14fc01a8750a6c93f434`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/system/os/port/rustc_static_e2e_spec.spl
mirror: doc/06_spec/system/os/port/rustc_static_e2e_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/system/os/port/rustc_static_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/os/port/rustc_static_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/os/port/rustc_static_e2e_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/system/os/port/rustc_static_e2e_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rustc_static binary paths and spawn symbol resolve at lint time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
