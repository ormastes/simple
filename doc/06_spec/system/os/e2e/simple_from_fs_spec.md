# simple_from_fs_spec

> Two-step end-to-end gate:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_from_fs_spec

Two-step end-to-end gate:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/system/os/e2e/simple_from_fs_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Two-step end-to-end gate:
      step 1 — `simple --version` emits a version banner on COM1.
      step 2 — `simple /tmp/hello.spl` prints "ok" to COM1.

    Both steps are gated on SIMPLEOS_SIMPLE_FS_E2E=1 and a built disk image.
    All it-blocks skip cleanly (return a skip-reason string) when the gate
    env var is absent — this is intentional until Tracks F and B''' land.

## Scenarios

### E2E: Simple compiler runs from FAT32 on SimpleOS

#### step 1 [simple-fs-version]: simple --version prints a version banner on COM1

- step 1 [simple-fs-version]: simple --version prints a version banner on COM1


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("step 1 [simple-fs-version]: simple --version prints a version banner on COM1")
"""
The kernel init script runs `simple --version` after boot.
Expected: serial output contains "Simple " (natural version prefix).
FAILS UNTIL: Track F (kernel link) + Track B''' (SMF on disk) land.
"""
val gate = _gate()
if gate == "":
    return "skip: SIMPLEOS_SIMPLE_FS_E2E not set"
val serial = ensure_serial()
expect(serial).to_contain("Simple ")
```

</details>

#### step 2 [simple-fs-hello]: simple /tmp/hello.spl prints ok on COM1

- step 2 [simple-fs-hello]: simple /tmp/hello.spl prints ok on COM1


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("step 2 [simple-fs-hello]: simple /tmp/hello.spl prints ok on COM1")
"""
The kernel init script pre-seeds /tmp/hello.spl with `fn main(): print("ok\n")`
and then runs `simple /tmp/hello.spl`.
Expected: serial output contains "ok".
FAILS UNTIL: Track F (kernel link) + Track B''' (SMF on disk) land.
"""
val gate = _gate()
if gate == "":
    return "skip: SIMPLEOS_SIMPLE_FS_E2E not set"
val serial = ensure_serial()
expect(serial).to_contain("ok")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `f583d336a3fc5d91afa9a69af9e99e5038a2584ebe1fef482c2f568209246372`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f583d336a3fc5d91afa9a69af9e99e5038a2584ebe1fef482c2f568209246372`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f583d336a3fc5d91afa9a69af9e99e5038a2584ebe1fef482c2f568209246372`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/system/os/e2e/simple_from_fs_spec.spl
mirror: doc/06_spec/system/os/e2e/simple_from_fs_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/os/e2e/simple_from_fs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/os/e2e/simple_from_fs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/os/e2e/simple_from_fs_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'step 1 [simple-fs-version]: simple --version prints a version banner on COM1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/os/e2e/simple_from_fs_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'step 2 [simple-fs-hello]: simple /tmp/hello.spl prints ok on COM1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
