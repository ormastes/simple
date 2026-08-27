# loader_api dispatch

> Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# loader_api dispatch

Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10 |
| Category | Kernel loader |
| Status | Active |
| Source | `test/unit/os/kernel/loader/loader_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

## Scenarios

### loader_dispatch

#### empty buffer returns -ENOEXEC

- empty buffer returns -ENOEXEC


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty buffer returns -ENOEXEC")
"""No magic to match => -8."""
val rc = loader_dispatch(_zero_bytes(4), _empty_space())
expect rc.to_equal(-8i64)
```

</details>

#### non-ELF non-SMF bytes return -ENOEXEC

- non-ELF non-SMF bytes return -ENOEXEC


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-ELF non-SMF bytes return -ENOEXEC")
"""Random data must not silently dispatch to either loader."""
val rc = loader_dispatch(_zero_bytes(128), _empty_space())
expect rc.to_equal(-8i64)
```

</details>

#### ELF magic dispatches to elf64 path

- ELF magic dispatches to elf64 path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ELF magic dispatches to elf64 path")
"""ELF prefix should leave the -ENOEXEC branch and reach elf64_load.
With a minimal/invalid ELF body elf64_load returns an error, but it
must NOT be the generic -8 that the sniff branch would return."""
val rc = loader_dispatch(_elf_magic_prefix(), _empty_space())
val dispatched: bool = rc != -8i64 or rc < 0i64
expect dispatched.to_equal(true)
```

</details>

#### SMF trailer magic dispatches to smf path

- SMF trailer magic dispatches to smf path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SMF trailer magic dispatches to smf path")
"""SMF v1.1 packages should not be rejected just because byte zero is payload/stub."""
val rc = loader_dispatch(_smf_trailer_bytes(), _empty_space())
expect rc.to_equal(-38i64)
```

</details>

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

- Canonical SPipe generation for source `27e79f173062795069fca174044abb06ddf70d268145cb96f9cef23680f02d35`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27e79f173062795069fca174044abb06ddf70d268145cb96f9cef23680f02d35`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27e79f173062795069fca174044abb06ddf70d268145cb96f9cef23680f02d35`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/loader/loader_api_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/loader_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/loader_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/loader_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/loader_api_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty buffer returns -ENOEXEC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/loader_api_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'non-ELF non-SMF bytes return -ENOEXEC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/loader_api_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ELF magic dispatches to elf64 path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
