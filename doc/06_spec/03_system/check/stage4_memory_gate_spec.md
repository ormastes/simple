# Stage-4 Memory Gate Sampler

> Operators attach the out-of-process `memstat` sampler (src/app/memstat) to a running PID to record an OS-truth memory profile: /proc/<pid>/smaps_rollup (Rss, Pss, Pss_Anon, Private_Dirty, Swap) plus /proc/<pid>/stat fault counters, one CSV row per interval. `scripts/check/check-stage4-memory-gate.shs` wraps the same sampler around a fixed workload and gates on peak RSS. This spec proves the sampler contract on a short-lived target: the CSV exists, carries the fixed header plus at least one data row, the RSS column parses as a positive integer, and a missing-argument invocation fails with usage help.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage-4 Memory Gate Sampler

Operators attach the out-of-process `memstat` sampler (src/app/memstat) to a running PID to record an OS-truth memory profile: /proc/<pid>/smaps_rollup (Rss, Pss, Pss_Anon, Private_Dirty, Swap) plus /proc/<pid>/stat fault counters, one CSV row per interval. `scripts/check/check-stage4-memory-gate.shs` wraps the same sampler around a fixed workload and gates on peak RSS. This spec proves the sampler contract on a short-lived target: the CSV exists, carries the fixed header plus at least one data row, the RSS column parses as a positive integer, and a missing-argument invocation fails with usage help.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #stage4-memory-gate |
| Category | Infrastructure |
| Status | In Progress |
| Requirements | doc/03_plan/compiler/bootstrap/stage4_memory_parallel_agent_plan_2026-07-29.md (lane L5) |
| Design | doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md |
| Source | `test/03_system/check/stage4_memory_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Operators attach the out-of-process `memstat` sampler (src/app/memstat) to a
running PID to record an OS-truth memory profile: /proc/<pid>/smaps_rollup
(Rss, Pss, Pss_Anon, Private_Dirty, Swap) plus /proc/<pid>/stat fault
counters, one CSV row per interval. `scripts/check/check-stage4-memory-gate.shs`
wraps the same sampler around a fixed workload and gates on peak RSS. This
spec proves the sampler contract on a short-lived target: the CSV exists,
carries the fixed header plus at least one data row, the RSS column parses as
a positive integer, and a missing-argument invocation fails with usage help.

## Key Concepts

| Concept | Description |
|---------|-------------|
| smaps_rollup | Kernel-aggregated per-process memory truth (kB values) |
| memstat | Pure-Simple sampler app; exits cleanly when the target PID dies |
| RSS gate | check-stage4-memory-gate.shs fails when peak rss_kb exceeds STAGE4_MEM_GATE_RSS_KB |

## Related Specifications

- doc/03_plan/compiler/bootstrap/stage4_memory_parallel_agent_plan_2026-07-29.md — lane map

## Scenarios

### Stage-4 memory gate sampler

#### records a header plus data rows with positive RSS for a short-lived process

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records a header plus data rows with positive RSS for a short-lived process
- Prepare a clean artifact directory
- Start a short-lived background target process
- Sample the target with memstat until it exits
- Read back the recorded CSV profile
- Parse the RSS column of the first data row


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records a header plus data rows with positive RSS for a short-lived process")
step("Prepare a clean artifact directory")
dir_create_all(ARTIFACT_DIR)

step("Start a short-lived background target process")
val pid = start_short_lived_target("8")
val pid_num = parse_dec(pid)
expect(pid_num).to_be_greater_than(0)

step("Sample the target with memstat until it exits")
val rc = sample_with_memstat(pid, CSV_PATH)
assert_equal(rc, 0)

step("Read back the recorded CSV profile")
assert_true(file_exists(CSV_PATH))
val lines = non_empty_lines(file_read(CSV_PATH))
expect(lines.len()).to_be_greater_than(1)
assert_equal(lines[0], CSV_HEADER)

step("Parse the RSS column of the first data row")
val cols = lines[1].split(",")
assert_equal(cols.len(), 8)
val rss_kb = parse_dec(cols[1])
expect(rss_kb).to_be_greater_than(0)
```

</details>

#### rejects an invocation without arguments and prints usage help

- rejects an invocation without arguments and prints usage help
- Run memstat with no arguments
   - Expected: code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an invocation without arguments and prints usage help")
step("Run memstat with no arguments")
val (out, _err, code) = process_run("bin/simple", ["run", "src/app/memstat/main.spl"])
expect(code).to_equal(2)
expect(out).to_contain("usage: memstat")
```

</details>

#### --by-owner degrades to a clear status instead of a crash or silent empty output when attribution is off

- --by-owner degrades to a clear status instead of a crash or silent empty output when attribution is off
- Run memstat --by-owner without SIMPLE_MEM_ATTR set
- Confirm memstat exits cleanly and always prints the mode banner
- Confirm a clear STATUS line is printed: off or extern-unavailable, never a silent empty body


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("--by-owner degrades to a clear status instead of a crash or silent empty output when attribution is off")
step("Run memstat --by-owner without SIMPLE_MEM_ATTR set")
val (out, _err, code) = run_by_owner_with(contract_binary(), false)

step("Confirm memstat exits cleanly and always prints the mode banner")
assert_equal(code, 0)
expect(out).to_contain("memstat --by-owner: per-owner memory report")

step("Confirm a clear STATUS line is printed: off or extern-unavailable, never a silent empty body")
val degraded = out.contains("STATUS\tATTRIBUTION_OFF") or out.contains("STATUS\tEXTERN_UNAVAILABLE")
assert_true(degraded)
```

</details>

#### --by-owner prints real per-owner rows when SIMPLE_MEM_ATTR=1 and the extern is available

- --by-owner prints real per-owner rows when SIMPLE_MEM_ATTR=1 and the extern is available
- Run memstat --by-owner in a child process with SIMPLE_MEM_ATTR=1 (self-heals onto a seed with the extern wired if needed)
- Confirm the subprocess exited cleanly
- Confirm at least one per-owner data row printed under the header
- No available binary in this environment has rt_mem_attr_* wired yet; confirm the blocked-dependency status instead of a crash or silent empty output


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("--by-owner prints real per-owner rows when SIMPLE_MEM_ATTR=1 and the extern is available")
step("Run memstat --by-owner in a child process with SIMPLE_MEM_ATTR=1 (self-heals onto a seed with the extern wired if needed)")
val (out, _err, code) = run_by_owner_attr_on()

step("Confirm the subprocess exited cleanly")
assert_equal(code, 0)

if out.contains("OWNER\tLIVE\tPEAK\tALLOCS"):
    step("Confirm at least one per-owner data row printed under the header")
    expect(out).to_contain("<unattributed>")
else:
    step("No available binary in this environment has rt_mem_attr_* wired yet; confirm the blocked-dependency status instead of a crash or silent empty output")
    expect(out).to_contain("STATUS\tEXTERN_UNAVAILABLE")
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


## Related Documentation

- **Requirements:** `doc/03_plan/compiler/bootstrap/stage4_memory_parallel_agent_plan_2026-07-29.md (lane L5)`
- **Design:** `doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-STAGE4-MEMORY-GATE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8beb2f7a52200ba28bb4e9f4c98e7e8a6955876f79bb35401e6178ed4ed38ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8beb2f7a52200ba28bb4e9f4c98e7e8a6955876f79bb35401e6178ed4ed38ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8beb2f7a52200ba28bb4e9f4c98e7e8a6955876f79bb35401e6178ed4ed38ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/stage4_memory_gate_spec.spl
mirror: doc/06_spec/03_system/check/stage4_memory_gate_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/check/stage4_memory_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/stage4_memory_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/stage4_memory_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/stage4_memory_gate_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/stage4_memory_gate_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a header plus data rows with positive RSS for a short-lived process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/stage4_memory_gate_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an invocation without arguments and prints usage help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/stage4_memory_gate_spec.spl:170:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '--by-owner degrades to a clear status instead of a crash or silent empty output when attribution is off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
