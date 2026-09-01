# Live-relay offset tracking in process_run_timeout_live

> `process_run_timeout_live` supervises long-running children (the native-build

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Live-relay offset tracking in process_run_timeout_live

`process_run_timeout_live` supervises long-running children (the native-build

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/app/io/process_ops_relay_offset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`process_run_timeout_live` supervises long-running children (the native-build
worker, the test runner) and relays their output as it is produced. It polls
the child's stdout/stderr temp files on a 500ms interval.

Until 2026-08-18 each poll called `rt_file_read_text` on the WHOLE temp file
and sliced off the tail it had not yet printed. Only the new bytes were
printed -- so output was never duplicated -- but the READ was O(n^2) in the
child's total output. Measured with the Rust seed: relaying a 2.98 MB log cost
146 MB of `rchar` in the supervising process, with the per-interval read cost
growing linearly for the whole run. The fix reads only the appended bytes via
`rt_file_size` + `rt_file_read_text_at`, which took the same run to 2.84 MB of
`rchar` (linear, ~258 KB per 5s).

## Scope and Preconditions

Unix only (`process_run_timeout_live` delegates to the Windows path on
Windows). Requires `/bin/sh` and `timeout`.

## Primary Workflow

Drive a child that appends unique, numbered lines in several bursts spread
over more than one poll interval, so the relay loop is forced through multiple
iterations with a growing file. The captured stdout must contain every emitted
line exactly once, in order -- no loss, no duplication, no reordering, and no
truncated final line.

## Compatibility and Limitations

**This spec asserts the CORRECTNESS property, not the performance one.** The
relayed bytes go to the supervising process's own stdout, which a spec running
inside that same process cannot capture, so the assertions are made on the
returned stdout -- which is read from the same temp file the relay loop
consumes. A wall-clock or throughput assertion was deliberately NOT written:
this host routinely runs at load 33-55 with 20-30 concurrent `simple`
processes, so any timing bound would be flaky. The O(n^2) regression is
guarded by the recorded `rchar` measurement above and its ablation, not by
this spec.

## Scenarios

### process_run_timeout_live relay offset

#### relays a multi-burst child without losing or duplicating a line

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- relays a multi-burst child without losing or duplicating a line
   - Expected: rc equals `0`
   - Expected: lines.len() equals `200`
   - Expected: lines[idx] equals `burst-{i}-line-{j}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("relays a multi-burst child without losing or duplicating a line")
# 5 bursts of 40 unique lines, ~400ms apart: spans several 500ms polls
# and grows the temp file between each one.
val script = "i=0; while [ $i -lt 5 ]; do j=0; while [ $j -lt 40 ]; do echo \"burst-$i-line-$j\"; j=$((j+1)); done; i=$((i+1)); sleep 0.4; done"
val (stdout, stderr, rc) = process_run_timeout_live("/bin/sh", ["-c", script], 60000)

expect(rc).to_equal(0)

val lines = stdout.trim().split("\n")
expect(lines.len()).to_equal(200)

# Every line unique and in emission order: proves no duplication,
# no loss and no reordering across poll boundaries.
var idx = 0
for i in 0..5:
    for j in 0..40:
        expect(lines[idx]).to_equal("burst-{i}-line-{j}")
        idx = idx + 1
```

</details>

#### does not truncate a final line that lacks a trailing newline

- does not truncate a final line that lacks a trailing newline
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not truncate a final line that lacks a trailing newline")
# printf without \n: the last bytes arrive as a partial line and must
# still be relayed and captured.
val (stdout, stderr, rc) = process_run_timeout_live("/bin/sh", ["-c", "echo first; sleep 0.6; printf 'no-trailing-newline'"], 60000)
expect(rc).to_equal(0)
expect(stdout).to_contain("first")
expect(stdout).to_contain("no-trailing-newline")
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `80b7bd4739797aafdc66fcd24520a20cae13b51357218f0194845a8b53c947ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80b7bd4739797aafdc66fcd24520a20cae13b51357218f0194845a8b53c947ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80b7bd4739797aafdc66fcd24520a20cae13b51357218f0194845a8b53c947ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/io/process_ops_relay_offset_spec.spl
mirror: doc/06_spec/01_unit/app/io/process_ops_relay_offset_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/process_ops_relay_offset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/process_ops_relay_offset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/process_ops_relay_offset_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/io/process_ops_relay_offset_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'relays a multi-burst child without losing or duplicating a line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/process_ops_relay_offset_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not truncate a final line that lacks a trailing newline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
