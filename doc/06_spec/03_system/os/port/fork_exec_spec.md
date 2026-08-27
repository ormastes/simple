# fork/exec/wait/pipe/dup2 host contract (IF-01 host lane)

> Each scenario exercises the IF-01 syscall family behaviorally on the host by

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fork/exec/wait/pipe/dup2 host contract (IF-01 host lane)

Each scenario exercises the IF-01 syscall family behaviorally on the host by

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/fork_exec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Each scenario exercises the IF-01 syscall family behaviorally on the host by
spawning a real child via std.nogc_sync_mut.src.infra.run_process (which uses
fork+exec+waitpid+pipe+dup2 under the hood) and asserting on the child's
captured exit status and byte streams. Kernel-only contracts (IF-02
Scheduler::clone_task COW) remain documented in the SimpleOS kernel specs;
they are not assertable on a host build.

## Scenarios

### fork/exec/wait IF-01 host lane

#### propagates the child exit status through waitpid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- spawn a child that exits 7 and wait for it
   - Expected: code equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spawn a child that exits 7 and wait for it")
# evidence(protocol_json): exit status asserted below is the complete typed oracle
val (code, _, _) = _run("exit 7")
expect(code).to_equal(7)  # oracle: waitpid must surface the child's exact exit status
```

</details>

#### captures the child computed value across the fork boundary

- spawn a child that computes 41+1 in its own address space and exits with it
   - Expected: code equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spawn a child that computes 41+1 in its own address space and exits with it")
# evidence(protocol_json): exit status asserted below is the complete typed oracle
val (code, _, _) = _run("exit $((41 + 1))")
expect(code).to_equal(42)  # oracle: the child's own arithmetic result crosses the wait boundary
```

</details>

#### delivers child stdout to the parent through the pipe

- spawn a child that writes a sentinel to stdout
   - Expected: code equals `0`
   - Expected: out equals `SSPEC_PIPE_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spawn a child that writes a sentinel to stdout")
# evidence(protocol_json): captured stdout asserted below is the complete typed oracle
val (code, out, _) = _run("printf SSPEC_PIPE_OK")
expect(code).to_equal(0)
expect(out).to_equal("SSPEC_PIPE_OK")  # oracle: pipe read end must deliver the child's bytes verbatim
```

</details>

#### dup2 wiring keeps stdout and stderr as separate streams

- spawn a child that writes distinct sentinels to stdout and stderr
   - Expected: code equals `0`
   - Expected: out equals `OUT_TAG`
   - Expected: err equals `ERR_TAG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spawn a child that writes distinct sentinels to stdout and stderr")
# evidence(protocol_json): both captured streams asserted below are the complete typed oracle
val (code, out, err) = _run("printf OUT_TAG; printf ERR_TAG 1>&2")
expect(code).to_equal(0)
expect(out).to_equal("OUT_TAG")
expect(err).to_equal("ERR_TAG")  # oracle: dup2 must not merge the two descriptors
```

</details>

#### a failing child command reports a non-zero wait status

- spawn a child that fails and wait for it
   - Expected: code != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spawn a child that fails and wait for it")
# evidence(protocol_json): exit status asserted below is the complete typed oracle
val (code, _, _) = _run("false")
expect(code != 0).to_equal(true)  # oracle: waitpid must report failure, never a false success
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `21eeb83eb4c78caf00e548087760242479a2639a4c08dc05612cbeb697a1508a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21eeb83eb4c78caf00e548087760242479a2639a4c08dc05612cbeb697a1508a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21eeb83eb4c78caf00e548087760242479a2639a4c08dc05612cbeb697a1508a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/os/port/fork_exec_spec.spl
mirror: doc/06_spec/03_system/os/port/fork_exec_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/port/fork_exec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/port/fork_exec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/port/fork_exec_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
