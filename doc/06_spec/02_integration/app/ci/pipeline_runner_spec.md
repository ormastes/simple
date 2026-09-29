# pipeline_runner_spec

> This is the CI application of the orchestration model. It EXECUTES: each job launches a real host process and the receipt carries that process's real exit code and real stdout. A fresh nonce is minted per run and must appear in the job's output, so a receipt cannot be satisfied by fabricated text (research §13.4).

<!-- sdn-diagram:id=pipeline_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pipeline_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pipeline_runner_spec -> std
pipeline_runner_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pipeline_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pipeline_runner_spec

This is the CI application of the orchestration model. It EXECUTES: each job launches a real host process and the receipt carries that process's real exit code and real stdout. A fresh nonce is minted per run and must appear in the job's output, so a receipt cannot be satisfied by fabricated text (research §13.4).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md |
| Source | `test/02_integration/app/ci/pipeline_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This is the CI application of the orchestration model. It EXECUTES: each job
launches a real host process and the receipt carries that process's real exit
code and real stdout. A fresh nonce is minted per run and must appear in the
job's output, so a receipt cannot be satisfied by fabricated text (research
§13.4).

Every job here runs on the `native-process` lane, which is a host process with
only the advertised process controls — NOT a container. The container lane is
separately asserted to be refused as BLOCKED on this host rather than quietly
downgraded to a process (research §4.1, ORCH-006).

## Examples

Three scenarios: a nonce round-trip, an upstream failure that stops its
dependent while an independent job still runs, and a `native-container` job
that is refused.

## Scenarios

### Simple CI runs a pipeline on this host

#### runs every job in order and each receipt carries that run's fresh nonce

- Mint a nonce for this run
- Build three jobs that each echo the nonce with their own name
- Run a pipeline where c waits for a and b
- Confirm the whole run passed and produced three receipts in order
   - Expected: run.verdict equals `VERDICT_PASS`
   - Expected: run.jobs.len() equals `3`
   - Expected: run.jobs[0].job_name equals `a`
   - Expected: run.jobs[1].job_name equals `b`
   - Expected: run.jobs[2].job_name equals `c`
- Confirm each receipt reports a real exit code AND the nonce in real output
   - Expected: r.verdict equals `VERDICT_PASS`
   - Expected: r.exit_code equals `0`
   - Expected: r.runtime_class equals `native-process`
   - Expected: r.attempt equals `1`
- Confirm the receipts are bound to this node's boot instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mint a nonce for this run")
val nonce = "SIMPLEORCH-" + current_time_ms().to_text()

step("Build three jobs that each echo the nonce with their own name")
var t: Dict<text, JobV1> = {}
t["a"] = shell_job("a", "echo " + nonce + "-a")
t["b"] = shell_job("b", "echo " + nonce + "-b")
t["c"] = shell_job("c", "echo " + nonce + "-c")

step("Run a pipeline where c waits for a and b")
val p = pipeline_from(node("a", "a", "", "") + node("b", "b", "", "") +
                      node("c", "c", "a, b", ""))
val run = run_or_empty(p, t, "run-nonce")

step("Confirm the whole run passed and produced three receipts in order")
expect(run.verdict).to_equal(VERDICT_PASS)
expect(run.jobs.len()).to_equal(3)
expect(run.jobs[0].job_name).to_equal("a")
expect(run.jobs[1].job_name).to_equal("b")
expect(run.jobs[2].job_name).to_equal("c")

step("Confirm each receipt reports a real exit code AND the nonce in real output")
for name in ["a", "b", "c"]:
    val r = receipt_for(run, name)
    expect(r.verdict).to_equal(VERDICT_PASS)
    expect(r.exit_code).to_equal(0)
    expect(r.runtime_class).to_equal("native-process")
    expect(r.attempt).to_equal(1)
    expect(r.stdout).to_contain(nonce + "-" + name)

step("Confirm the receipts are bound to this node's boot instance")
expect(receipt_for(run, "a").node_boot_id.len()).to_be_greater_than(0)
```

</details>

#### stops a dependent after its upstream fails while an independent job still runs

- Build a failing job, its dependent, an independent job, and an always-run collector
- Run the pipeline
- Confirm the failing job reports its real non-zero exit code and its output
   - Expected: f.verdict equals `VERDICT_FAIL`
   - Expected: f.exit_code equals `3`
- Confirm the dependent never ran and says which upstream stopped it
   - Expected: d.verdict equals `VERDICT_NOT_RUN`
   - Expected: d.exit_code equals `0`
   - Expected: d.stdout equals ``
- Confirm the independent job still ran and passed
   - Expected: i.verdict equals `VERDICT_PASS`
   - Expected: i.exit_code equals `0`
- Confirm the always-policy collector ran despite the upstream failure
   - Expected: col.verdict equals `VERDICT_PASS`
- Confirm collecting diagnostics did not turn the run green
   - Expected: run.verdict equals `VERDICT_FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a failing job, its dependent, an independent job, and an always-run collector")
val nonce = "SIMPLEORCH-" + current_time_ms().to_text()
var t: Dict<text, JobV1> = {}
t["fails"] = shell_job("fails", "echo " + nonce + "-fails; exit 3")
t["dependent"] = shell_job("dependent", "echo " + nonce + "-dependent")
t["independent"] = shell_job("independent", "echo " + nonce + "-independent")
t["collector"] = shell_job("collector", "echo " + nonce + "-collector")

step("Run the pipeline")
val p = pipeline_from(node("fails", "fails", "", "") +
                      node("dependent", "dependent", "fails", "") +
                      node("independent", "independent", "", "") +
                      node("collector", "collector", "dependent", "always"))
val run = run_or_empty(p, t, "run-failprop")

step("Confirm the failing job reports its real non-zero exit code and its output")
val f = receipt_for(run, "fails")
expect(f.verdict).to_equal(VERDICT_FAIL)
expect(f.exit_code).to_equal(3)
expect(f.stdout).to_contain(nonce + "-fails")

step("Confirm the dependent never ran and says which upstream stopped it")
val d = receipt_for(run, "dependent")
expect(d.verdict).to_equal(VERDICT_NOT_RUN)
expect(d.exit_code).to_equal(0)
expect(d.stdout).to_equal("")
expect(d.reason).to_contain("fails")

step("Confirm the independent job still ran and passed")
val i = receipt_for(run, "independent")
expect(i.verdict).to_equal(VERDICT_PASS)
expect(i.exit_code).to_equal(0)
expect(i.stdout).to_contain(nonce + "-independent")

step("Confirm the always-policy collector ran despite the upstream failure")
val col = receipt_for(run, "collector")
expect(col.verdict).to_equal(VERDICT_PASS)
expect(col.stdout).to_contain(nonce + "-collector")

step("Confirm collecting diagnostics did not turn the run green")
expect(run.verdict).to_equal(VERDICT_FAIL)
```

</details>

#### refuses a native-container job on this host instead of running it as a process

- Probe the host container lane
- Run a pipeline with one native-container job and one process job
- Confirm the container job was refused, not executed
   - Expected: b.verdict equals `VERDICT_BLOCKED`
   - Expected: b.runtime_class equals `native-container`
   - Expected: b.attempt equals `0`
   - Expected: b.exit_code equals `0`
   - Expected: b.stdout equals ``
- Confirm the refusal states why, matching the host probe
   - Expected: b.reason equals `probe.reason`
- Confirm the independent process job still ran for real
   - Expected: plain.verdict equals `VERDICT_PASS`
- Confirm a blocked job leaves the run un-green
   - Expected: run.verdict equals `VERDICT_BLOCKED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Probe the host container lane")
val probe = probe_container_lane()

step("Run a pipeline with one native-container job and one process job")
val nonce = "SIMPLEORCH-" + current_time_ms().to_text()
var t: Dict<text, JobV1> = {}
t["boxed"] = container_job("boxed")
t["plain"] = shell_job("plain", "echo " + nonce + "-plain")
val p = pipeline_from(node("boxed", "boxed", "", "") + node("plain", "plain", "", ""))
val run = run_or_empty(p, t, "run-blocked")

step("Confirm the container job was refused, not executed")
val b = receipt_for(run, "boxed")
expect(b.verdict).to_equal(VERDICT_BLOCKED)
expect(b.runtime_class).to_equal("native-container")
expect(b.attempt).to_equal(0)
expect(b.exit_code).to_equal(0)
expect(b.stdout).to_equal("")

step("Confirm the refusal states why, matching the host probe")
expect(b.reason.len()).to_be_greater_than(0)
expect(b.reason).to_equal(probe.reason)

step("Confirm the independent process job still ran for real")
val plain = receipt_for(run, "plain")
expect(plain.verdict).to_equal(VERDICT_PASS)
expect(plain.stdout).to_contain(nonce + "-plain")

step("Confirm a blocked job leaves the run un-green")
expect(run.verdict).to_equal(VERDICT_BLOCKED)
```

</details>

#### runs the qualification pipeline fixture from disk end to end

- Read the committed pipeline fixture
   - Expected: p.meta.name equals `orchestrator-qualification`
   - Expected: p.jobs.len() equals `4`
- Bind its four template references to the committed process-lane Job
- Run it
- Confirm all four jobs ran in dependency order and the run passed
   - Expected: run.verdict equals `VERDICT_PASS`
   - Expected: run.jobs.len() equals `4`
   - Expected: run.jobs[0].job_name equals `build-linux`
   - Expected: run.jobs[1].job_name equals `build-probe`
   - Expected: run.jobs[2].job_name equals `publish`
   - Expected: run.jobs[3].job_name equals `evidence`
- Confirm the receipts name this pipeline and carry this run's nonce
   - Expected: run.pipeline equals `orchestrator-qualification`
   - Expected: r.verdict equals `VERDICT_PASS`
   - Expected: r.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the committed pipeline fixture")
val p = fixture_pipeline("ci_pipeline.sdn")
expect(p.meta.name).to_equal("orchestrator-qualification")
expect(p.jobs.len()).to_equal(4)

step("Bind its four template references to the committed process-lane Job")
val nonce = "SIMPLEORCH-" + current_time_ms().to_text()
var t: Dict<text, JobV1> = {}
for ref_name in ["echo-linux", "echo-probe", "echo-publish", "echo-evidence"]:
    t[ref_name] = fixture_job("ci_job_process.sdn", ref_name, nonce)

step("Run it")
val run = run_or_empty(p, t, "run-fixture")

step("Confirm all four jobs ran in dependency order and the run passed")
expect(run.verdict).to_equal(VERDICT_PASS)
expect(run.jobs.len()).to_equal(4)
expect(run.jobs[0].job_name).to_equal("build-linux")
expect(run.jobs[1].job_name).to_equal("build-probe")
expect(run.jobs[2].job_name).to_equal("publish")
expect(run.jobs[3].job_name).to_equal("evidence")

step("Confirm the receipts name this pipeline and carry this run's nonce")
expect(run.pipeline).to_equal("orchestrator-qualification")
for r in run.jobs:
    expect(r.verdict).to_equal(VERDICT_PASS)
    expect(r.exit_code).to_equal(0)
    expect(r.stdout).to_contain(nonce)
```

</details>

#### reports the container engine and its privilege as separate facts

- Probe the container lane on this host
- Confirm an unavailable lane claims no engine and no privilege
   - Expected: probe.engine equals ``
   - Expected: probe.privilege equals `PRIVILEGE_UNKNOWN`
- Confirm an available lane names one of the supported engines
- Confirm an available lane states root or rootless, never unknown
- Confirm a rootless claim is never made for docker's root daemon
   - Expected: probe.privilege equals `PRIVILEGE_ROOT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Probe the container lane on this host")
val probe = probe_container_lane()

step("Confirm an unavailable lane claims no engine and no privilege")
if not probe.available:
    expect(probe.engine).to_equal("")
    expect(probe.privilege).to_equal(PRIVILEGE_UNKNOWN)
    expect(probe.reason.len()).to_be_greater_than(0)

step("Confirm an available lane names one of the supported engines")
if probe.available:
    expect([ENGINE_PODMAN, ENGINE_DOCKER, ENGINE_RUNC].contains(probe.engine)).to_be(true)

step("Confirm an available lane states root or rootless, never unknown")
if probe.available:
    expect([PRIVILEGE_ROOTLESS, PRIVILEGE_ROOT].contains(probe.privilege)).to_be(true)

step("Confirm a rootless claim is never made for docker's root daemon")
if probe.engine == ENGINE_DOCKER:
    expect(probe.privilege).to_equal(PRIVILEGE_ROOT)
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


## Related Documentation

- **Research:** [doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md](doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md)


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `4ffd445bbb94e28014d4259ad5ea3041eb4c9917e350a63111d4d27d6ade1b60`
