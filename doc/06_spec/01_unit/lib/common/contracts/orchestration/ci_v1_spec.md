# ci_v1_spec

> CI is applied as a controller over the existing Job path, not as a second scheduler: a `Pipeline` is a reusable definition that EXPANDS into ordinary `Job` resources with declared dependencies. This spec pins the expansion — deterministic order, and refusal of every unschedulable pipeline shape (unresolved template, unknown dependency, self-edge, cycle).

<!-- sdn-diagram:id=ci_v1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ci_v1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ci_v1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ci_v1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ci_v1_spec

CI is applied as a controller over the existing Job path, not as a second scheduler: a `Pipeline` is a reusable definition that EXPANDS into ordinary `Job` resources with declared dependencies. This spec pins the expansion — deterministic order, and refusal of every unschedulable pipeline shape (unresolved template, unknown dependency, self-edge, cycle).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md |
| Source | `test/01_unit/lib/common/contracts/orchestration/ci_v1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

CI is applied as a controller over the existing Job path, not as a second
scheduler: a `Pipeline` is a reusable definition that EXPANDS into ordinary
`Job` resources with declared dependencies. This spec pins the expansion —
deterministic order, and refusal of every unschedulable pipeline shape
(unresolved template, unknown dependency, self-edge, cycle).

## Examples

`test/fixtures/orchestration/ci_pipeline.sdn` is the four-job diamond;
`ci_pipeline_cycle.sdn` is a two-job cycle; `ci_job_process.sdn` and
`ci_job_container.sdn` are the Job templates.

## Scenarios

### Simple CI pipeline expansion

#### decodes a Job whose template runs on the host process lane

- Decode the process-lane Job fixture
- Confirm identity, backoff intent and execution class
   - Expected: j.meta.name equals `echo-linux`
   - Expected: j.meta.ns equals `ci`
   - Expected: j.backoff_limit equals `0`
   - Expected: j.template.runtime_class equals `native-process`
- Confirm the executable and its arguments survived decode
   - Expected: c.command.len() equals `2`
   - Expected: c.command[0] equals `/usr/bin/busybox`
   - Expected: c.image equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode the process-lane Job fixture")
val j = job_of("ci_job_process.sdn")

step("Confirm identity, backoff intent and execution class")
expect(j.meta.name).to_equal("echo-linux")
expect(j.meta.ns).to_equal("ci")
expect(j.backoff_limit).to_equal(0)
expect(j.template.runtime_class).to_equal("native-process")

step("Confirm the executable and its arguments survived decode")
val c = j.template.containers[0]
expect(c.command.len()).to_equal(2)
expect(c.command[0]).to_equal("/usr/bin/busybox")
expect(c.args[0]).to_contain("build-linux")
expect(c.image).to_equal("")
```

</details>

#### refuses a process-lane Job that names no executable

- Decode a process-lane Job with command removed
- Confirm the refusal names the missing command
   - Expected: r.kind equals `missing_field`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a process-lane Job with command removed")
var src = file_read(F + "ci_job_process.sdn") ?? ""
src = src.replace("                  command: [\"/usr/bin/busybox\", \"echo\"]\n", "")
match decode_job(src):
    case Ok(_): assert_true(false)
    case Err(r):
        step("Confirm the refusal names the missing command")
        expect(r.kind).to_equal("missing_field")
        expect(r.path).to_end_with(".command")
```

</details>

#### refuses a process-lane Job that also names an image

- Decode a process-lane Job carrying an image as well as a command
- Confirm the contradiction is refused
   - Expected: r.kind equals `unexpected_field`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a process-lane Job carrying an image as well as a command")
var src = file_read(F + "ci_job_process.sdn") ?? ""
src = src.replace("                  command:", "                  image: \"docker.io/library/busybox\"\n                  command:")
match decode_job(src):
    case Ok(_): assert_true(false)
    case Err(r):
        step("Confirm the contradiction is refused")
        expect(r.kind).to_equal("unexpected_field")
        expect(r.message).to_contain("does not run an image")
```

</details>

#### orders a four-job diamond so every dependency precedes its dependents

- Decode the qualification pipeline
   - Expected: p.meta.name equals `orchestrator-qualification`
   - Expected: p.jobs.len() equals `4`
- Expand it against the four Job templates
- Confirm declaration order breaks the tie between the two builds
   - Expected: names.len() equals `4`
   - Expected: names[0] equals `build-linux`
   - Expected: names[1] equals `build-probe`
- Confirm publish follows both builds and evidence follows publish
   - Expected: names[2] equals `publish`
   - Expected: names[3] equals `evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode the qualification pipeline")
val p = pipeline_of("ci_pipeline.sdn")
expect(p.meta.name).to_equal("orchestrator-qualification")
expect(p.jobs.len()).to_equal(4)

step("Expand it against the four Job templates")
val names = order_names(p, four_templates())

step("Confirm declaration order breaks the tie between the two builds")
expect(names.len()).to_equal(4)
expect(names[0]).to_equal("build-linux")
expect(names[1]).to_equal("build-probe")

step("Confirm publish follows both builds and evidence follows publish")
expect(names[2]).to_equal("publish")
expect(names[3]).to_equal("evidence")
```

</details>

#### refuses a pipeline whose jobs form a dependency cycle

- Expand a two-job cycle
- Confirm the cycle is named as such
   - Expected: r.kind equals `dependency_cycle`
   - Expected: r.path equals `spec.jobs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expand a two-job cycle")
val r = expansion_rejection(pipeline_of("ci_pipeline_cycle.sdn"), four_templates())

step("Confirm the cycle is named as such")
expect(r.kind).to_equal("dependency_cycle")
expect(r.path).to_equal("spec.jobs")
```

</details>

#### refuses a job that depends on itself

- Expand a pipeline whose only job lists itself in runAfter
- Confirm the self-edge is reported at the job's runAfter
   - Expected: r.kind equals `dependency_cycle`
   - Expected: r.path equals `spec.jobs.0.runAfter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expand a pipeline whose only job lists itself in runAfter")
val src = "apiVersion: " + CI_API_VERSION_V1 + "\n" +
          "kind: Pipeline\n" +
          "metadata:\n" +
          "    name: selfish\n" +
          "spec:\n" +
          "    jobs:\n" +
          "        - name: a\n" +
          "          jobTemplateRef: echo-linux\n" +
          "          runAfter: [a]\n"
match decode_pipeline(src):
    case Err(_): assert_true(false)
    case Ok(p):
        val r = expansion_rejection(p, four_templates())
        step("Confirm the self-edge is reported at the job's runAfter")
        expect(r.kind).to_equal("dependency_cycle")
        expect(r.path).to_equal("spec.jobs.0.runAfter")
```

</details>

#### refuses a pipeline that references a Job nobody supplied

- Expand the qualification pipeline with one template withheld
- Confirm the unresolved reference is named
   - Expected: r.kind equals `unresolved_reference`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expand the qualification pipeline with one template withheld")
val p = pipeline_of("ci_pipeline.sdn")
var partial: Dict<text, JobV1> = {}
partial["echo-linux"] = job_of("ci_job_process.sdn")
val r = expansion_rejection(p, partial)

step("Confirm the unresolved reference is named")
expect(r.kind).to_equal("unresolved_reference")
expect(r.message).to_contain("echo-probe")
```

</details>

#### refuses a runAfter that names an undeclared job

- Expand a pipeline whose runAfter names a job it never declares
- Confirm the dangling dependency is refused
   - Expected: r.kind equals `unresolved_reference`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expand a pipeline whose runAfter names a job it never declares")
val src = "apiVersion: " + CI_API_VERSION_V1 + "\n" +
          "kind: Pipeline\n" +
          "metadata:\n" +
          "    name: dangling\n" +
          "spec:\n" +
          "    jobs:\n" +
          "        - name: a\n" +
          "          jobTemplateRef: echo-linux\n" +
          "          runAfter: [ghost]\n"
match decode_pipeline(src):
    case Err(_): assert_true(false)
    case Ok(p):
        val r = expansion_rejection(p, four_templates())
        step("Confirm the dangling dependency is refused")
        expect(r.kind).to_equal("unresolved_reference")
        expect(r.message).to_contain("ghost")
```

</details>

#### refuses an unsupported runPolicy

- Decode a pipeline job with an invented runPolicy
- Confirm the policy is refused at its own path
   - Expected: r.kind equals `unsupported_run_policy`
   - Expected: r.path equals `spec.jobs.0.runPolicy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a pipeline job with an invented runPolicy")
val src = "apiVersion: " + CI_API_VERSION_V1 + "\n" +
          "kind: Pipeline\n" +
          "metadata:\n" +
          "    name: policy\n" +
          "spec:\n" +
          "    jobs:\n" +
          "        - name: a\n" +
          "          jobTemplateRef: echo-linux\n" +
          "          runPolicy: maybe\n"
match decode_pipeline(src):
    case Ok(_): assert_true(false)
    case Err(r):
        step("Confirm the policy is refused at its own path")
        expect(r.kind).to_equal("unsupported_run_policy")
        expect(r.path).to_equal("spec.jobs.0.runPolicy")
```

</details>

#### refuses a Job document offered where a Pipeline is expected

- Decode the Job fixture as a Pipeline
- Confirm the kind mismatch is reported
   - Expected: r.kind equals `unsupported_kind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode the Job fixture as a Pipeline")
match decode_pipeline(file_read(F + "ci_job_process.sdn") ?? ""):
    case Ok(_): assert_true(false)
    case Err(r):
        step("Confirm the kind mismatch is reported")
        expect(r.kind).to_equal("unsupported_kind")
        expect(r.message).to_contain("Pipeline")
```

</details>

#### orders jobs that were declared out of dependency order

- Declare the dependent job before the two it waits for
- Confirm the declared order really is publish-first
   - Expected: p.jobs[0].name equals `publish`
- Expand it
- Confirm both builds now precede publish
   - Expected: names.len() equals `3`
   - Expected: names[0] equals `build-linux`
   - Expected: names[1] equals `build-probe`
   - Expected: names[2] equals `publish`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Declare the dependent job before the two it waits for")
val src = "apiVersion: " + CI_API_VERSION_V1 + "\n" +
          "kind: Pipeline\n" +
          "metadata:\n" +
          "    name: reversed\n" +
          "spec:\n" +
          "    jobs:\n" +
          "        - name: publish\n" +
          "          jobTemplateRef: echo-publish\n" +
          "          runAfter: [build-linux, build-probe]\n" +
          "        - name: build-linux\n" +
          "          jobTemplateRef: echo-linux\n" +
          "        - name: build-probe\n" +
          "          jobTemplateRef: echo-probe\n"
match decode_pipeline(src):
    case Err(_): assert_true(false)
    case Ok(p):
        step("Confirm the declared order really is publish-first")
        expect(p.jobs[0].name).to_equal("publish")

        step("Expand it")
        val names = order_names(p, four_templates())

        step("Confirm both builds now precede publish")
        expect(names.len()).to_equal(3)
        expect(names[0]).to_equal("build-linux")
        expect(names[1]).to_equal("build-probe")
        expect(names[2]).to_equal("publish")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** [doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md](doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md)


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `ded2e3475baa33a792ac4f45d7033558e3b177d6dd1a97ac08a7b78f830dd46a`
