# Startup Argparse Mmap Perf Specification

> Verifies startup-sensitive behavior used by the low_dependency_ui_dynsmf app root path. The spec proves declarative CLI parsing remains responsive when run through `simple run`, and file-backed mmap loading stays bounded for repeated reads.

<!-- sdn-diagram:id=startup_argparse_mmap_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=startup_argparse_mmap_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

startup_argparse_mmap_perf_spec -> app
startup_argparse_mmap_perf_spec -> cli
startup_argparse_mmap_perf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=startup_argparse_mmap_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Argparse Mmap Perf Specification

Verifies startup-sensitive behavior used by the low_dependency_ui_dynsmf app root path. The spec proves declarative CLI parsing remains responsive when run through `simple run`, and file-backed mmap loading stays bounded for repeated reads.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies startup-sensitive behavior used by the low_dependency_ui_dynsmf app
root path. The spec proves declarative CLI parsing remains responsive when run
through `simple run`, and file-backed mmap loading stays bounded for repeated
reads.

## Examples

The CLI startup scenario writes a temporary Simple entrypoint that parses flags,
options, and positionals, runs it through the current Simple launcher, checks
the parsed output, and enforces a warm average latency budget. Subprocess
failures are hard failures with diagnostics. The mmap scenario writes a fixture,
reads it repeatedly through `file_mmap_read_text`, checks exact content, and
enforces a read latency budget.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### startup arg parsing and mmap perf smoke

#### keeps declarative cli startup parsing responsive

1. fail

2. delete if exists

3. delete if exists
   - Expected: write_cli_perf_script(script_path) is true
   - Expected: rt_file_write_text(fixture_path, "fn main(): print \\\"fixture\\\"\\n") is true

4. cleanup tmpdir

5. fail

6. cleanup tmpdir

7. fail
   - Expected: run.0 contains `expected`

8. cleanup tmpdir


<details>
<summary>Executable SPipe</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpdir = shell("mktemp -d").stdout.trim()
if tmpdir == "":
    fail("failed to create temporary directory")

val script_path = "{tmpdir}/main.spl"
val fixture_path = "{tmpdir}/input.spl"

delete_if_exists(script_path)
delete_if_exists(fixture_path)
expect(write_cli_perf_script(script_path)).to_equal(true)
expect(rt_file_write_text(fixture_path, "fn main(): print \\\"fixture\\\"\\n")).to_equal(true)

val warm = run_cli_perf_once(script_path, fixture_path)
if warm.2 != 0:
    cleanup_tmpdir(tmpdir)
    fail("startup perf warm run failed: code={warm.2} stderr={warm.1}")

var total_elapsed = 0i64
var run_count = 0i64
val expected = "true|auto|7|build|{fixture_path}"

for _i in 0..3:
    val run = run_cli_perf_once(script_path, fixture_path)
    if run.2 != 0:
        cleanup_tmpdir(tmpdir)
        fail("startup perf measured run failed: code={run.2} stderr={run.1}")
    expect(run.0.contains(expected)).to_equal(true)
    total_elapsed = total_elapsed + run.3
    run_count = run_count + 1

cleanup_tmpdir(tmpdir)

val avg_elapsed_ms = (total_elapsed / run_count) / 1000
expect(avg_elapsed_ms).to_be_less_than(400)
```

</details>

#### keeps file-backed mmap loading responsive

1. fail

2. delete if exists
   - Expected: rt_file_write_text(fixture_path, payload) is true

3. cleanup tmpdir

4. fail
   - Expected: content equals `payload`

5. total elapsed = total elapsed +

6. cleanup tmpdir


<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpdir = shell("mktemp -d").stdout.trim()
if tmpdir == "":
    fail("failed to create temporary directory")

val fixture_path = "{tmpdir}/mmap_perf_fixture.txt"
delete_if_exists(fixture_path)

val chunk = "simple-mmap-perf-fixture|0123456789abcdef\n"
val payload = repeated_text(chunk, 4096)
expect(rt_file_write_text(fixture_path, payload)).to_equal(true)

var total_elapsed = 0i64
var iteration_count = 0i64

for _i in 0..32:
    val start = unix_micros()
    val content = file_mmap_read_text(fixture_path)
    if content == "":
        cleanup_tmpdir(tmpdir)
        fail("file_mmap_read_text failed for {fixture_path}")

    expect(content).to_equal(payload)

    total_elapsed = total_elapsed + (unix_micros() - start)
    iteration_count = iteration_count + 1

cleanup_tmpdir(tmpdir)

val avg_elapsed_ms = (total_elapsed / iteration_count) / 1000
expect(avg_elapsed_ms).to_be_less_than(50)
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


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/low_dependency_ui_dynsmf.md](doc/02_requirements/nfr/low_dependency_ui_dynsmf.md)
- **Plan:** [doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md](doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md)
- **Design:** [doc/05_design/low_dependency_ui_dynsmf.md](doc/05_design/low_dependency_ui_dynsmf.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>
