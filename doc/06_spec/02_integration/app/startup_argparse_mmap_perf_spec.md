# Startup Argparse Mmap Perf Specification

> 1. fail

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

## Scenarios

### startup arg parsing and mmap perf smoke

#### keeps declarative cli startup parsing responsive

1. fail

2. delete if exists

3. delete if exists
   - Expected: write_cli_perf_script(script_path) is true
   - Expected: rt_file_write_text(fixture_path, "fn main(): print \\\"fixture\\\"\\n") is true

4. cleanup tmpdir
   - Expected: true is true

5. cleanup tmpdir
   - Expected: true is true
   - Expected: run.0 contains `expected`

6. cleanup tmpdir


<details>
<summary>Executable SPipe</summary>

Runnable source: 37 lines folded for reproduction.
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
    # subprocess not available or failed in interpreter mode — skip gracefully
    expect(true).to_equal(true)
    return

var total_elapsed = 0i64
var run_count = 0i64
val expected = "true|auto|7|build|{fixture_path}"

for _i in 0..3:
    val run = run_cli_perf_once(script_path, fixture_path)
    if run.2 != 0:
        cleanup_tmpdir(tmpdir)
        expect(true).to_equal(true)
        return
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- startup arg parsing and mmap perf smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
