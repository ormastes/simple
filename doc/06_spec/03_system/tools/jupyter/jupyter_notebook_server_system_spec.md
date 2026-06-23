# Jupyter Notebook Server System Specification

> <details>

<!-- sdn-diagram:id=jupyter_notebook_server_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jupyter_notebook_server_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jupyter_notebook_server_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jupyter_notebook_server_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jupyter Notebook Server System Specification

## Scenarios

### Jupyter Notebook Server E2E

<details>
<summary>Advanced: should pass full E2E test in Docker container</summary>

#### should pass full E2E test in Docker container _(slow)_

1. print "SKIP: simple-jupyter-test Docker image not built
2. print "stderr
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_docker:
    print "SKIP: docker not available"
    return
if not _has_binary:
    print "SKIP: Simple runtime not found"
    return
if not rt_file_exists("scripts/test/jupyter-docker-test.shs"):
    print "SKIP: scripts/test/jupyter-docker-test.shs not found"
    return
if not rt_file_exists("tools/docker/Dockerfile.jupyter-test"):
    print "SKIP: tools/docker/Dockerfile.jupyter-test not found"
    return
# Only run if Docker image is already built (building takes too long)
val (img_out, img_err, img_code) = rt_process_run("docker", ["image", "inspect", "simple-jupyter-test"])
if img_code != 0:
    print "SKIP: simple-jupyter-test Docker image not built (run: sh scripts/test/jupyter-docker-test.shs)"
    return
print "Running E2E test in Docker container..."
val (stdout, stderr, code) = rt_process_run("docker", ["run", "--rm", "simple-jupyter-test"])
print stdout
if code != 0 and stderr.trim() != "":
    print "stderr (tail): {stderr.substring(stderr.len() - 300)}"
expect(code).to_equal(0)
expect(stdout).to_contain("ALL CHECKS PASSED")
```

</details>


</details>

<details>
<summary>Advanced: should start server and execute cell via HTTP + ZMQ locally</summary>

#### should start server and execute cell via HTTP + ZMQ locally _(slow)_

1. print "stderr
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_notebook or not _has_binary or not _has_jupyter:
    print "SKIP: missing notebook/jupyter/binary"
    return
val helper = "test/system/jupyter/helpers/run_server_check.py"
if not rt_file_exists(helper):
    print "SKIP: {helper} not found"
else:
    val (stdout, stderr, code) = rt_process_run("python3", [helper])
    print stdout
    if code != 0 and stderr.trim() != "":
        val tail_start = stderr.len() - 300
        if tail_start < 0:
            print "stderr: {stderr}"
        else:
            print "stderr (tail): {stderr.substring(tail_start)}"
    expect(code).to_equal(0)
    expect(stdout).to_contain("ALL CHECKS PASSED")
```

</details>


</details>

<details>
<summary>Advanced: should execute hello.ipynb via nbconvert and verify output</summary>

#### should execute hello.ipynb via nbconvert and verify output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_jupyter or not _has_binary:
    print "SKIP: missing dependencies"
    return
val helper = "test/system/jupyter/helpers/run_notebook_server_test.py"
if not rt_file_exists(helper):
    print "SKIP: {helper} not found"
else:
    val (stdout, stderr, code) = rt_process_run("python3", [helper, "--notebook", "test/system/jupyter/fixtures/hello.ipynb", "--skip-server"])
    print stdout
    if code != 0 and stderr.trim() != "":
        print "stderr: {stderr}"
    expect(code).to_equal(0)
    expect(stdout).to_contain("ALL CHECKS PASSED")
```

</details>


</details>

<details>
<summary>Advanced: should execute state_persistence.ipynb and verify cross-cell state</summary>

#### should execute state_persistence.ipynb and verify cross-cell state _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_jupyter or not _has_binary:
    print "SKIP: missing dependencies"
    return
val helper = "test/system/jupyter/helpers/run_notebook_server_test.py"
if not rt_file_exists(helper):
    print "SKIP: {helper} not found"
else:
    val (stdout, stderr, code) = rt_process_run("python3", [helper, "--notebook", "test/system/jupyter/fixtures/state_persistence.ipynb", "--skip-server"])
    print stdout
    if code != 0 and stderr.trim() != "":
        print "stderr: {stderr}"
    expect(code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: should have kernel.json with display_name 'Simple'</summary>

#### should have kernel.json with display_name 'Simple' _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = rt_process_run("python3", ["-c", "import json; d=json.load(open('tools/jupyter/kernel.json')); print(d['display_name'])"])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("Simple")
```

</details>


</details>

<details>
<summary>Advanced: should have kernel_wrapper.py with valid Python syntax</summary>

#### should have kernel_wrapper.py with valid Python syntax _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = rt_process_run("python3", ["-c", "import ast; ast.parse(open('tools/jupyter/kernel_wrapper.py').read()); print('ok')"])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("ok")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jupyter Notebook Server E2E

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
