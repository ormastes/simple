# Jupyter Notebook Server System Specification

> Tests covering Jupyter Notebook Server E2E.

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should pass full E2E test in Docker container
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should pass full E2E test in Docker container")
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

- should start server and execute cell via HTTP + ZMQ locally
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should start server and execute cell via HTTP + ZMQ locally")
if not _has_notebook or not _has_binary or not _has_jupyter:
    print "SKIP: missing notebook/jupyter/binary"
    return
val helper = "test/03_system/tools/jupyter/helpers/run_server_check.py"
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

- should execute hello.ipynb via nbconvert and verify output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute hello.ipynb via nbconvert and verify output")
if not _has_jupyter or not _has_binary:
    print "SKIP: missing dependencies"
    return
val helper = "test/03_system/tools/jupyter/helpers/run_notebook_server_test.py"
if not rt_file_exists(helper):
    print "SKIP: {helper} not found"
else:
    val (stdout, stderr, code) = rt_process_run("python3", [helper, "--notebook", "test/03_system/tools/jupyter/fixtures/hello.ipynb", "--skip-server"])
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

- should execute state_persistence.ipynb and verify cross-cell state
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute state_persistence.ipynb and verify cross-cell state")
if not _has_jupyter or not _has_binary:
    print "SKIP: missing dependencies"
    return
val helper = "test/03_system/tools/jupyter/helpers/run_notebook_server_test.py"
if not rt_file_exists(helper):
    print "SKIP: {helper} not found"
else:
    val (stdout, stderr, code) = rt_process_run("python3", [helper, "--notebook", "test/03_system/tools/jupyter/fixtures/state_persistence.ipynb", "--skip-server"])
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

- should have kernel.json with display_name 'Simple'
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `Simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have kernel.json with display_name 'Simple'")
val (stdout, stderr, code) = rt_process_run("python3", ["-c", "import json; d=json.load(open('tools/jupyter/kernel.json')); print(d['display_name'])"])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("Simple")
```

</details>


</details>

<details>
<summary>Advanced: should have kernel_wrapper.py with valid Python syntax</summary>

#### should have kernel_wrapper.py with valid Python syntax _(slow)_

- should have kernel_wrapper.py with valid Python syntax
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have kernel_wrapper.py with valid Python syntax")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Jupyter Notebook Server E2E.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e959663b26a374f772f5f415bf929df90535bbf53582d8cb9afca3573f63e97b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e959663b26a374f772f5f415bf929df90535bbf53582d8cb9afca3573f63e97b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e959663b26a374f772f5f415bf929df90535bbf53582d8cb9afca3573f63e97b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl
mirror: doc/06_spec/03_system/tools/jupyter/jupyter_notebook_server_system_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/jupyter/jupyter_notebook_server_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/jupyter/jupyter_notebook_server_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass full E2E test in Docker container' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pass full E2E test in Docker container' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should start server and execute cell via HTTP + ZMQ locally' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should start server and execute cell via HTTP + ZMQ locally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:134:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute hello.ipynb via nbconvert and verify output' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute hello.ipynb via nbconvert and verify output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:159:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute state_persistence.ipynb and verify cross-cell state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:178:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have kernel.json with display_name 'Simple'' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl:185:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have kernel_wrapper.py with valid Python syntax' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
