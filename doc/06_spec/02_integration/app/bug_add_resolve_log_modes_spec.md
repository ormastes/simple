# Bug Add Resolve Log Modes Specification

> 1.  setup fixture

<!-- sdn-diagram:id=bug_add_resolve_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bug_add_resolve_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bug_add_resolve_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bug_add_resolve_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bug Add Resolve Log Modes Specification

## Scenarios

### bug add and resolve log mode CLI options

#### bug-add shows shared log options in help

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_bug_add(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### bug-resolve shows shared log options in help

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_bug_resolve(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### bug-add supports log-mode json

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_bug_add(["--id=log_mode_bug_001", "--severity=p2", "--title=fixture", "--file=src/main.spl", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"bug-add\"")
expect(out).to_contain("\"id\":\"log_mode_bug_001\"")
```

</details>

#### bug-resolve supports log-mode json

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (_add_out, _add_err, _add_code) = _run_bug_add(["--id=log_mode_bug_002", "--severity=p2", "--title=fixture", "--file=src/main.spl"])
val (out, err, code) = _run_bug_resolve(["--id=log_mode_bug_002", "--date=2026-05-24", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"bug-resolve\"")
expect(out).to_contain("\"id\":\"log_mode_bug_002\"")
```

</details>

#### bug-add supports dot progress

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_bug_add(["--id=log_mode_bug_003", "--severity=p2", "--title=fixture", "--file=src/main.spl", "--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Added bug log_mode_bug_003")
```

</details>

#### bug-add rejects invalid log mode

1.  setup fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_bug_add(["--id=log_mode_bug_004", "--title=fixture", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### bug-resolve rejects invalid log mode

1.  setup fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_bug_resolve(["--id=log_mode_bug_004", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/bug_add_resolve_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bug add and resolve log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
