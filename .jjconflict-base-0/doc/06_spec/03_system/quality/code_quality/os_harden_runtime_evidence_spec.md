# Os Harden Runtime Evidence Specification

> <details>

<!-- sdn-diagram:id=os_harden_runtime_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_harden_runtime_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_harden_runtime_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_harden_runtime_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Harden Runtime Evidence Specification

## Scenarios

### OS hardening runtime evidence

#### requires canary variation and text-write trap markers before writing green evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_os_harden_runtime_evidence_spec"
val (_clean_out, _clean_err, _clean_code) = rt_process_run("/bin/sh", ["-c", "rm -rf " + root + " && mkdir -p " + root])
val bad_log = root + "/bad.log"
expect(rt_file_write_text(bad_log, "[harden] canary arch=x86_64 value=111\n")).to_equal(true)
val bad = rt_process_run("bin/simple", ["run", "scripts/audit/os_harden_runtime_evidence.spl", "--", "--arch", "x86_64", "--out-root", root + "/out_bad", bad_log])
expect(bad.2).to_equal(1)

val good_log = root + "/good.log"
val body =
    "[harden] canary arch=x86_64 value=111\n" +
    "[harden] canary arch=x86_64 value=222\n" +
    "[harden] text_write_trap=pass\n"
expect(rt_file_write_text(good_log, body)).to_equal(true)
val good = rt_process_run("bin/simple", ["run", "scripts/audit/os_harden_runtime_evidence.spl", "--", "--arch", "x86_64", "--out-root", root + "/out_good", good_log])
expect(good.2).to_equal(0)

val canary = rt_file_read_text(root + "/out_good/x86_64/canary_runtime.json")
expect(canary).to_contain("\"differs_across_reboots\": true")
expect(canary).to_contain("\"distinct_sample_count\": 2")
val trap = rt_file_read_text(root + "/out_good/x86_64/text_write_trap.json")
expect(trap).to_contain("\"trap_observed\": true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/os_harden_runtime_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OS hardening runtime evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
