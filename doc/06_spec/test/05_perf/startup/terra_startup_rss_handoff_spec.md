# Terra Startup Rss Handoff Specification

> Tests covering:

## Scenarios

### Terra startup/RSS handoff

#### should validate synthetic evidence and reject a forged successful count

- Run the checker selftest with 15 raw successful samples
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TERRA-STARTUP-RSS-001
step("Run the checker selftest with 15 raw successful samples")
val (out, code) = run(CHECK + " --selftest")
expect(out).to_contain("PASS: terra handoff selftest")
expect(out).to_contain("N=15")
expect(code).to_equal(0)
```

</details>

#### should require the production handoff instead of treating absence as success

- Run the checker against the production default receipt
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TERRA-STARTUP-RSS-001
step("Run the checker against the production default receipt")
val (out, code) = run(CHECK)
expect(code).to_equal(0)
expect(out).to_contain("PASS: terra startup/RSS handoff admitted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | REQ-TERRA-STARTUP-RSS-001 |
| Source | `test/05_perf/startup/terra_startup_rss_handoff_spec.spl` |
| Updated | 2026-09-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Terra startup/RSS handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** REQ-TERRA-STARTUP-RSS-001


<!-- sdn-diagram:id=terra_startup_rss_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terra_startup_rss_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terra_startup_rss_handoff_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terra_startup_rss_handoff_spec.arch hash=sha256:auto
+-----+      +--------------------------------+
| std | ---> | terra_startup_rss_handoff_spec |
+-----+      +--------------------------------+
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |
