# Tmp Signal Extract Specification

> <details>

<!-- sdn-diagram:id=tmp_signal_extract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_signal_extract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_signal_extract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_signal_extract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Signal Extract Specification

## Scenarios

### signal extract

#### extracts signal

- mark
- mark
- mark
   - Expected: signal equals `wake`
- mark


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mark("start")
val parsed = json_parse(r"""{"session_id":"s","kind":"signal","message":"wake payload","signal":"wake","timestamp_ms":1000,"event_id":"event-1"}""")
mark("parsed")
val signal = json_to_string(json_object_get(parsed, "signal"))
mark("signal:" + (signal ?? ""))
expect(signal).to_equal("wake")
mark("done")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_signal_extract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- signal extract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
