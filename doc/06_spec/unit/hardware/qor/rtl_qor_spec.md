# Rtl Qor Specification

## Scenarios

### RTL QoR run model

#### computes area score with weighted hard macros

1. expect run area score


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = baseline_run()
expect run.area_score() == 2300
```

</details>

#### serializes to SDN-style storage text

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = baseline_run().to_sdn()
check(sdn.starts_with("rtl_qor_run"))
```

</details>

### RTL QoR comparison

#### computes deltas and improvement predicates

1. check

2. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val delta = compare_qor_runs(baseline_run(), candidate_run())
expect delta.lut_delta == -80
expect delta.ff_delta == -20
expect delta.fmax_delta == 5
check(delta.improved_area())
check(delta.improved_fmax())
```

</details>

### RTL QoR store

#### stores runs and serializes them

1. expect store len

2. check

3. expect latest unwrap


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = RtlQorStore.empty().with_run(baseline_run()).with_run(candidate_run())
expect store.len() == 2
val latest = store.latest_for_design("rv32i_core")
check(latest.?)
expect latest.unwrap().run_id == "cand"
```

</details>

### RTL QoR reports

#### renders run and comparison markdown

1. check

2. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_md = rtl_qor_run_markdown(baseline_run())
val compare_md = rtl_qor_compare_markdown(baseline_run(), candidate_run())
check(run_md.contains("RTL QoR Run"))
check(compare_md.contains("RTL QoR Delta"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/hardware/qor/rtl_qor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RTL QoR run model
- RTL QoR comparison
- RTL QoR store
- RTL QoR reports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

