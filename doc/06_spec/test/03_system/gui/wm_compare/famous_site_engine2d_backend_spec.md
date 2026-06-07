# Famous Site Engine2d Backend Specification

> <details>

<!-- sdn-diagram:id=famous_site_engine2d_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=famous_site_engine2d_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

famous_site_engine2d_backend_spec -> std
famous_site_engine2d_backend_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=famous_site_engine2d_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Famous Site Engine2d Backend Specification

## Scenarios

### famous-site Engine2D backend coverage

#### matches default Simple Web Renderer pixels for every corpus page

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_all_engine_backend_samples_match_default(40, 30)).to_equal(true)
```

</details>

#### matches default Simple Web Renderer pixels for representative full-size corpus pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(_engine_backend_matches_default_for_sample(samples[0], 160, 120)).to_equal(true)
expect(_engine_backend_matches_default_for_sample(samples[44], 160, 120)).to_equal(true)
expect(_engine_backend_matches_default_for_sample(samples[99], 160, 120)).to_equal(true)
```

</details>

#### keeps direct layout software and cpu backend pixels identical

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = build_famous_site_sample_corpus()
expect(_layout_software_backend_matches_cpu_for_sample(samples[0], 160, 120)).to_equal(true)
expect(_layout_software_backend_matches_cpu_for_sample(samples[44], 160, 120)).to_equal(true)
expect(_layout_software_backend_matches_cpu_for_sample(samples[99], 160, 120)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/famous_site_engine2d_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- famous-site Engine2D backend coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
