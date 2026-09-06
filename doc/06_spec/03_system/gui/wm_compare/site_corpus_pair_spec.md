# Site Corpus Pair Specification

> <details>

<!-- sdn-diagram:id=site_corpus_pair_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=site_corpus_pair_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

site_corpus_pair_spec -> std
site_corpus_pair_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=site_corpus_pair_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Site Corpus Pair Specification

## Scenarios

### famous-site corpus pair comparison

#### does not accept captures with mismatched viewport metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val pixels = [0xFF000000u32, 0xFFFFFFFFu32]
val chrome = CaptureResult(
    pixels: pixels,
    width: 1, height: 2,
    backend_name: "chrome", success: true, error: ""
)
val simple = CaptureResult(
    pixels: pixels,
    width: 2, height: 1,
    backend_name: "simple", success: true, error: ""
)
val pair = compare_site_sample(sample, chrome, simple, _opts(2, 1))
expect(pair.exact).to_equal(false)
expect(pair.accepted).to_equal(false)
expect(pair.chrome_ok).to_equal(false)
expect(pair.chrome_error).to_contain("viewport metadata mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/site_corpus_pair_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- famous-site corpus pair comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
