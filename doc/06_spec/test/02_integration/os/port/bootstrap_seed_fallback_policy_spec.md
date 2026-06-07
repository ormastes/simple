# Bootstrap Seed Fallback Policy Specification

> <details>

<!-- sdn-diagram:id=bootstrap_seed_fallback_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_seed_fallback_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_seed_fallback_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_seed_fallback_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Seed Fallback Policy Specification

## Scenarios

### bootstrap seed fallback policy

#### keeps bootstrap_main free of seed-wrapper fallback generation

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/cli/bootstrap_main.spl") ?? ""
val bin_catalog = rt_file_read_text("bin/FILE.md") ?? ""
expect(src).to_contain("bootstrap_main cannot emit a seed-wrapper fallback")
expect(forbidden_bootstrap_marker(src)).to_equal("ok")
expect(rt_file_exists("bin/simple.bootstrap_seed_wrapper.c")).to_equal(false)
expect(bin_catalog.contains("bootstrap_seed_wrapper")).to_equal(false)
```

</details>

#### rejects driver bootstrap seed and stub fallbacks

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/compiler/80.driver/driver_bootstrap.spl") ?? ""
expect(src).to_contain("bootstrap seed-wrapper fallback was removed")
expect(src).to_contain("bootstrap driver stub LLVM was removed")
expect(src).to_contain("bootstrap direct stub IR was removed")
expect(forbidden_bootstrap_marker(src)).to_equal("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bootstrap seed fallback policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
