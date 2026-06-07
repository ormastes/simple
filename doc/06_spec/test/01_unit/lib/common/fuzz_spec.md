# Fuzz Specification

> <details>

<!-- sdn-diagram:id=fuzz_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fuzz_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fuzz_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fuzz_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fuzz Specification

## Scenarios

### Fuzzing Library

#### keeps fuzz configuration and result models available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = fuzz_source()

expect(source).to_contain("struct FuzzConfig:")
expect(source).to_contain("struct FuzzResult:")
expect(source).to_contain("fn fuzz_default_config() -> FuzzConfig")
expect(source).to_contain("fn fuzz_config(iters: i64, s: i64) -> FuzzConfig")
```

</details>

#### keeps deterministic generators available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = fuzz_source()

expect(source).to_contain("fn gen_int(rng_state: (i64, i64, i64, i64), min_v: i64, max_v: i64)")
expect(source).to_contain("fn gen_text(rng_state: (i64, i64, i64, i64), min_len: i64, max_len: i64)")
expect(source).to_contain("fn gen_identifier(rng_state: (i64, i64, i64, i64), min_len: i64, max_len: i64)")
expect(source).to_contain("fn gen_sdn_value(rng, max_depth: i64)")
```

</details>

#### keeps shrinking, corpus, and reporting entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = fuzz_source()

expect(source).to_contain("fn shrink_int(n: i64) -> [i64]")
expect(source).to_contain("fn fuzz_check(name: text, gen_fn, prop_fn, config: FuzzConfig) -> FuzzResult")
expect(source).to_contain("fn corpus_load(dir: text) -> [text]")
expect(source).to_contain("fn fuzz_report(result: FuzzResult) -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/fuzz_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Fuzzing Library

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
