# watcher_smf_integration_spec

> Watcher SMF Integration Specification

<!-- sdn-diagram:id=watcher_smf_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_smf_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_smf_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_smf_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# watcher_smf_integration_spec

Watcher SMF Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-INT-011 to #WATCH-INT-020 |
| Category | Integration |
| Status | Active |
| Source | `test/02_integration/watcher/watcher_smf_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Watcher SMF Integration Specification

Tests end-to-end SMF cache generation and validation through the watcher.

## Scenarios

### Watcher SMF Integration

### compile and cache

<details>
<summary>Advanced: stores options hash in SMF</summary>

#### stores options hash in SMF _(slow)_

1. smf int reset
2. smf int compile
   - Expected: smf_compile_log_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_int_reset()
smf_int_compile("src/main.spl", "build/smf/main.smf", 99999)
val idx = smf_find("build/smf/main.smf")
expect(idx).to_be_greater_than(-1)
expect(smf_compile_log_len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: verifies matching options</summary>

#### verifies matching options _(slow)_

1. smf int reset
2. smf int compile
   - Expected: status equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_int_reset()
smf_int_compile("src/main.spl", "build/smf/main.smf", 99999)
val status = smf_int_check("build/smf/main.smf", 99999)
expect(status).to_equal(0)
```

</details>


</details>

### options mismatch detection

<details>
<summary>Advanced: detects backend change</summary>

#### detects backend change _(slow)_

1. smf int reset
2. smf int compile
   - Expected: status equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_int_reset()
smf_int_compile("src/main.spl", "build/smf/main.smf", 11111)
val status = smf_int_check("build/smf/main.smf", 22222)
expect(status).to_equal(2)
```

</details>


</details>

<details>
<summary>Advanced: detects missing SMF</summary>

#### detects missing SMF _(slow)_

1. smf int reset
   - Expected: status equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_int_reset()
val status = smf_int_check("build/smf/main.smf", 11111)
expect(status).to_equal(3)
```

</details>


</details>

### recompilation

<details>
<summary>Advanced: recompiles when options change</summary>

#### recompiles when options change _(slow)_

1. smf int reset
2. smf int compile
   - Expected: smf_compile_log_len() equals `1`
   - Expected: status equals `2`
3. smf int compile
   - Expected: smf_compile_log_len() equals `2`
   - Expected: status2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_int_reset()
smf_int_compile("src/main.spl", "build/smf/main.smf", 11111)
expect(smf_compile_log_len()).to_equal(1)
val status = smf_int_check("build/smf/main.smf", 22222)
expect(status).to_equal(2)
smf_int_compile("src/main.spl", "build/smf/main.smf", 22222)
expect(smf_compile_log_len()).to_equal(2)
val status2 = smf_int_check("build/smf/main.smf", 22222)
expect(status2).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
