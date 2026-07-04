# watcher_shb_integration_spec

> Watcher SHB Integration Specification

<!-- sdn-diagram:id=watcher_shb_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_shb_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_shb_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_shb_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# watcher_shb_integration_spec

Watcher SHB Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-INT-001 to #WATCH-INT-010 |
| Category | Integration |
| Status | Active |
| Source | `test/02_integration/watcher/watcher_shb_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Watcher SHB Integration Specification

Tests end-to-end SHB cache generation and validation through the watcher.

## Scenarios

### Watcher SHB Integration

### fresh SHB cache hit

<details>
<summary>Advanced: skips recompilation for unchanged files</summary>

#### skips recompilation for unchanged files _(slow)_

- int reset
- int add source
- int compile shb
   - Expected: int_compile_log_len() equals `1`
   - Expected: status equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
int_reset()
int_add_source("src/main.spl", 12345)
int_compile_shb("src/main.spl")
expect(int_compile_log_len()).to_equal(1)
val status = int_check_freshness("src/main.spl")
expect(status).to_equal(0)
```

</details>


</details>

### stale SHB detection

<details>
<summary>Advanced: detects missing SHB</summary>

#### detects missing SHB _(slow)_

- int reset
- int add source
   - Expected: status equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
int_reset()
int_add_source("src/main.spl", 12345)
val status = int_check_freshness("src/main.spl")
expect(status).to_equal(3)
```

</details>


</details>

### batch processing

<details>
<summary>Advanced: processes multiple files</summary>

#### processes multiple files _(slow)_

- int reset
- int add source
- int add source
- int add source
- int compile shb
- int compile shb
- int compile shb
   - Expected: int_compile_log_len() equals `3`
   - Expected: int_shb_paths_len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
int_reset()
int_add_source("src/a.spl", 100)
int_add_source("src/b.spl", 200)
int_add_source("src/c.spl", 300)
int_compile_shb("src/a.spl")
int_compile_shb("src/b.spl")
int_compile_shb("src/c.spl")
expect(int_compile_log_len()).to_equal(3)
expect(int_shb_paths_len()).to_equal(3)
```

</details>


</details>

### dependency invalidation

<details>
<summary>Advanced: detects when dependency interface changes</summary>

#### detects when dependency interface changes _(slow)_

- int reset
- int add source
- int add source
- int compile shb
- int add source
   - Expected: new_dep_hash != dep_hash is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
int_reset()
int_add_source("src/dep.spl", 100)
int_add_source("src/main.spl", 200)
val dep_hash = int_compile_shb("src/dep.spl")
int_compile_shb("src/main.spl")
int_add_source("src/dep.spl", 999)
val new_dep_hash = int_compile_shb("src/dep.spl")
expect(new_dep_hash != dep_hash).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
