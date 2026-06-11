# watcher_client_spec

> Watcher Client Specification

<!-- sdn-diagram:id=watcher_client_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_client_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_client_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_client_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# watcher_client_spec

Watcher Client Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-031 to #WATCH-040 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/watcher/watcher_client_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Watcher Client Specification

Tests client API for requesting cache artifacts from the watcher.
Uses module-level functions for all state mutations (closure limitation).

## Scenarios

### WatcherClient

### check_shb_freshness

#### returns FRESH for cached SHB

1. client reset
2. client add shb
   - Expected: result equals `FRESH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
client_add_shb(".build/headers/src/main.spl", 12345)
val result = mock_check_shb("src/main.spl", ".build/headers")
expect(result).to_equal(FRESH)
```

</details>

#### returns MISSING for uncached SHB

1. client reset
   - Expected: result equals `MISSING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
val result = mock_check_shb("src/main.spl", ".build/headers")
expect(result).to_equal(MISSING)
```

</details>

### check_smf_freshness

#### returns FRESH for matching options

1. client reset
2. client add smf
   - Expected: result equals `FRESH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
client_add_smf("build/smf/src/main.spl", 99999)
val result = mock_check_smf("src/main.spl", "build/smf", 99999)
expect(result).to_equal(FRESH)
```

</details>

#### returns STALE for mismatched options

1. client reset
2. client add smf
   - Expected: result equals `STALE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
client_add_smf("build/smf/src/main.spl", 99999)
val result = mock_check_smf("src/main.spl", "build/smf", 11111)
expect(result).to_equal(STALE)
```

</details>

#### returns MISSING for uncached SMF

1. client reset
   - Expected: result equals `MISSING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
val result = mock_check_smf("src/main.spl", "build/smf", 99999)
expect(result).to_equal(MISSING)
```

</details>

### get_or_generate_shb

#### returns cached when available

1. client reset
2. client add shb
   - Expected: result equals `cached`
   - Expected: client_gen_files_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
client_add_shb(".build/headers/src/main.spl", 12345)
val result = mock_get_or_generate_shb("src/main.spl")
expect(result).to_equal("cached")
expect(client_gen_files_len()).to_equal(0)
```

</details>

#### generates inline when not cached

1. client reset
   - Expected: result equals `generated`
   - Expected: client_gen_files_len() equals `1`
   - Expected: client_gen_file_at(0) equals `src/main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
val result = mock_get_or_generate_shb("src/main.spl")
expect(result).to_equal("generated")
expect(client_gen_files_len()).to_equal(1)
expect(client_gen_file_at(0)).to_equal("src/main.spl")
```

</details>

#### caches after generation

1. client reset
2. mock get or generate shb
   - Expected: result2 equals `cached`
   - Expected: client_gen_files_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
mock_get_or_generate_shb("src/main.spl")
val result2 = mock_get_or_generate_shb("src/main.spl")
expect(result2).to_equal("cached")
expect(client_gen_files_len()).to_equal(1)
```

</details>

### get_or_generate_smf

#### returns cached for matching options

1. client reset
2. client add smf
   - Expected: result equals `cached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
client_add_smf("build/smf/src/main.spl", 55555)
val result = mock_get_or_generate_smf("src/main.spl", 55555)
expect(result).to_equal("cached")
```

</details>

#### regenerates for mismatched options

1. client reset
2. client add smf
   - Expected: result equals `generated`
   - Expected: client_gen_files_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
client_add_smf("build/smf/src/main.spl", 55555)
val result = mock_get_or_generate_smf("src/main.spl", 99999)
expect(result).to_equal("generated")
expect(client_gen_files_len()).to_equal(1)
```

</details>

#### generates for missing SMF

1. client reset
   - Expected: result equals `generated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
client_reset()
val result = mock_get_or_generate_smf("src/main.spl", 55555)
expect(result).to_equal("generated")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
