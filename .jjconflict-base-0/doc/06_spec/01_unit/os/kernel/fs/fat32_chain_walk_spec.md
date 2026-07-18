# FAT32 Cluster-Chain Walk — Wave-4b Regression Spec

> Verifies that `Fat32Filesystem.read_cluster_chain`:

<!-- sdn-diagram:id=fat32_chain_walk_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fat32_chain_walk_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fat32_chain_walk_spec -> std
fat32_chain_walk_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fat32_chain_walk_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FAT32 Cluster-Chain Walk — Wave-4b Regression Spec

Verifies that `Fat32Filesystem.read_cluster_chain`:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/fat32_chain_walk_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**Bug:** fat32_no_cycle_guard_chain_walk_2026-06-11
Verifies that `Fat32Filesystem.read_cluster_chain`:
  1. Correctly walks a linear N-cluster chain to EOC.
  2. Terminates at EOC and returns the chain without the EOC value.
  3. Returns Err on a cyclic FAT (entry pointing back into the chain).
  4. Returns Err on a FREE cluster mid-chain.
  5. Returns Err on a BAD cluster (0x0FFFFFF7) mid-chain.
  6. Returns Err when start cluster < 2.

The mock block device stores FAT sectors in memory so tests never touch
real hardware.  Geometry is configured via `Fat32Filesystem.make_for_chain_test`.

## Scenarios

### fat32 read_cluster_chain — wave-4b cycle guard

### linear chain walk

#### single-cluster chain (FAT[2]=EOC) returns chain length 1

- var sec =  zero sector
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_ok() is true
   - Expected: chain.len() equals `1`
   - Expected: chain[0] equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sec = _zero_sector()
sec = _fat_put(sec, 2u32, _eoc())
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(10u32)
val result = fs.read_cluster_chain(dev, 2u32)
expect(result.is_ok()).to_equal(true)
val chain = result.unwrap()
expect(chain.len()).to_equal(1)
expect(chain[0]).to_equal(2u32)
```

</details>

#### three-cluster chain (2→3→4→EOC) returns [2, 3, 4]

- var sec =  zero sector
- sec =  fat put
- sec =  fat put
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_ok() is true
   - Expected: chain.len() equals `3`
   - Expected: chain[0] equals `2u32`
   - Expected: chain[1] equals `3u32`
   - Expected: chain[2] equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sec = _zero_sector()
sec = _fat_put(sec, 2u32, 3u32)
sec = _fat_put(sec, 3u32, 4u32)
sec = _fat_put(sec, 4u32, _eoc())
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(100u32)
val result = fs.read_cluster_chain(dev, 2u32)
expect(result.is_ok()).to_equal(true)
val chain = result.unwrap()
expect(chain.len()).to_equal(3)
expect(chain[0]).to_equal(2u32)
expect(chain[1]).to_equal(3u32)
expect(chain[2]).to_equal(4u32)
```

</details>

#### EOC at 0x0FFFFFF8 (minimum EOC) terminates correctly

- var sec =  zero sector
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sec = _zero_sector()
sec = _fat_put(sec, 2u32, _eoc_min())
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(10u32)
val result = fs.read_cluster_chain(dev, 2u32)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().len()).to_equal(1)
```

</details>

#### chain starting at cluster 5 returns correct list

- var sec =  zero sector
- sec =  fat put
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_ok() is true
   - Expected: chain.len() equals `2`
   - Expected: chain[0] equals `5u32`
   - Expected: chain[1] equals `6u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sec = _zero_sector()
sec = _fat_put(sec, 5u32, 6u32)
sec = _fat_put(sec, 6u32, _eoc())
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(10u32)
val result = fs.read_cluster_chain(dev, 5u32)
expect(result.is_ok()).to_equal(true)
val chain = result.unwrap()
expect(chain.len()).to_equal(2)
expect(chain[0]).to_equal(5u32)
expect(chain[1]).to_equal(6u32)
```

</details>

### cycle guard

#### cyclic FAT (2→3→2) with fuel=2 returns Err

- var sec =  zero sector
- sec =  fat put
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# step1: push 2, fuel→1; step2: push 3, fuel→0; next FAT[3]=2 → Err
var sec = _zero_sector()
sec = _fat_put(sec, 2u32, 3u32)
sec = _fat_put(sec, 3u32, 2u32)
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(2u32)
val result = fs.read_cluster_chain(dev, 2u32)
expect(result.is_err()).to_equal(true)
```

</details>

#### chain longer than fuel (4 clusters, fuel=3) returns Err

- var sec =  zero sector
- sec =  fat put
- sec =  fat put
- sec =  fat put
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sec = _zero_sector()
sec = _fat_put(sec, 2u32, 3u32)
sec = _fat_put(sec, 3u32, 4u32)
sec = _fat_put(sec, 4u32, 5u32)
sec = _fat_put(sec, 5u32, _eoc())
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(3u32)
val result = fs.read_cluster_chain(dev, 2u32)
expect(result.is_err()).to_equal(true)
```

</details>

#### chain exactly at fuel (3 clusters, fuel=3) succeeds

- var sec =  zero sector
- sec =  fat put
- sec =  fat put
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sec = _zero_sector()
sec = _fat_put(sec, 2u32, 3u32)
sec = _fat_put(sec, 3u32, 4u32)
sec = _fat_put(sec, 4u32, _eoc())
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(3u32)
val result = fs.read_cluster_chain(dev, 2u32)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().len()).to_equal(3)
```

</details>

### corruption guards

#### FREE cluster (0x00000000) mid-chain returns Err

- var sec =  zero sector
- sec =  fat put
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sec = _zero_sector()
sec = _fat_put(sec, 2u32, 3u32)
sec = _fat_put(sec, 3u32, _free())
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(10u32)
val result = fs.read_cluster_chain(dev, 2u32)
expect(result.is_err()).to_equal(true)
```

</details>

#### BAD cluster marker (0x0FFFFFF7) mid-chain returns Err

- var sec =  zero sector
- sec =  fat put
- sec =  fat put
- var dev = MockFatDevice new
- dev = dev with sector
- var fs =  make fs
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sec = _zero_sector()
sec = _fat_put(sec, 2u32, 3u32)
sec = _fat_put(sec, 3u32, _bad())
var dev = MockFatDevice.new()
dev = dev.with_sector(32u64, sec)
var fs = _make_fs(10u32)
val result = fs.read_cluster_chain(dev, 2u32)
expect(result.is_err()).to_equal(true)
```

</details>

### invalid start cluster

#### start cluster 0 returns Err

- var dev = MockFatDevice new
- var fs =  make fs
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = MockFatDevice.new()
var fs = _make_fs(10u32)
val result = fs.read_cluster_chain(dev, 0u32)
expect(result.is_err()).to_equal(true)
```

</details>

#### start cluster 1 returns Err (reserved)

- var dev = MockFatDevice new
- var fs =  make fs
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = MockFatDevice.new()
var fs = _make_fs(10u32)
val result = fs.read_cluster_chain(dev, 1u32)
expect(result.is_err()).to_equal(true)
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
