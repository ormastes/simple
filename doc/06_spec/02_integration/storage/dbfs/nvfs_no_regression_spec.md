# nvfs_no_regression_spec

> NVFS No-Regression Specification

<!-- sdn-diagram:id=nvfs_no_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_no_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_no_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_no_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvfs_no_regression_spec

NVFS No-Regression Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/nvfs_no_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

NVFS No-Regression Specification

Verifies the live NVFS driver surfaces still work after the blob-backend refactor:
  - native NvfsDriver open/read/write/stat
  - Posix shim open/pwrite/ftruncate/stat

## Scenarios

### NVFS no-regression — NvfsDriver

#### NvfsDriver mounts and exposes the root inode

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_nvfs()
val root = d.root().unwrap()
expect(root.id).to_equal(1)
```

</details>

#### NvfsDriver open + write + read round-trips bytes

1. d write
   - Expected: n equals `7`
   - Expected: got[0] equals `110`
   - Expected: got[6] equals `107`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_nvfs()
val fh = d.open(Path(raw: "/nvfs_reg.bin"), OpenFlags(bits: 2)).unwrap()
val payload: [u8] = [110, 118, 102, 115, 45, 111, 107]
d.write(fh, 0, payload).unwrap()
var got: [u8] = [0, 0, 0, 0, 0, 0, 0]
val n = d.read(fh, 0, got).unwrap()
expect(n).to_equal(7)
expect(got[0]).to_equal(110)
expect(got[6]).to_equal(107)
```

</details>

#### NvfsDriver stat returns correct size after write

1. d write

2. d close
   - Expected: stat.size equals `5`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_nvfs()
val fh = d.open(Path(raw: "/size_test.bin"), OpenFlags(bits: 2)).unwrap()
val payload: [u8] = [49, 50, 51, 52, 53]
d.write(fh, 0, payload).unwrap()
d.close(fh).unwrap()
val stat = d.stat(Path(raw: "/size_test.bin")).unwrap()
expect(stat.size).to_equal(5)
```

</details>

#### NvfsDriver rejects non-append positional overwrite on the native driver

1. d write
   - Expected: res.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_nvfs()
val fh = d.open(Path(raw: "/append_only.bin"), OpenFlags(bits: 2)).unwrap()
val payload: [u8] = [1, 2, 3, 4]
d.write(fh, 0, payload).unwrap()
val patch: [u8] = [9]
val res = d.pwrite(fh, 1, patch)
expect(res.is_err()).to_equal(true)
```

</details>

### NVFS no-regression — NvfsPosixDriver

#### NvfsPosixDriver mounts and exposes the root inode

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_nvfs_posix()
val root = d.root().unwrap()
expect(root.id).to_equal(1)
```

</details>

#### NvfsPosixDriver open + write + read round-trips bytes

1. d write
   - Expected: n equals `8`
   - Expected: got[0] equals `112`
   - Expected: got[7] equals `107`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_nvfs_posix()
val fh = d.open(Path(raw: "/posix_reg.txt"), OpenFlags.write_only().with_append()).unwrap()
val payload: [u8] = [112, 111, 115, 105, 120, 45, 111, 107]
d.write(fh, 0, payload).unwrap()
var got: [u8] = [0, 0, 0, 0, 0, 0, 0, 0]
val n = d.read(fh, 0, got).unwrap()
expect(n).to_equal(8)
expect(got[0]).to_equal(112)
expect(got[7]).to_equal(107)
```

</details>

#### NvfsPosixDriver pwrite updates bytes in place

1. d write

2. d pwrite
   - Expected: n equals `4`
   - Expected: got[0] equals `65`
   - Expected: got[2] equals `66`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_nvfs_posix()
val fh = d.open(Path(raw: "/rewrite.txt"), OpenFlags.write_only().with_append()).unwrap()
val seed: [u8] = [65, 65, 65, 65]
d.write(fh, 0, seed).unwrap()
val patch: [u8] = [66, 66]
d.pwrite(fh, 2, patch).unwrap()
var got: [u8] = [0, 0, 0, 0]
val n = d.pread(fh, 0, got).unwrap()
expect(n).to_equal(4)
expect(got[0]).to_equal(65)
expect(got[2]).to_equal(66)
```

</details>

#### NvfsPosixDriver stat returns updated size after ftruncate

1. d write

2. d ftruncate
   - Expected: stat.size equals `10`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_nvfs_posix()
val fh = d.open(Path(raw: "/file.txt"), OpenFlags.write_only().with_append()).unwrap()
val payload: [u8] = [1, 2, 3, 4]
d.write(fh, 0, payload).unwrap()
d.ftruncate(fh, 10).unwrap()
val stat = d.fstat(fh).unwrap()
expect(stat.size).to_equal(10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
