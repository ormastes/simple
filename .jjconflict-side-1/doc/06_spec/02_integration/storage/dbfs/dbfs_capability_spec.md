# dbfs_capability_spec

> DBFS Capability Extension Probe Specification

<!-- sdn-diagram:id=dbfs_capability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_capability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_capability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_capability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_capability_spec

DBFS Capability Extension Probe Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_capability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Capability Extension Probe Specification

Verifies DbFsDriver reports capabilities correctly:
  Positive: POSIX-shim, xattr, ACL, snapshot, COW, LargeFiles
  Negative: no dedup, no hard-links, no DirectIo

## Scenarios

### DBFS Capability — positive probes

#### PosixCompat capability is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.PosixCompat).?).to_equal(true)
```

</details>

#### Xattr capability is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.Xattr).?).to_equal(true)
```

</details>

#### Acl capability is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.Acl).?).to_equal(true)
```

</details>

#### Snapshot capability is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.Snapshot).?).to_equal(true)
```

</details>

#### COW capability is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.COW).?).to_equal(true)
```

</details>

#### LargeFiles capability is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.LargeFiles).?).to_equal(true)
```

</details>

### DBFS Capability — negative probes (out-of-scope ops)

#### Dedup capability is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.Dedup).?).to_equal(false)
```

</details>

#### Hardlinks capability is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.Hardlinks).?).to_equal(false)
```

</details>

#### DirectIo capability is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
expect(d.probe(Capability.DirectIo).?).to_equal(false)
```

</details>

### DBFS Capability — capabilities() set

#### capabilities() returns a FsCapabilitySet containing PosixCompat

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
val caps = d.capabilities()
expect(caps.has(Capability.PosixCompat)).to_equal(true)
```

</details>

#### capabilities() does not contain Dedup

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_driver()
val caps = d.capabilities()
expect(caps.has(Capability.Dedup)).to_equal(false)
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
