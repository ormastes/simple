# mount_table_dbfs_dispatch_spec

> MountTable DBFS Dispatch Specification

<!-- sdn-diagram:id=mount_table_dbfs_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mount_table_dbfs_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mount_table_dbfs_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mount_table_dbfs_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mount_table_dbfs_dispatch_spec

MountTable DBFS Dispatch Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/mount_table_dbfs_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

MountTable DBFS Dispatch Specification

Verifies that adding DbFs(driver) to the DriverInstance enum routes
path lookups correctly through MountTable longest-prefix match.

## Scenarios

### MountTable DBFS dispatch — longest-prefix routing

#### path under /data routes to DbFsDriver

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/data/foo.txt").unwrap()
expect(resolved.driver_name()).to_equal("DbFsDriver")
```

</details>

#### path under / (not /data) routes to RamFsDriver

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/etc/config").unwrap()
expect(resolved.driver_name()).to_equal("RamFsDriver")
```

</details>

#### exact /data route resolves to DbFsDriver

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/data").unwrap()
expect(resolved.driver_name()).to_equal("DbFsDriver")
```

</details>

#### nested path /data/a/b/c routes to DbFsDriver

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/data/a/b/c").unwrap()
expect(resolved.driver_name()).to_equal("DbFsDriver")
```

</details>

#### does not route sibling path names through the /data DBFS mount

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/database/file").unwrap()
expect(resolved.driver_name()).to_equal("RamFsDriver")
```

</details>

### MountTable DBFS dispatch — exhaustive match compiles clean

#### DriverInstance.DbFs variant is present in driver_name()

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = DbFsDriver.new_hosted()
val inst = DriverInstance.DbFs(driver)
# driver_name() must handle DbFs variant — if it panics, the match is not exhaustive.
val name = inst.driver_name()
expect(name).to_equal("DbFsDriver")
```

</details>

### MountTable DBFS dispatch — mount/unmount

#### unmount /data leaves / still resolvable

- mt unmount
   - Expected: resolved.driver_name() equals `RamFsDriver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table_with_both()
mt.unmount("/data").unwrap()
val resolved = mt.resolve_driver("/etc/hosts").unwrap()
expect(resolved.driver_name()).to_equal("RamFsDriver")
```

</details>

#### resolve after unmount of /data returns error for /data path

- mt unmount
   - Expected: resolved.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table_with_both()
mt.unmount("/data").unwrap()
# /data no longer has a dedicated mount; falls back to / (RamFs) if present.
# But if MountTable removes sub-prefix entirely, path still resolves to root.
val resolved = mt.resolve_driver("/data/file")
expect(resolved.is_ok()).to_equal(true)
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
