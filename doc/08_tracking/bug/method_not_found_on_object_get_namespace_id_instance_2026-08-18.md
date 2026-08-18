# `method get_namespace_id not found on type object` — instance of the general object-dispatch defect

Status: OPEN (mechanism), NOT a separate defect
Date: 2026-08-18

## Symptom

Sharded suite run, 84 occurrences:

```
semantic: method `get_namespace_id` not found on type `object` (receiver value: NvmeDriver(admin_queue: NvmeQueuePair(...)))
```

Seen in `shard_02_integration.log` and `u_os.log`.

## Why this is NOT a missing/renamed method

- The method exists and is public:
  `src/os/drivers/nvme/_NvmeDriver/driver_operations.spl:1687` — `fn get_namespace_id() -> u32:`
- Every caller uses a receiver with an explicit declared class type, e.g.
  `src/os/services/vfs/vfs_boot_init.spl:78` — `var g_nvme: NvmeDriver = NvmeDriver.new()`,
  called at lines 1865 and 1903.
- The error message itself prints the receiver as a fully-formed `NvmeDriver(...)`
  value. The VALUE is correct; only the STATIC type has been erased to `object`,
  so method resolution fails.

## Why it is an instance, not its own bug

The same log set carries the identical `not found on type \`object\`` shape for many
unrelated method names, with `get_namespace_id` only the second most frequent:

| count | method |
|---|---|
| 158 | `init` |
| 84 | `get_namespace_id` |
| 31 | `now_micros` |
| 27 | `with_sector` |
| 24 | `sector_size` |
| 20 | `_persist` |
| 20 | `open` |
| 18 | `push` / `forward` / `add_bug` |

A rename or export gap cannot produce that distribution. The defect is the
receiver's static type collapsing to `object` in the semantic phase; fixing
`get_namespace_id` in isolation would be a no-op.

## Action

No product change made here. Mechanism work belongs to the general
`method/field not found on type object` investigation; this file exists so the
84 NVMe occurrences are attributed rather than re-root-caused.
