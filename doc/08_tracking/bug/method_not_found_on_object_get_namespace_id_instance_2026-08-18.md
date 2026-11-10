# `method get_namespace_id not found on type object` — instance of the general object-dispatch defect

Status: SUPERSEDED (2026-11-11, lane ne15) — instance of
`method_field_not_found_on_object_2026-08-18`, which is now FIXED on the fresh
seed; this attribution record stays closed by that fix. See addendum.
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


## Addendum 2026-11-11 (lane ne15) — SUPERSEDED; parent object-dispatch defect is FIXED on the fresh seed

This record was always an attribution shell ("NOT a separate defect") for the
general `method/field not found on type object` mechanism tracked in
`doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md`. That
parent defect is now fixed:

**Verification actually run** (worktree simple-p3-ne15-20261111, tip
f7640d20a458, fresh seed 46fe8f6b6def, seed-smoke) — the parent doc's minimal
repro:

```simple
class C:
    var x: i64
    me now() -> i64:
        self.x
fn main():
    var c = C(x: 3)
    print(c.x)
    print(c.now())
```

```
$ SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe ./bin/simple.exe run \
    build/p3-ne15/fixtures/object_dispatch_probe.spl --mode=interpreter
3
3
```

Field read and method dispatch on an interpreted `class` instance both work
(were: `undefined field 'x' ... type 'object'` / ``method `now` not found on
type `object'``).

**Source confirmation:** the two missing `Value::ClassInstance` arms the parent
doc identified now exist — `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1596`
(method dispatch) and `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:683`
(field access), with comments describing exactly this erase-to-`object`
symptom.

Note: the parent record itself still shows OPEN as of this pass and was not
edited by this lane (not one of its rows); the 84 NVMe `get_namespace_id`
occurrences this file attributes are covered by the same fix. No product
change is attributable to this row.
