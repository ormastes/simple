# SCV CURRENT readback rejects a valid combined cursor record

## Cause and correction

The compiler helper `str_index_of` declared `rt_string_index_of` as returning
an `i64`. The Rust runtime exports that name with an `Option<i64>` runtime
value result. A boxed result used as a slice endpoint retains the entire
combined CURRENT record, whose 617 bytes then fail the 64-byte digest validator.
The post-publication caller reports `inventory-publication-raced` even when
the pointer and immutable generation are consistent on disk.

Route the helper through the existing `rt_string_find` API, which returns a
raw UTF8 byte offset or -1 in both Rust and core-C providers. Keep the Rust
Option export and normal compact slice syntax unchanged.

## Retained component evidence

Source snapshot: `5da86869df060ad4c1b87abfd2384f8d2a761e3a`.
Linux startup rejected before frontend work after 287.16 seconds. The retained
generation contains 17,018 entries and 6,399,256 bytes. Its SHA256 and CURRENT
first line both equal
`34eb407387e2a73ede4b4f43ef41e126689ead2142a5f2e030393e8e02aaa349`.

Three bounded native component cycles used the actual 1,058 cached objects,
Rust nativeall/backfill providers, and an init sequence reconstructed from
the parent disassembly. The original linker response and entry shims were
not retained. All input hashes were unchanged before and after each cycle.

| Cycle | Native observation | Link/run seconds | Run peak RSS KiB |
| --- | --- | --- | --- |
| 1 | `read_current`: false tag 19, `inventory-pointer-invalid`; retained generation decoder: true tag 11, `ok`, exact SHA | 66.69/6.69 | 186,980 |
| 2 | File reads and optional unwrap preserve 617 bytes; raw index result 290361617 is a boxed value; fresh 64-byte digest and selected-generation read pass | 63.02/7.09 | 243,228 |
| 3 | Private types object changes exactly one relocation from `rt_string_index_of` to `rt_string_find`; actual `read_current` returns true tag 11, `ok`, exact SHA | 90.89/7.19 | 242,728 |

The cycle 3 private object preserves every allocated section's bytes, including
code. Original types object SHA256:
`6b6cb0e99d5933f18899f0dd30efa3d9e446e052dbd5885b9d14069dda6f2fa6`.
Private object SHA256:
`b36c7e5ab41e133129fc2c55bbe2cbbcd1cb28848736d29de67cc291ded08d7e`.
Nativeall SHA256:
`6df633e8a22e2e08c21c5079b207809df236b6f19608d100deac7b28c228c295`.
Backfill SHA256:
`b42d571ff7a88932dd87f4c81d25a1b901ed54ab5ad0e9132092840cb491bf25`.

Artifacts are retained under
`D:/dev/simple-wsl-recovery-20260928/scv-readback-native-probe-20260929`,
including exact argv, before/after hashes, object ABI mapping, relocation
comparison, metrics, and native outputs. Cycles 2 and 3 have separate directories.

## Qualification limits

This is experimental component proof using a private symbol substitution,
not verification of a newly compiled compiler or a full bootstrap. The new
SSpec covers found/missing/empty text, UTF8 byte offsets, and CURRENT slicing;
its execution awaits a trusted rebuilt producer. Windows has matching
persisted pointer/generation evidence, but this native isolation ran on Linux.
The separate diagnostic change adds readback failure provenance; it does not
repair this boundary.
