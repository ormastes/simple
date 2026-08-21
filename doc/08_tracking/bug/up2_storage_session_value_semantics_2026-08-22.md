# UP2 storage session aggregate loses native field values

Status: fix implemented, bounded OVMF regression pending

## Reproducer

The current freestanding image accepted an aligned 4 KiB plan on a valid
64 MiB QEMU NVMe namespace and printed the correct compact challenge. Confirming
that exact challenge then returned `storage-write-range`, even though admission
had already passed identity equality, busy-state, and equal-size checks.

This isolates the failure to long-lived aggregate fields after a struct was
stored in and unwrapped from module-global optional state. The same run printed
shifted PCI fields from `Up2NvmeLiveDevice`, another aggregate containing a
large reference-valued driver.

The diagnostic build proved the exact corruption: capacity and start remained
`67108864` and `1048576`, while the stored plan length changed from `4096` to
`134801553` before constructing the admission request.

## Fix

The board leaf now retains only module-owned scalar/text fields for its pending
plan, expected identity, active state, and next offset. The common image owner
is stateless per chunk and receives a transient value-semantic plan; completion
flushes and hashes the exact range from a fresh adapter. Exact PCI fields are
also copied into dedicated scalars at enumeration instead of rereading them
through the driver-bearing device aggregate. The next bounded board build/OVMF
run must prove identity and plan/confirm/chunk/finish before closing this bug.
