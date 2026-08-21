# UP2 freestanding `u64` capacity guard miscompiled

Status: fixed, board-image regression verification pending

## Reproducer

The admitted Stage-3 compiler built the UP2 freestanding closure successfully,
but `nvme identify` rejected QEMU's valid 64 MiB namespace:

```text
lba_size=512 lba_count=131072
nvme identify blocked reason=up2-nvme-capacity-overflow
```

The rejected expression compared the count with
`0xffffffffffffffffu64 / lba_size`. This native target did not preserve the
intended unsigned quotient.

## Fix

Capacity owners now multiply and verify the inverse relation:
`capacity = count * size`; for nonzero count, `capacity / count` must equal
`size`. The check is applied in the UP2 identity paths and the shared block
image planner. This retains overflow rejection without maximum-literal
division. Unit coverage retains valid bounded geometry; the current board image
and OVMF command must pass before this record is closed.
