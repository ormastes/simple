# UP2 RSP UART frame assembly exhausts the freestanding heap

Status: fixed; four consecutive maximum-size OVMF writes pass

## Reproducer

After a successful raw-image plan and confirmation, two consecutive 1024-byte
GDB `M` packets returned `OK`. The third packet faulted with nil-receiver
addresses resolving inside `up2_rsp_execute` and `up2_gdb_rsp_uart_main`.
No NVMe chunk command had run, so media remained untouched.

The UART reader constructed its roughly 2 KiB ASCII frame by
`frame = frame + char` for every received byte. The UP2 freestanding allocator
is a 16 MiB monotonic heap whose `free` is intentionally a no-op; repeated
quadratic text construction exhausted it during sustained staging.

## Fix

The UART transport now parses `M` packets directly into scalar address, length,
checksum, and byte state, writing only to the admitted staging range and
immediately reading each byte back. It never materializes or slices the roughly
2 KiB packet. Generic low-frequency packets retain the text parser.

OVMF evidence on 2026-08-22 accepted four consecutive 1024-byte nonzero writes
at `0x0a000000`, `+0x400`, `+0x800`, and `+0xc00`, each returning `+$OK#9a`;
an `m` packet independently returned `000102...0f` from staging. The subsequent
storage chunk was rejected before media I/O by the separately tracked
freestanding SHA issue.
