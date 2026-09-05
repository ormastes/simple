# UP2 freestanding streaming SHA-256 mismatch

Status: fixed and verified under OVMF

## Reproducer

Under a fresh OVMF boot, admit a 4096-byte image session, then use four
checksummed 1024-byte GDB RSP `M` packets to stage `00..ff` repeated sixteen
times. Every packet passes immediate target readback, and an independent `m`
packet returns the expected first bytes `000102...0f`.

`nvme image chunk 0 0 4096
c8f5d0341d54d951a71b136e6e2afcb14d11ed8489a7ae126a8fee0df6ecf193`
is rejected as `storage-image-chunk-digest-mismatch:session-aborted`. A
512-byte prefix also mismatches its independently computed digest. The failure
therefore precedes `BlockDevice.write_sector`; `media_writes` remains zero.

## Attempts and next investigation

1. Removed quadratic UART text concatenation.
2. Replaced `M` frame materialization with a scalar, allocation-free parser.
3. Changed `Sha256Stream` from a returned value struct to a mutable class.

The next scoped session exposed streaming digest `8a0e5bf3...7409` and one-shot
digest `c8f5d034...f193` for the same target array. The one-shot result matched
the host, isolating the failure to the streaming block path: it repeatedly
passed a large byte array with nonzero offsets through the freestanding ABI and
returned newly allocated state/schedule arrays.

The fix preallocates one 64-byte block and one 64-word schedule in
`Sha256Stream`, fills them in place, and mutates the eight state words without
per-block allocations or nonzero-offset large-array calls. This is constant
memory for a full disk image.

`--ovmf-image-provision` now proves four nonzero 1024-byte RSP writes, exact
chunk SHA, NVMe write, Flush, fresh-adapter full-range SHA, independent host
SHA, and unchanged 512-byte ranges immediately before and after the write.
