# UP2 freestanding streaming SHA-256 mismatch

Status: open; retry cap reached, no NVMe media write occurred

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

The mandatory three-cycle cap is reached. A fresh scoped session should expose
the observed target digest, compare one-shot and streaming SHA on the same
staging bytes in freestanding mode, and inspect array/value ABI behavior at the
`sha256_process_block` boundary. Do not weaken or bypass the digest gate.
