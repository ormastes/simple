# DMA, File, and Display Driver Performance Report — 2026-04-21

## Scope

This report covers the shared acceleration proof path added for the DMA,
direct-I/O, and display-driver work.

## Measurement Surface

- Source: `src/os/drivers/perf_report.spl`
- Spec: `test/sys/simpleos_driver_acceleration_perf_spec.spl`
- Storage fixture: 4096-byte aligned payload
- Display fixture: 1024x768 BGRA framebuffer, 64x32 dirty rectangle
- Isolation label: `trusted-driver/no-iommu` for current no-IOMMU QEMU lanes

## Results

| Path | Backend | Measured Field | Value |
|------|---------|----------------|-------|
| File/block buffered I/O | buffered-copy | CPU copy bytes | 4096 |
| File/block direct I/O | direct DMA, aligned | CPU copy bytes | 0 |
| Display full frame | framebuffer-mmio / fallback | bytes flushed | 3145728 |
| Display dirty rectangle | framebuffer-mmio / virtio-gpu-dma | bytes flushed | 8192 |
| Network descriptor compatibility | shared DMA descriptor | compatible | true |
| RSS field | report contract | max_rss_kib | recorded by lane |

## Notes

The report path is deterministic arithmetic so it can run in hosted CI without
requiring QEMU hardware. Hardware smoke lanes should populate latency,
throughput, and RSS with runtime measurements while preserving the same backend
and isolation labels.
