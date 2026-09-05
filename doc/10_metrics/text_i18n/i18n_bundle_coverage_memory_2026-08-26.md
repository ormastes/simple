# i18n bundle coverage and memory evidence — 2026-08-26

The new production-owner suite passes 13/13 examples. Its third/final bounded
coverage cycle measured `src/lib/nogc_sync_mut/i18n/bundle.spl` at 52% lines
(50/95) and 92% branches (13/14).

The repository contains a byte-identical shadow at
`src/std/nogc_sync_mut/i18n/bundle.spl`. Instrumenting both paths produced 0/95
lines and 0/0 decisions for the shadow while the `src/lib` owner received all
hits. Coverage aggregation must canonicalize this module identity before an
all-owner percentage is meaningful.

The memory lane passes 2/2:

- 4,096 lookups over five entries and 120 catalog UTF-8 bytes;
- 512 two-argument Arabic formatting operations and 24,576 output bytes.

Runtime allocation/live/capacity counters and process HWM are unavailable, so
no zero-allocation or RSS claim is made. The repeated-`replace` formatter still
requires replacement by one-pass MessageIR plus matched memory measurement.
