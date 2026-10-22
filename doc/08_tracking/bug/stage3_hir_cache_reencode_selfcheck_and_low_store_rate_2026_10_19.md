# Stage 3 HIR cache: reencode SELFCHECK failures and almost no stores

- Status: OPEN
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu
- Affects: Stage 3 resume from an admitted Stage 2 (r8, sha256
  `552150e7...15d8`); defeats "restart from the failed module via cache hits".

## Observation

During the 44 GiB-capped Stage 3 run (HIR 771/1315 reached) the log carried

```text
[hir-cache] SELFCHECK FAILED module=src/compiler/00.common/driver_core_types.spl
  path=src/compiler/00.common/driver_core_types.spl reason=reencode
  line=34858 field=1 expected=10 got=0; entry not stored
```

5 such lines by module 490. The Stage 2 matrix full-CLI builds (r1-r8) show
none of these; they refuse stores with `cache store refused (codec, not I/O)`
instead, so the reencode selfcheck is reached only on the Stage 3 lane.

After 771 lowered modules the Stage 3 HIR cache
(`stage3/<triple>/stage3-native-cache/hir/`) held only 25 `*.parser-v4.hir`
entries (6.1 MB); the frontend cache held 106 MB of `.fpc`. The next resume
with a changed compiler-ceiling env reported `cached=0` for both parse
(1315/1315) and HIR (231 modules) -- the ceiling env is part of the Stage 3
args digest, so the producer identity changed.

## Not yet established

Why `field=1` re-encodes as 0 (expected 10), and whether the silent non-store
of the other ~745 modules is the same refusal without a log line.
