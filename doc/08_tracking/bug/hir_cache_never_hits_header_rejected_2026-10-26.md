# HIR cache never hits: every lookup rejected with header:1 (2026-10-26)

**Date:** 2026-10-26
**Status:** open
**Evidence:** `C:/dev/hircfg-probe/logs/`, `C:/dev/hircfg-probe/summary.txt`
**Compiler:** `build/s2hw/stage2.exe`, run as `native-build --source src --entry src/hello.spl --target <triple> --cache-dir C:/dev/hircfg-probe/cache --emit-object`
**Severity:** P2
**Owner:** cache lane (agent aac789c06e9d9279b), accepted

## Symptom

Repeating a build of the same target never hits the HIR cache, and the parse
cache also shows zero hits. Warm/repeat logs (`x86_64-pc-windows-msvc.warm.log`,
`aarch64-unknown-simpleos.rep1.log`, `.rep2.log`) all show:

```
[frontend-cache] hits=0 misses=1 parses=1 native_digest_unavailable=0
[hir-cache] hits=0 misses=1 stores=1 refused=0 io_failed=0 reason=- dir=C:/dev/hircfg-probe/hircache rejected=absent:0,header:1,checksum:0,framing:0,decode:0,rebase:0 selfcheck=off selfchecked=0 selfcheck_failed=0
```

The first (cold) lookup reports `rejected=absent:1,header:0`. The repeated
lookup finds the stored entry but rejects it at the header stage
(`rejected=header:1`), then re-lowers (`[hir-cache] adopted=0 lowered=1`) and
stores again.

## Second symptom: one file for all targets

Across all 10 probed targets only one file is ever written:
`C:/dev/hircfg-probe/hircache/0954f323b04fae4cc24968582d26318291f13b1f3f6004c4a7a00d88fe73b18d.parser-v4.hir`.
Every target overwrites it, so the key is target-neutral while the header check
is not (or the header embeds target/run-specific data).

## Impact

Blocks target-neutral HIR sharing across targets
(`doc/03_plan/compiler/hir_target_neutral_mir_target_plan.md`): no hit is
possible even for an identical repeated build.

## Suspected area

`src/compiler/80.driver/driver_hir_cache.spl`, `src/compiler/20.hir/hir_codec_support.spl`
(header validation). Needs a header-field diff of the stored vs expected header.
