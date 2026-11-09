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

## Fix 2026-11-07 (nondeterministic identity + header diagnostic)
Nondeterministic field found: when the compiler executable cannot be hashed
(`native_build_compiler_executable_hash` returns "", e.g. argv0/SIMPLE_BINARY
not resolvable), `native_build_frontend_identity_from` returns
`uncacheable-<pid>-<micros>`. That token rides the frontend scope into the
HIR header while the entry KEY stays stable, so every run overwrote the same
file and the next lookup rejected it as `header` (both symptoms above).
- `hir_cache_identity_scope_v1` (driver_cache_scope_policy_v1.spl) now returns
  "" for an `uncacheable-` scope, which disables the HIR cache
  (`hir_cache_enabled`) instead of storing entries that can never hit.
- `hir_cache_load_in_owned_scope` prints the first header rejection per process:
  `[hir-cache] header rejected path=<p> field=<n> stored=<s> expected=<e>`
  (`hir_cache_header_diff_v1`).
- Spec: `test/01_unit/compiler/driver/hir_cache_header_determinism_spec.spl`
  4/4 (identity built twice in one process is equal; uncacheable scope
  disables; diff names the field). `driver_cache_scope_publication_spec` 8/8.
Still open: why stage2.exe's executable hash was empty on the Windows probe
(rerun the probe; the new line names the field). Status stays open until then.

## Correction 2026-11-07 (PR follow-up)
The "disable the cache for an `uncacheable-` scope" half of the 2026-11-07 fix
is reverted. The orchestrator publishes the scope once and every shard child
inherits it, so an uncacheable token is still shared by one build; across runs it
already fails closed as a `header` miss. The header-reject diagnostic stays.
The remaining defect is the empty executable hash on the Windows probe.

## Empty executable hash on Windows (2026-11-09)
`_native_build_compiler_executable_hash_uncached` only tried SIMPLE_BINARY and
argv[0] verbatim. A bare-name Windows launch (`stage2`) gives argv[0] /
SIMPLE_BINARY without `.exe`, so `rt_file_exists` failed and the hash was ""
-> `uncacheable-<pid>-<micros>` scope -> `header` reject every repeat build.
Fix (incremental.spl): candidates = SIMPLE_BINARY, SIMPLE_BINARY.exe, argv0,
argv0.exe (`native_build_compiler_exe_candidates_v1`); when none hashes, print
`[native-build] compiler executable hash unavailable (SIMPLE_BINARY=.. argv0=..)`
once instead of failing silently. Spec
`test/01_unit/compiler/80.driver/compiler_exe_hash_candidates_spec.spl` 3/3.
Pending: stage3 repeat-build run showing hits>0.
