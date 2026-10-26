# Explicit native cache argument did not isolate HIR persistence

Date: 2026-10-12. Status: OPEN; request-level fix prepared for next reviewed attempt. Bug DB reconciliation pending; no qualified DB mutation performed.

Producer: `a6b18fd84c5f88a48afa0beaf61434f39678155fb0f0ed01127db25a28cf5078`. Frozen source: `c78cfd47a59902bbe814c85cbe8e4fe3cc964eaf` plus private MIR JSON three-join candidate. Request SHA256: `132a684a36e0d5d80057d0f158eb025eec118e8741ae87a4b60f53da399ad0d8`. Controller SHA256: `9ca659842b0a2d3ed3fc5f2a8905be1620b8642e41e83ade4b7499c88798f947`. Result SHA256: `d628c8835679a370ba4c8f2bdf45a5082693d3991caa858f9be579bff4725d6d`. Log SHA256: `12c547ae0f815ba8fd2920079b5016b67a4646dbeb9d252a89405eedd1434c84`. Receipt SHA256: `a8f1e5fc1e494b9dca37094e8bea57dcce6b85f4e9cde9e3a0afc584aedca5ab`.

Evidence directory: `build/native_probe/mir-json-perf-review-20261012-astra/native-criterion-attempt1/`. Exact terminal summary is `TERMINAL_REVIEW.json`; raw output and Windows Job closure are `compile/child.log` and `compile/receipt.env`. One compile exited1 in36.619s, peak239148KiB; all children closed and pinned inputs unchanged. Ordinary-zero, ordinary-small and nul-small runtime cases are UNEXECUTED. No parity or performance claim follows from HIR completion.


## Observed scope escape

The compile argv specified a packet-owned `--cache-dir .../native-criterion-attempt1/cache/native`, but the actual HIR summary reported56 stores under `/tmp/simple-cache/v1/projects/7dcf7beb22f33342151bfd60494ef3d85d51da9a92b6318d2576edd1a65e5941/native-build/v1/default/hir`. This establishes that the effective HIR cache selection escaped the requested isolated cache scope. The external directory was not deleted or adopted. The report does not infer physical path resolution or successful persistence beyond the producer's recorded stores.

## Authenticated selection chain

The retained producer's positional bootstrap entry binds the CLI selection through `app.io.native_build_cache`, whose setter only writes SIMPLE_NATIVE_BUILD_CACHE_DIR. The direct route bypasses the ordinary native_build_main worker coordinator that would set SIMPLE_FRONTEND_CACHE_DIR from `--cache-dir`. Neither path makes the HIR owner inherit the object-cache variable.

`driver_hir_cache.hir_cache_dir` first reads SIMPLE_HIR_CACHE_DIR; if absent it selects machine_cache_root()/native-build/v1/(SIMPLE_CACHE_SCOPE or default)/hir. machine_cache_root first honors SIMPLE_CACHE. Without that override, host_cache_base checks SIMPLE_USER_STORAGE_ROOT, SIMPLE_HOST_CACHE_ROOT, XDG_CACHE_HOME and HOME, then falls back to `/tmp/simple-cache`. The reviewed minimal environment supplied none of those roots. Its fixed default project hash explains the exact logged directory. The frontend parse owner independently falls back to relative `build/bootstrap/native_cache/default/frontend` when SIMPLE_FRONTEND_CACHE_DIR is absent. Environment is explicitly passed to the child; shell HOME is not implicitly inherited.

## Next request correction and verification

Before any attempt2 dispatch, explicitly bind packet-owned SIMPLE_NATIVE_BUILD_CACHE_DIR, SIMPLE_FRONTEND_CACHE_DIR, SIMPLE_HIR_CACHE_DIR, SIMPLE_RT_OBJ_CACHE_DIR and SIMPLE_CACHE. Retain persistence and SIMPLE_NO_STUB_FALLBACK=1. Controller preflight must validate containment and effective values before compile/runtime dispatch; inspect the actual HIR summary afterward. Do not fabricate cache identity receipts or assume copied records are compatible.

The source owner and canonical source-root paths change in attempt2. Existing HIR headers include source/closure/environment/compiler identities, so cache reuse must be checked against those identities; no reuse count is established. Preserve attempt1 and its accidental external HIR evidence. Adopt only idle, demonstrably compatible records; never clear shared or live cache roots. This request correction is separate from any future general CLI cache-policy change.
