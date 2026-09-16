# Phase-2 sweep triage — remaining real failures (2026-08-21)

Triage of the parallel `test/01_unit` + `test/02_integration` sweep. Scope
excludes `compiler/mir/**`, `compiler/mir_opt/**` and the
`lib/nogc_async_mut` facade/sanitizer group (assigned elsewhere).

## Load-induced flakes — NOT defects

Five specs reported failures under the 16-way sweep and pass byte-identically
when re-run standalone. They must not be treated as regressions:

| spec | under sweep | standalone |
|---|---|---|
| `lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.spl` | 41 total, 0 passed, 41 failed | 41 total, 41 passed, 0 failed |
| `lib/nogc_sync_mut/engine/render/gpu_lighting3d_spec.spl` | 18 total, 11 passed, 7 failed | 18 total, 18 passed, 0 failed |
| `lib/nogc_sync_mut/engine/render/gpu_mesh3d_spec.spl` | 12 total, 3 passed, 9 failed | 12 total, 12 passed, 0 failed |
| `lib/nogc_sync_mut/engine/render/texture3d_spec.spl` | 18 total, 7 passed, 11 failed | 18 total, 18 passed, 0 failed |
| `lib/nogc_sync_mut/src/collections/hashset_known_new_parity_spec.spl` | 4 total, 0 passed, 4 failed | 4 total, 4 passed, 0 failed |
| `lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl` | 6 total, 4 passed, 2 failed | 6 total, 6 passed, 0 failed |
| `lib/nogc_sync_mut/spec_bool_expect_spec.spl` | 3 total, 2 passed, 1 failed (`function expect_not not found`) | 3 total, 3 passed, 0 failed |
| `lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.spl` | 3 total, 0 passed, 3 failed | 3 total, 3 passed, 0 failed |

The `expect_not` row is worth calling out: `expect_not` **is** defined and
`pub` at `src/lib/nogc_sync_mut/spec.spl:710`. The "not found" verdict is a
concurrency artefact, not the glob-import gap the spec's own header comment
blames.

## Remaining real failures, by root cause

### 1. Unimplemented feature — `normalize_type_segments` does not exist
`test/01_unit/compiler/module_resolver/type_domain_resolver_spec.spl`
(`4 total, 0 passed, 4 failed`). `/usr/bin/grep -rn normalize_type_segments src/compiler/`
returns **zero** hits: the type-domain import normalization the spec describes
was never implemented. A separate, real drift in the same spec (static
constructors desugared away) was fixed — see the triage report — which moves the
error from `unknown static method new on class ModuleResolver` to
`function normalize_type_segments not found`, i.e. from spec rot to the genuine
missing feature. Left red on purpose.

### 2. Unbacked extern — `rt_cpu_is_x86_64`
`test/01_unit/compiler/native/simd_capabilities_spec.spl`
(`14 total, 2 passed, 12 failed`), every failure
`semantic: unknown extern function: rt_cpu_is_x86_64`. Same class as
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`. Needs a
runtime symbol in the seed plus a redeploy.

### 3. Missing dict method — `Map.for_each`
Filed separately: `doc/08_tracking/bug/map_for_each_missing_on_dict_2026-08-21.md`.

### 4. Intentional RED (TDD), not a regression
`test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl`
(`4 total, 0 passed, 4 failed`), failure text
`RED: generation-safe JS VM reclamation is not implemented`.

### 5. Behavioural defects still open (not yet root-caused)
- `lib/nogc_sync_immut/native_combinators_spec.spl` — `1 total, 0 passed, 1 failed`,
  `expected <lambda> to equal [7, 8]`: a combinator returns the unapplied lambda
  instead of its result.
- `lib/nogc_sync_mut/http/auth/digest_spec.spl` — `14 total, 9 passed, 5 failed`,
  RFC 7616 §3.9.1 SHA-256 and MD5 response hexes do not match.
- `lib/nogc_sync_mut/engine/render/shader_compile_spec.spl` — `17 total, 12 passed, 5 failed`,
  WGSL emission (`@vertex` marker, no GLSL `void main()`) and spirv-cache reuse.
- `lib/common/web/browser_session_http_status_spec.spl` — `12 total, 10 passed, 2 failed`
  (307 POST body/content-type preservation; final-URL resolution for redirected
  relative imports).
- `lib/common/web/browser_session_loading_history_spec.spl` — `2 total, 1 passed, 1 failed`
  (`expected 24 to equal 25`, history retention bound off by one).
- `app/browser/browser_render_lane_spec.spl` — `11 total, 10 passed, 1 failed`
  (inline `style=` attribute ignored by the test lane).
- `compiler/module_resolver/group_import_self_named_module_spec.spl` — `2 total, 1 passed, 1 failed`;
  `compiler/module_resolver/group_import_shadowing_generalization_spec.spl` — `3 total, 2 passed, 1 failed`.
  Both are the self-named-module class binding tracked by
  `doc/08_tracking/bug/group_import_self_named_module_binds_module_dict_2026-08-17.md`.

## Method note

`rc` alone was never trusted; every verdict above is the spec run's own
`Results:` / `SPEC FILE VERDICT` line. Re-runs were capped at 8 concurrent
`bin/simple` processes.
