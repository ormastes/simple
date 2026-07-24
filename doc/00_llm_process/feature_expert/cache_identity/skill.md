# Feature Expert: Cache Identity (Option-C global cache)

## What this is
The identity/digest layer for the global content-addressed cache: SHA-256
ActionKey canonical encoder, hybrid file-stamp index (C fast path / A strict
mode), and disk CAS primitives. Phase 1 = compute-and-log only; NOT wired into
any load path yet.

## Source of truth
- Audit: `doc/01_research/compiler/cache/global_content_addressed_cache_audit_2026-07-24.md`
- Plan: `doc/03_plan/compiler/cache/global_cas_interpreter_cache_option_c_plan_2026-07-24.md`
- **Formal model (normative):** `src/verification/cache_identity/src/CacheIdentity/Model.lean`
  — the `.spl` encoder mirrors it field-for-field; divergence is a defect.
  Theorems: injectivity core (`encode_eq_iff_canon`), field-completeness,
  `no_false_hit`, `stamp_fast_eq_strict` (C≡A bridge). Gate:
  `scripts/check/check-cache-identity-formal-proofs.shs`.

## Code map
| File | Role |
|---|---|
| `src/compiler/80.driver/cache/action_key.spl` | ActionKey (15 fields), canonical length-prefixed encoder, `action_key_digest`, `interface_digest_of`, `resolution_witness_digest` (probes ORDERED — order is semantic) |
| `src/compiler/80.driver/cache/file_stamp.spl` | FileStamp/StampIndex; `file_sha_via_stamp(strict)` = C fast path vs A rehash+divergence recording; torn-read guard (stat→hash→stat, retry once) |
| `src/compiler/80.driver/cache/cas_store.spl` | Disk CAS `<root>/cas/sha256/ab/…`; verify-before-serve, quarantine on mismatch; action manifests refuse mislabeled keys; VERSION schema stamp |
| `src/compiler/80.driver/cache/compile_options_hash.spl` | Combined hash = sha256-prefix i64 over canonical sorted length-prefixed encoding (was rt_hash_text); zero-hash never accepted (`smf_cache.validated_smf_load`) — mismatch = plain miss → rebuild |
| `src/compiler/10.frontend/core/interpreter/load_session_cache.spl` | `lsc_invalidate_module` now also evicts target (`module|` prefix) + freshness entries |

Specs: `test/01_unit/compiler/cache/{action_key,file_stamp,cas_store,compile_options_hash}_spec.spl`,
`test/01_unit/compiler/interpreter/load_session_cache_spec.spl`.

## Landmines
- Text `<` on native backend lowers to pointer compare — encoder uses explicit
  byte-wise compare (`action_key_text_lt`); keep it that way.
- `[text].sort()` is a seed no-op — explicit sorts only.
- Changing ANY encoding detail changes every digest: the golden-digest test in
  `action_key_spec.spl` will fail — that is the point; never "fix" it by
  updating the golden without bumping the domain string version.
- mtime granularity is whole seconds (`rt_file_stat`): same-size same-second
  rewrite is the stamp ceiling; strict mode (A) exists to catch it.

## Next phases (plan §2.2)
2: process-global immutable cache behind flag + shadow strict compare;
3: wire CAS write-through; 4: ArtifactId resolver; 5: SMF manifests;
6: interpreter realization from cached plan; 7: retire path-keyed caches.
