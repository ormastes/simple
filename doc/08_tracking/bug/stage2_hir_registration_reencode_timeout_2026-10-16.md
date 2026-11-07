# Stage 2 HIR registration re-encode timeout (2026-10-16)

## Status

Open. One redundant complete-body encode is removed; the remaining full-body
validation encode and cache publication copies still need measured reduction.

## Reproduction

The admitted Stage 2 compiler `1481e8cdd59624ceeff5c274d2a74155432d761d672a6faa9dce49ce46c2348c`
ran the canonical slim phase-verification matrix with one build thread and a
3,600 second tool timeout.

- `compiler_cli_build`: `TIMEOUT`, status 124, 3,601 seconds, peak RSS
  4,486,712 KiB, 81/2,680 HIR modules complete.
- `test_runner_build`: campaign terminated at 118/265 HIR modules after the
  CLI timeout consumed the first half of the 7,200 second campaign bound.
- Neither producer repeated the prior projection-encoder SIGSEGV.

Evidence is retained under:

`build/bootstrap-combined-20261016/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/`

## Finding

Fresh HIR publication already calls `hir_module_encode(module)` to create and
hash `HirBodyArchiveV1`. Registration then encoded the same complete module
again only to derive the cohort of a body-free symbol projection:

`sha256(archive_key + "\n" + hir_module_encode(module))`.

The archive descriptor already seals the exact body digest, and its archive key
binds input identity, body digest, and warning digest. Replacing the second body
encode with `sha256(archive_key + "\n" + body_digest)` retains a collision-safe,
body-specific cohort without serializing executable HIR again.

## Remaining work

Profile the other repeated complete-body encodes in transaction cache storage,
body-archive storage, and registration validation. Introduce a single owned
encoded-body receipt if measurements show those copies dominate. The next full
bootstrap must demonstrate both tool producers inside their 3,600 second bounds
before Stage 3 resume or local deployment.

## 2026-11-07 — encode-once receipt (fix-implemented-verification-pending)

Branch `work/p2-hir-encode-once-20261107`. `HirEncodedBodyV1`
(`driver_hir_cache.spl`) carries one complete-body encode, keyed by module
name + path + the digest of its own bytes, as scratch of the caller's owned
scope. The shard transaction builds it once and passes it to both
`hir_cache_store_in_owned_scope` and `hir_body_archive_store_in_owned_scope_v1`;
`mir_hir_project_module_in_owned_scope_v1` accepts the caller's bytes and
rechecks their digest without re-encoding (shard export, archive-borrowed
reader). A receipt for another module, or whose bytes no longer match its
digest, is invalidated and re-encoded.

Measured with `hir_module_encode_calls()` on seed `4efe643ae90e1a85…`
(17,847,296 B, 2026-11-06 15:11): per registered module 3 -> 1; archive
publication 2 -> 1; projection with caller bytes 1 -> 0. Unchanged on purpose:
the sampled store self-check (decode + re-encode, every 8th bootstrap store)
and the lease-load `sha256(encode(decoded)) == body_digest` recheck.

Specs: `test/01_unit/compiler/driver/hir_registration_encode_count_spec.spl`
(repro, RED 2 -> GREEN 1), `test/01_unit/compiler/driver/hir_encode_once_prevention_spec.spl`.

Verification pending (Windows host, admitted Stage 2 + phase-verification matrix):

```bash
. scripts/setup/windows-gitbash-bootstrap-env.shs
SIMPLE_COMPILER_PHASE_PROFILE=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
```

Pass bar: `compiler_cli_build` and `test_runner_build` both complete inside
their 3,600 s bounds.
