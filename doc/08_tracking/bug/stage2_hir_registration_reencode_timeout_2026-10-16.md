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
