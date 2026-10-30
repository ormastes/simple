# Module resolver cache drops directory import metadata

- Date: 2026-09-21
- Severity: P1
- Status: fix-implemented-verification-pending
- Owner: `src/compiler/99.loader/module_resolver/resolution.spl`
- Discovered during macOS P0/P1 loader/import ledger audit.

## Defect and impact

`resolve_from_base` returns a directory module for `pkg/__init__.spl`, but
`resolve` cached only its path. Every cache hit rebuilt `ResolvedModule.file`,
changing `is_directory` from true to false. Directory-specific export and
manifest handling can therefore differ between the first and repeated import.
The defect is platform independent and affects macOS as well.

## Implemented correction

Store `ResolvedModule?` in `resolution_cache`; preserve the complete successful
result in all seven search routes and return it on a hit. A nil entry continues
to cache a missing module. Existing invalidation still clears the entire map.
Do not infer module kind from a filename: an explicit `crate.pkg.__init__`
import resolves as a file even though it has the same path as the package.
The cache retains metadata alongside each path; it adds no filesystem probes.

## Focused regression and evidence

`test/01_unit/compiler/module_resolver/cached_directory_resolution_spec.spl`
checks directory imports, ordinary files, explicit `__init__` file imports,
and cached failures. The existing tier warning source assertion now recognizes
the complete-result cache write.

Execution was attempted with the installed
`bin/release/aarch64-apple-darwin/simple`, using a temporary source overlay.
The test runner failed before executing the spec while parsing the existing
`src/lib/nogc_sync_mut/io/process_ops.spl` dependency: expected expression,
found Colon. A standalone probe subsequently identified this installed release
path as a Rust bootstrap seed, so it is not admissible self-hosted verification.
No PASS is claimed. No bootstrap or seed modification was performed.

Evidence logs from this host:
- `/tmp/simple-loader-cache-todo3-20260921-test.log`
- `/tmp/simple-loader-cache-todo3-20260921-probe.log`

## Existing ledger triage

The open P1 tierless-import ambiguity record has already received fixed tier
precedence and a root-directory collision warning in source. Its remaining
broader resolution policy is not closed by this cache correction. The macOS
seed PROT_EXEC refusal likewise remains outside this pure-Simple change.

## Admitted self-hosted follow-up

The separate admitted Stage 2 binary at
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple` has SHA256
`e1c0f79a7f0bc9b42df99b1219293e9c3852742a24843e07f96e81d5dcbcd81a`, matching
both adjacent provenance and sanity receipts. Its admission receipt SHA256
also matches `3fb0e91da5ded08eaabdae050a70fc930bea35e7f4a2d8dc31546fcd756f00e8`.
This bootstrap CLI has no `test` or direct-run command. A dependency-free
native probe of the cache-hit branch was attempted, but stopped in source
loading with `scv-authority-missing`; it requires explicit package-index cold
initialization. No runtime PASS is claimed. The live bootstrap owner's cache
and concurrent build were left undisturbed.

- Admitted CLI evidence: `/tmp/simple-loader-cache-todo3-20260921-admitted.log`
- Native probe evidence: `/tmp/simple-loader-cache-todo3-20260921-native.log`
- Static review confirms all seven successful search routes cache the complete
  resolved value and miss/invalidation paths retain their prior behavior.
- `direct-env-runtime-guard.shs --working`: PASS.
