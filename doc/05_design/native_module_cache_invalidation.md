<!-- codex-design -->
# Native module cache invalidation detail design

## Data model

`NativeModuleCacheWitnessV1` has `schema`, `physical_module_id`, `own_mir_sha256`,
`direct_interfaces`, `resolution_witnesses`, `external_layouts`,
`compiler_sha256`, `compiler_source_sha256`, `target`, `mode`, normalized
`options`, `resolver_generation`, and `provider_receipt_sha256`. Compiler,
target, normalized options, and provider identity are supplied together as the
required versioned `NativeModuleConfigFactV1`; omission invalidates the witness.

`NativeModuleCacheDecisionV1` has module ID, authoritative witness decision,
closure comparison metadata, bounded reason code, witness digest, capsule digest, object digest,
elapsed microseconds, and mismatch flag. Reasons are stable values such as
`hit`, `own-mir`, `dependency-interface`, `resolution`, `layout`, `provider`,
`configuration`, `missing-witness`, `corrupt-witness`, `legacy-schema`, and
`capsule-mismatch`.

## Algorithms

1. Collect semantic facts from the resolved closure; reject duplicate physical
   IDs or ambiguous selected paths.
2. Sort set-valued facts and retain resolver probe order.
3. Encode using length-prefixed fields and hash with SHA-256.
4. Read the stored witness with exact version, field-count, duplicate-field,
   bounds, and digest checks.
5. Re-authenticate witness, capsule receipt, object digest, provider and config.
6. Authorize reuse only on an exact complete-witness match; record the closure
   fingerprint only as comparison metadata.
7. Atomically publish object, capsule, then witness/receipt only after success.

## Mutation contract

| Mutation | Producer | Direct consumer | Unrelated sibling |
|---|---|---|---|
| dependency body only | miss | hit | hit |
| dependency signature/layout | miss | miss | hit |
| higher-precedence resolver candidate | affected | miss | hit |
| provider/compiler/target/options | miss | miss | miss within changed configuration |
| missing/corrupt/legacy witness | miss | miss | unaffected entries independently evaluated |

## Authoritative reuse gate

The stable root only discovers candidates. Reuse additionally requires the
parse-time source snapshot, complete witness, current schema, physical identity,
capsule/object receipt, and object bytes to agree. Missing or mismatching facts
fail closed. Validation requires zero stale acceptance across 1,000 representative
actions, >=99% warm hits, <5% witness overhead, complete mutation coverage, and
bounded receipts. Legacy entries never migrate implicitly.

## Test adapter

The system spec exercises the production witness primitives for dependency,
resolution, layout, and configuration facts. A structural driver assertion also
guards the stable root, exact witness-match admission, and receipt authority so
an isolated witness oracle cannot falsely claim end-to-end authorization.

## Bootstrap integration note — 2026-08-29

Sequential MCP and LSP builds now share the phase-local `tool_builds` cache
directory while keeping distinct output paths. Exact compiler/configuration
witnesses still decide every hit. The old per-tool roots produced LSP
frontend/HIR `0/22` hits despite overlapping source closures.

Entry-closure reduction precedes provider growth. LSP replaced broad
log/I/O/process facades with a narrow owner; focused core-C initialize/link
evidence improved from 45 unresolved symbols to zero and a 126 KiB artifact.
Full MCP instead requires separately validated handler-category artifacts, a
versioned callable ABI, digest-bound metadata, fail-closed loading, and one
immutable package manifest; its current lazy registry is metadata-only.

Retained status is evidence, not admission: Phase1 had 11 terminal rows (two
1,800s timeouts; LSP failed at 1,408s), and Phase2 had 9. The Phase2 MC/DC
standalone-SMF blocker has an honest interpreter fallback (`099b40b5795`) that
records why instrumentation was skipped. A fresh Phase2 matrix must validate
the fix before Phase3 is rebuilt; Phase3 remains pending re-admission.
