# Release cache preservation port

Base: `832b06d2e90780ed9c20ee91dfd63e962636a084`.
Main source: cache PR #2097 (`6a1e6382bcb`), source refresh
`06dae5a8a0490e9ab8c54096248699f03ee0cc2e`, sealed archive
`d6f242be6febbe17f90f92f6d34ecab4d9573990`.

The release wrapper uses its existing inline producer and resume commands.
The native environment identity owner is identical to main `6a58e328`; the
release driver rejects an unavailable snapshot before selecting object scope.
The strict lineage/archive helper is identical to `d6f242be6fe`.

Source refresh admits only the reviewed release Rust owner
`51febe82933b423cdcb113e1b36e9d2bdfe73b2f166076af718629c7dc2bc2db`.
Review found the object/global dependency-key region byte-identical to main:
region SHA-256 `fe24925a7ed535555a621e1c6c5e700c81c781071c0a97af17d6932cb73f5d2a`.
This is source review, not evidence of executing a release Rust producer.

## Focused checks executed

| Check | Environment | Result |
|---|---|---|
| `bootstrap_release_cache_vector_test.shs` | Windows Git sh | PASS: real inline Stage 2 hash/run/replay, Linux/MSVC argument vectors, verbose/spaces, old absent cache vector, malformed pairs, option presence |
| `bootstrap_cache_policy_test.shs` | Windows Git sh | PASS: existing regression updated to require retained incremental one-binary cache and explicit clean behavior |
| `bootstrap_cache_hir_controls_test.shs` | Windows Git sh | PASS: real release inline Stage 3 and resume hash/run agreement, persistent per-phase HIR, semantic environment |
| `bootstrap_release_attempt_archive_test.shs` | WSL Ubuntu shell | PASS: actual wrapper loop preserves sealed authorities and mutable HOME/TMP separately; verifies frozen receipt and unchanged cached object |
| `bootstrap_cache_source_refresh_test.shs` | WSL Ubuntu shell | PASS: actual release context reconstruction, explicit immutable transition, refused runtime/tools/producer/options/root changes and active writers; missing snapshot and malformed environment preserve binding/object |

Each passing criterion ran once. Unchanged main helper tests were retained
without repeating their prior green runs. All checks above are shell boundary
or storage checks; no compiler was executed by them.

## Outstanding qualification

`release_native_environment_identity_spec.spl` has four compiler cases queued
for the Phase 2 full CLI/runner. Full release compiler/core/library checks and
MCP smoke gates remain pending. Native environment identity conservatively
includes present diagnostic `SIMPLE_*` fields, so retained objects alone do not
prove cross-attempt cache hits. No release admission or complete verify PASS is
claimed by this report.
