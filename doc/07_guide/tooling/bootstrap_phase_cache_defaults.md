# Bootstrap phase cache defaults

`scripts/bootstrap/bootstrap-windows.cmd` delegates to `bootstrap-windows.sh`,
which delegates to `bootstrap-from-scratch.sh`. Linux/macOS/BSD use the same
canonical shell stage engine. The batch wrapper therefore inherits its cache
defaults; it does not select a shared global native cache.

## Phase roles and internal labels

| Phase role | Current internal label | Cache ownership |
|---|---|---|
| Phase 1: Rust seed and runtime archives | Stage 1 | Cargo/seed authority is separate from mutable service builds |
| Phase 2: seed builds the pure-Simple bootstrap compiler | Stage 2 | Platform-specific `stage2-native-cache`; separate CLI/runner/MCP/LSP entry caches |
| Phase 3: self-hosted compiler and requested releasable full-CLI candidate | Stage 3 and its full-CLI/tool matrix | Platform-specific `stage3-native-cache`; producer/input-bound entry caches |
| Additional full-CLI production and verification | Stage 4 | Separate native lane and entry caches; existing release gates still apply |

Phase 3's bootstrap compiler alone is not a releaseable full CLI. The full CLI
and its required verification must succeed; admission or a cache directory is
not release approval. This cache policy does not renumber stages, publish a
release, or waive any bootstrap/resource/verification gate.

## Existing default separation

The canonical Stage 2 and Stage 3 compiler caches already reside under the
output's platform root in distinct directories. Their provenance/ownership
checks remain in force. Stage 4, the UI backend, and later server production
already have distinct native lanes guarded by cache-scope ownership. Phase 2
and Phase 3 tool builds already split full CLI, test runner, MCP, and LSP caches
by phase, exact producer hash, and admitted input identity.

The remaining Stage 1 and Stage 4 verification service defaults now use:

```text
<verification-cache-root>/tool_builds/<stage>/<producer-sha256>/<input-identity>/mcp
<verification-cache-root>/tool_builds/<stage>/<producer-sha256>/<input-identity>/lsp
```

Stage 1's input identity is the admitted seed-stamp SHA-256, binding source,
tool, runtime, and target inputs in addition to executable bytes. Stage 4 uses
its existing admitted tool/runtime input identity. Different OS/target inputs
therefore select different contexts, even if a caller supplies the same cache
root. Full digests are retained in cache paths. The two service entries never
share their writable object directory.

Retries with the same phase, producer, input context, and entry reuse the same
path and retain its contents. No old cache is deleted or migrated by this
change. Existing owner/scheduler checks and one-writer operation still apply;
distinct entry paths do not authorize two simultaneous writers to one lineage.
The immutable host compiler CAS remains separate from these mutable caches.

## Focused checks

`test/01_unit/scripts/bootstrap_phase_cache_defaults_test.shs` executes the
production path helper, distinguishes every identity key, verifies retained
retry payloads, rejects invalid identities/entries, and checks the four argv
sites. It does not build a compiler or establish admission or release readiness.

Cache separation is independent of the observed SCV failure before object
emission. That failure produced no new objects for a linker to consume; this
configuration change does not claim to correct it.
