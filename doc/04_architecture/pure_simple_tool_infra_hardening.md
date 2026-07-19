<!-- codex-design -->
# Pure-Simple tool and infrastructure hardening architecture

## Decision

Keep one production owner per tool and put truth gates at boundaries rather
than adding another framework:

1. Bootstrap may construct a candidate, but production admission rejects seed,
   debug, stale, or protocol-incompatible artifacts before deployment.
2. The pure-Simple CLI dispatches directly to the test, lint, format, fix, and
   duplication owners. Wrappers execute admitted compiled artifacts only.
3. Child exits and versioned structured evidence are authoritative on the
   implemented interpreter `--assert-ran` paths. Human text cannot turn their
   failure or zero execution green; other modes remain unqualified.
4. Mutating tools write through the canonical atomic-file facade and propagate
   failure. JSON modes emit JSON Lines only.
5. The bootstrap essential-tools gate runs a bounded test/lint/duplication
   matrix against the exact fresh Stage 4 candidate before deployment.

## Boundaries

| Layer | Owns | Must not own |
|---|---|---|
| Bootstrap/admission | provenance, candidate checks, atomic swap, rollback | production tool behavior |
| CLI | argument validation and direct owner dispatch | raw-source/seed fallback |
| Tool owner | semantics, diagnostics, stable exit status | launcher selection |
| Runtime facade | argv-safe process calls, atomic file replacement | tool policy |
| Verification | structured evidence, time/RSS/cache equivalence | implementation repair |

This is ordinary layered ownership; MDSOC transforms are unnecessary because
the behavior is boundary policy, not runtime feature composition.

## Cache and performance

Incremental native objects are content/config/compiler keyed. Failed mangled
batches do not publish objects compiled against incomplete import context;
dependency-independent `no_mangle` objects may publish atomically for bounded
retry. MCP/LSP wrappers use content-addressed probe stamps and invalidate on
binary hash change. Hot request paths must not rescan the tree or invoke raw
source workers.

## Failure model

Usage is exit 2, assertion/tool failure exit 1, internal failure exit 3, empty
test discovery exit 4, and timeout/resource termination exit 124. Atomic-write,
structured-evidence, provenance, or protocol failure is fail-closed.
