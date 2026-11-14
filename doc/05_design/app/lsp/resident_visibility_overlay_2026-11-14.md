# Resident document-symbol visibility over live sources

This checkpoint repairs the raw LSP `textDocument/documentSymbol` source path.
It reuses the existing query classifier and does not claim the selected new
folder-local/explicit-private visibility semantics. MCP, hover, completion,
workspace symbols, and semantic-token adoption remain separate work.

## Composition and request contract

`app/lsp/main.spl` installs the app-owned visibility provider before starting
the protocol loop. The protocol library owns document snapshots and source
freshness; the app owns the existing query parser/classifier. An embedding
that invokes the library loop directly must install a provider to serve this
request. A missing provider returns an explicit unavailable/pending response.
The former subprocess implementation remains an explicitly named legacy API.

The source reader preserves canonical logical file identity. Open synchronized
documents supply current editor text; an invalid open document returns Pending.
Closed files use the existing bounded regular-file reader. No temporary source
path replaces the owner, and the new document-symbol route starts no child.

The shared query core reads through one request-scoped source reader. Reads are
memoized only between begin/finish; inactive CLI reads retain no disk cache.
Callback source paths and overlay generation/revision identities are checked.
Every consumed source becomes a dependency, retaining the actual text read.
Missing files also become dependencies because absence of `__init__.spl`
affects boundary classification.

Before returning, the handler verifies the target and global overlay generation.
Overlay dependencies must still match URI, version, lifetime and content.
Document versions are signed integers; only the lifetime marker distinguishes
closed disk snapshots. Negative versions remain valid for open documents.
Disk dependencies are reread and compared to the consumed content; missing
dependencies must still be absent. Closed targets additionally retain their
initial source text. Stale results return an error, never a cached permission
or an apparently current empty symbol list.

The request owner is synchronous and non-reentrant. There is no persistent
symbol index in this slice. Post-query dependency rereads are deliberate: they
validate both content changes and newly created boundary manifests. Reads are
bounded; no full workspace scan or retry loop is added to documentSymbol.
Qualification must measure warm startup, representative request latency and
max RSS on realistic fixtures. No latency/RSS target is claimed achieved here.

## Regression coverage and qualification status

Source tests cover actual didOpen/didChange, unchanged disk bytes, closed-file
queries, inactive-reader freshness, wrong-owner callbacks, changed manifests,
and absent manifests created during a query. The native probe uses production
document sync, app composition and handler modules. Its disjoint disk/overlay
symbol names prevent substring false failures; acceptance requires the exact
`LSP_OVERLAY_PROBE_PASS` output and exit 77. A zero-return stub cannot pass.

Prior attempt history is retained, and is not runtime evidence:

1. An address-space-limited launch was invalid and stopped at worker admission.
2. A wrapper rejected missing explicit workers before launching a compiler.
3. Another wrapper rejected inconsistent compiler-ceiling settings before launch.
4. A two-worker launch used fabricated worker estimates and is invalid for
   qualification. It refused SCV source membership before parsing.

The fourth snapshot (`6060355e...`) contains 42,384 source rows. Retained older
inventory `865473e7...` lacks the new probe and records the integration test at
6,575 bytes instead of 9,860. Current generation 4 inventory `bb357ba0...`
matches every snapshot row exactly. The refusal log does not identify the
inherited digest, so these findings demonstrate stale inventory candidates,
not a proven internal cause. No source-authority bypass is justified.

The reviewed source checkpoint is committed before a normal source capture.
The next supervised attempt is attempt 5 (third actual compiler launch), with
the real admitted Stage 2 producer `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`,
explicit serial workers, core-c runtime, private cache, and a 300-second/4-GiB
process-tree RSS watchdog. No address-space limit, fabricated estimates, or
speculative refresh flag is used. The full compiler/tooling checks, generated
manual and native qualification remain pending; this checkpoint is draft-only.

Attempt 5 passed normal source admission and completed all 129 MIR/AOP modules.
It reached native code generation, then stopped at the real process-tree RSS
cap after 186.129 seconds (peak sample 4,306,477,056 bytes; exit -15). No executable
was produced. The cache retains 115 native objects/capsule receipts and 129
frontend cache files. Logs and receipt are under
`build/lsp-overlay-supervised-20261114/` in the isolated worktree.

Review during that run identified two additional issues: negative document
versions were incorrectly treated as disk markers, and handwritten interpolated
JSON in the new fixtures was subject to the compiler's documented doubled-brace
decoding. The corrected sources discriminate by lifetime and use the canonical
JSON serializer. The native probe now includes a valid negative-version overlay.

Attempt 6 is the final allowed cycle, using the same real producer, 4-GiB/300-second
limits and retained cache after committing these fixes. No further automatic
retry, budget increase or attempt-history reset is authorized. Native acceptance
still requires actual probe execution and its output/exit sentinel.
