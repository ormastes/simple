# Cache, per-file and Phase 3 parallel execution — 2026-10-26

Status: ACTIVE. Target: `release/1.0.0`. The full acceptance matrices remain
in scope; this task split does not redefine completion.

User directions: workaround first, then underlying fix; avoid rebuilding
Phase 2 if an admitted existing producer can build the workaround. After
Phase 3, land source-to-object/cache changes remotely and make the per-file
pipeline the default after its self-rebuild/link/sanity/overlap qualification.
Use 80 jobs for applicable main builds; report measured concurrency and
memory admission. Host inventory: 80 logical processors, 128 GiB RAM.

| Lane | Owner / model | Writable scope | Deliverable |
| --- | --- | --- | --- |
| Coordinator, optional payload workaround and native qualification | root / inherited highest model | existing wt-bisect, work/phase3-optional-payload-20261026 | actual-owner qualification, evidence review, integration and landing |
| Unresolved then caller workaround | then_workaround / gpt-6-luna high | existing wt-bisect-good only after clean/scope check, its own work branch | behavior-preserving narrow patch + real regression + native probe proposal |
| Worker argv / existing producer viability | worker_argv / gpt-6-luna high | read-only wt-s2new and wt-s3self2 | exact limitation, supported workaround interface, cache and 80-job constraints |
| Cache/default completion audit | cache_acceptance / gpt-6-luna high | read-only current release-based source/plans | remaining code gaps, executable evidence mapping, default/overlap contract |

Shared-interface guidance given before delegation: preserve existing public
signatures; introduce no new manual step/setup/checker helper interface.
Reuse existing helpers. Any necessary unfinished scaffold must fail explicitly;
no no-op or placeholder passing evidence. No sidecar may claim broad PASS,
accept exclusions, mark plans done, or merge another lane's work.

Merge owner and final reviewer: root, normal/highest-capability review.
Each sidecar result requires independent source and caller compatibility
review before integration. Distinct writable worktrees/output caches prevent
collisions. Existing active jobs and their compatible artifacts are preserved.
The already-running 124-module qualification diagnostic was launched with four
jobs before the 80-job instruction; it is retained, not presented as an 80-core
measurement. Subsequent applicable main builds use 80 jobs under measured
memory admission. No full-CLI/SPipe PASS may be inferred from compiler-only
Stage 2 diagnostic output.
