# Paged historical-query regression slice

This additive source slice exercises the existing REQ-032 historical lookup and
REQ-019/030 provenance boundaries. It changes no selected requirements and adds
no remote authority, migration or runtime qualification.

## Fixture and ownership

`test/fixtures/scv/db_paged_history_fixture.spl` defines
`setup_item2_paged_history_entity`, `setup_item2_paged_history_patch`,
`setup_item2_paged_history_policy`, `setup_item2_paged_history`, and
`setup_item2_paged_history_checkpoint`. The integration spec uses
`check_item2_paged_history_exact`. Metadata allowlists and signing keys are
explicit test policy; production code never generates them.

The fixture initializes the actual Paged backend, admits two signed immutable
manifest observations, writes distinct evidence CAS objects, archives the first
manifest image, and installs an independently signed checkpoint containing real
History, Acceptance and Disposition records for both revisions. Page objects
are copied through the actual external checkpoint page source; no boolean or
caller-provided query result replaces proof reads.

The second UID uses a fixed counter found by bounded local hash exploration.
Its row key shares the first settled-alias key's bucket. The fixture asserts
the equality with the production key/bucket functions and asserts that the two
actual alias page digests differ. This makes deletion of only the historical
page observable while the current alias page remains available. There is no
per-test collision search and no performance claim.

The fixed counter is `87716`, and both production-derived keys must hash to
bucket `985c`. The bounded exploration examined counters 2 through 87716;
runtime fixtures only assert this known vector.

## Acceptance sources

1. Resolve an old settled alias using the requested root; bind original UID,
   accepted batch, semantic CAS digest and exact evidence digest. A not-yet
   allocated alias/row must not resolve through the current root.
2. Delete or corrupt only the old alias bucket. The old query must report typed
   missing/corrupt semantic data while the current alias still resolves exactly;
   all active and checkpoint generations stay unchanged.
3. Reject wrong namespace/epoch and insufficient cumulative page-read budget.
4. Construct and sign a structurally valid candidate checkpoint that rewrites
   an existing run_manifest field. Actual installation must reject immutable
   row regression and preserve both active HEAD and checkpoint journal.

## Concrete owner corrections and source status

The page reader previously reported an absent immutable object as a scope
failure, and its lower byte-reader facade exposed a prose size-limit error.
The page owner now probes native entry presence (dangling links still exist),
then uses the existing retained-handle IO facade. Actual handle metadata applies
the hard 16 MiB page cap and remaining proof budget before payload allocation.
Reads use chunks of at most 1 MiB, verify EOF and unchanged identity/size, and
close the handle on successful and failed reads. Historical query maps genuine
`SCVDB_PAGE_MISSING` to `SemanticMissing`; quota remains a typed unavailable
result. Scope/type errors remain hard failures. No new native ABI was added.

Six Paged history scenarios cover requested-root aliases, separate old/current
page objects, missing/corrupt data, dangling links, cumulative proof quota,
foreign namespace/epoch, actor-counter availability and signed checkpoint row
regression. Three direct physical page-reader scenarios cover empty/missing,
actual oversize/retry and dangling links. These sources are UNEXECUTED. Core,
library and MCP/LSP runtime smoke checks remain outstanding without an admitted
runner; static inspection does not close those gates.

The core agent owns these fixture/spec files and concrete owner fixes they
expose. The evidence agent owns Reference rollup/key-loss tests. The research
agent independently reviews the cohesive source. At most three bounded
source-review/fix cycles; no admitted runner is available, so execution remains
UNEXECUTED. External Paged page archives and protected publication remain open.
