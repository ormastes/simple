# MCP record-array field and loop element ownership

Status: OPEN. Canonical ID: `mcp_record_array_owner_loss_2026_10_11`.
GitHub: https://github.com/ormastes/simple/issues/3079

Actual failing source: `a51194b96b5f5ce3fa57670bc62a15c2414388bf`.
Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/release-phase3-canonical-preparation/attempt3-mcp-failure/{failure.json,mcp_build.log}`.

Six I64/non-array for-in diagnostics occur at `src/app/mcp/main_lazy_assistant.spl:719,738`,
`main_lazy_ctx_tools.spl:349`, `main_lazy_log_opt.spl:67`, and
`main_lazy_telemetry.spl:134,267`. The declarations are arrays:
`AssistantSessionRecord.child_tasks: [AssistantChildTaskRecord]` and
`SdnTable.rows: [SdnRow]`. `src/lib/nogc_sync_mut/database/core.spl:655,658`
also loses the `SdnRow.get` method owner on loop elements.

Concrete compiler gaps found: provider Array/Slice field element Named IDs
were reused in importer tables; array-return shapes used bare record names;
for-in bindings copied only storage/layout and omitted element HIR metadata;
Some(local-alias) did not reuse the local's optional provider layout.

The candidate repairs compiler metadata, without changing consumers, container
values, iteration order, or runtime representations. Prescan retains exact
provider identities; importer fields and call returns rebind Named elements
against those identities; for-in binds the same declaration as array indexing;
Some patterns retain the typed optional local's layout. Existing scalar and
unknown-iterator rejection remains unchanged. The new direct record-element
transport rejects missing provider keys, unavailable consumer owners, and
nonempty generic type arguments with fatal diagnostics: it has no evidence
for relocating those argument IDs. Established direct Named field handling
is unchanged. This candidate covers immediate non-generic record elements
only; nested container and function-signature relocation remain outside the
repair. Registry misses retain prior signature fallback behavior, so alias
and collision native qualification is still required.

Tests: `test/01_unit/compiler/mir/record_array_owner_provenance_spec.spl` covers
provider-ID collision, same-name absent-provider rejection, loop binding type,
and scalar negative controls. `test/fixtures/compiler/record_array_owner/`
contains provider/decoy modules, actual Optional-alias and nested-array loops,
row method/value assertions, missing Optional/key controls, and a scalar
non-iterable negative entry. Existing `declared_iterator_provenance_spec.spl`
also pins unknown/i64/Any/dict/non-word rejection.

All tests and native fixture execution are AUTHORED_UNEXECUTED under the disk
hold. Source review and actual MCP qualification are required. These concrete
gaps do not establish that every observed error has one cause. Keep OPEN until
an immutable repaired producer passes fixtures and all eight actual sites.
Separate MCP StructLit, extend, Result.map, float conversion, JSON optional
array, and unlocated trim errors remain outside this change.

**Revalidated 2026-11-02: still plausible because OPEN. Canonical ID: mcp_record_array_owner_loss_2026_10_11; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 lane s3g3: fix-implemented-verification-pending
- The candidate repair is in the tree (squashed sync `3d6a3b7a0f6`, refined by `b33f2740173` and later
  pass-through rules in `rebind_record_element_owner`: no provider key or a generic element is passed
  through un-rebound instead of failing the build).
- `test/01_unit/compiler/mir/record_array_owner_provenance_spec.spl` was stale (4 of 6 failed on the seed):
  the provider symbol was never bound in the qualified-type table, the two rejection examples contradicted
  the deliberate pass-through behavior, and `lower_for_array_indexed` gained 2 parameters. Fixed the spec;
  now 6/6 pass: `bin/simple.exe run test/01_unit/compiler/mir/record_array_owner_provenance_spec.spl`.
- Remaining: stage3 native build of the MCP sources (`main_lazy_assistant.spl:719,738` etc.) with zero
  I64/non-array for-in diagnostics.
