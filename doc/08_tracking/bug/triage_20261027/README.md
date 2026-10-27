# Reviewed bug triage checkpoint — 2026-10-27

This is a durable, reviewable snapshot of the accepted classifications from the Astra lane reviews. It is a documentation checkpoint only: it does not edit the canonical bug database, close reports, or qualify fixes.

## Scope and accounting

The immutable audit inputs identify 1,602 unique open bug records at source snapshot `d805f566f89b9e830c292d5cc0a1e0f5f6449c37`; review classifications assess source target `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`. This checkpoint captures one consistent copy of all ten then-current review CSVs and records each CSV SHA-256 in [manifest.sdn](manifest.sdn).

- 1,602 authoritative IDs: 415 accepted classifications, 1,187 `needs_more_evidence`, 0 missing.
- Accepted classifications: 381 valid, 33 uncertain, 1 invalid. All 415 reproducibility values remain `untested`.
- Accepted actions: 270 keep open, 119 fixed pending verification, 25 fix candidate, 1 close invalid candidate.
- One invalid/closure candidate is `font_registry_bungee_digest_mismatch_blocks_selected_outline_path_2026-08-15`. This is only a reviewed candidate; no canonical closure was applied.
- “Fixed pending verification” records a classification, not a verified fix. Runtime probes were unavailable and no fix is claimed as verified.

Machine-readable rows are intentionally compact and contain only ASCII identifier-like cells to avoid the native SDN codec's quote escaping hazard. Full evidence references, titles from the original authoritative shards, and rationales for accepted rows are in [evidence/](evidence/). The [residual list](residual_ids.sdn) identifies all 1,187 rows that still need evidence; the captured unaccepted rationales remain in the hashed source CSV snapshot, not copied wholesale here.

## Merged PR receipts

These eight merged PRs are recorded as related receipts: [#5034](https://github.com/ormastes/simple/pull/5034), [#5035](https://github.com/ormastes/simple/pull/5035), [#5036](https://github.com/ormastes/simple/pull/5036), [#5041](https://github.com/ormastes/simple/pull/5041), [#5042](https://github.com/ormastes/simple/pull/5042), [#5043](https://github.com/ormastes/simple/pull/5043), [#5048](https://github.com/ormastes/simple/pull/5048), and [#5049](https://github.com/ormastes/simple/pull/5049). PRs #5048 and #5049 postdate the review target; they are not silently treated as inputs to the review classifications.

## Still required for the user's full triage goal

This checkpoint does not complete the requested 1,602-category audit. Canonical category writes, invalid-closure handling, current-runtime qualification, and evidence review/fixes for the 1,187 residual records remain outstanding. No claim of a full-audit PASS is made. No live bug DB, CRC, or status file was touched. No compiler or test toolchain was run for this documentation-only checkpoint.


## Append-only correction precedence

Later correction files supersede the archived row for the named `bug_id` while leaving `reviewed_categories.sdn`, the original evidence pages, captured hashes, and original partition counts unchanged. When a correction exists, readers should use its revised fields and rationale for the current classification and retain the original row as historical provenance. The [append-only correction register](corrections.sdn) currently has one entry: [GPU type mapper struct symbol ID layout](correction_gpu_type_mapper_struct_symbolid_layout_2026-10-24.md). The original 415/1,187/0 accounting is a historical snapshot, not a recount after corrections.


## V2 full-lane review snapshot (2026-10-27)

[V2 categories](reviewed_categories_v2.sdn), [residual IDs](residual_ids_v2.sdn), [manifest and receipts](manifest_v2.sdn), and [accepted evidence by lane](evidence_v2/) capture one consistent read of the ten final lane exports. Lane 04 uses `merged_review04.csv` and its merge receipt, not the earlier primary export. CSVs, V2 progress/partition files, and merge/overlay receipts are bound by SHA-256 in the V2 manifest.

- The frozen source set contains 1,602 unique IDs. V2 has 600 accepted classifications and 1,002 still needing evidence; none are missing.
- All 600 accepted classifications remain `untested`. Accepted means the review classification was accepted; it does not mean a test passed, a bug was closed, or a fix was runtime-verified.
- Accepted actions: 395 keep open, 173 fixed pending verification, 31 fix candidate, and 1 close invalid candidate. The invalid candidate is `font_registry_bungee_digest_mismatch_blocks_selected_outline_path_2026-08-15`; no canonical invalid closure was applied.
- The V2 row for `gpu_type_mapper_struct_symbolid_layout_2026-10-24` includes the correction already recorded in the append-only V1 correction register: valid, solution unknown, structural change unknown, keep open.
- Related merged code-fix PR receipts: [#5034](https://github.com/ormastes/simple/pull/5034), [#5035](https://github.com/ormastes/simple/pull/5035), [#5036](https://github.com/ormastes/simple/pull/5036), [#5041](https://github.com/ormastes/simple/pull/5041), [#5042](https://github.com/ormastes/simple/pull/5042), [#5043](https://github.com/ormastes/simple/pull/5043), [#5048](https://github.com/ormastes/simple/pull/5048), [#5049](https://github.com/ormastes/simple/pull/5049), and [#5054](https://github.com/ormastes/simple/pull/5054). PRs #5048, #5049, and #5054 postdate the frozen assessment SHA and are recorded as related implementation receipts, not promoted into its evidence. Documentation PRs #5053 and #5057 are not code-fix receipts.

## Revision precedence

V1 files, their manifest, and the append-only V1 correction register remain historical records. V2 is the later full-ID classification snapshot: for current classification lookup, use the V2 row for each ID, including the corrected Vulkan mapper row. The V2 review target remains the frozen `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`; merged post-freeze fixes do not change the assessment SHA or confer runtime qualification.

This remains partial progress toward the full user goal. Canonical bug database writes and runtime-qualified build evidence remain held pending the user's build-exception decision. No bug DB, CRC, or status files were changed, and no compiler or SSpec was run for this documentation snapshot. No full-audit PASS is claimed.


## V3 scoped aggregate checkpoint

V3 is a scoped derived snapshot of the original frozen audit (`d805f566f89b9e830c292d5cc0a1e0f5f6449c37`) assessed at `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`. See [V3 categories](reviewed_categories_v3.sdn), [residual IDs](residual_ids_v3.sdn), [manifest and captured input hashes](manifest_v3.sdn), [accepted evidence by lane](evidence_v3/), and the mandatory [reproduction scope table](reproduction_scope_v3.sdn). V1 and V2 artifacts and correction records remain unchanged historical snapshots.

- The final partition has 1,097 accepted classifications, 505 not admitted and still needing evidence, and no missing IDs. The 505 residual records are not all unreviewed: their report/source inspection may be recorded, but their reproducibility remains untested and no runtime attempt is admitted for them.
- Count provenance: the V2 baseline is 600 accepted (including merged lane 04); V3 then applies 16 adjudication queues covering 512 rows (497 accepted, 15 needing more evidence), yielding 1,097 accepted and 505 residual. [V2 manifest](manifest_v2.sdn) and merged lane 04 hash are explicitly bound in [V3 manifest](manifest_v3.sdn); the ten primary CSVs alone do not explain the baseline count.
- Exactly one of the 1,602 rows is reproducible, and only in mandatory `HOST_PROTOCOL` scope: `BUG-STAGE3-RESUME-SOURCE-POLICY-20261011`. The portable [reproduction evidence](evidence_v3/stage3_host_protocol_reproduction.md) records the retained command, exits, receipt IDs, report-paraphrased red excerpt, and the 14 dependency blobs identical between executed baseline `b0d3cf73dc19e75640952c220bf0e069230b5eda` and assessed `c0`. This demonstrates a shell argument-builder mismatch for that protocol case; it does not show an actual compiler build reproduced.
- The other 1,601 rows remain `untested`. No compiled Simple runtime is qualified; full Phase 3, compiler build, and normal CLI qualification remain `UNRUN`.
- The Bungee font registry record is the only eligible invalid candidate; no closure was applied. The cross-engine invalid proposal was rejected, leaving that row valid and keep-open.
- Six related code PRs were already included in frozen `c0`: [#5034](https://github.com/ormastes/simple/pull/5034), [#5035](https://github.com/ormastes/simple/pull/5035), [#5036](https://github.com/ormastes/simple/pull/5036), [#5041](https://github.com/ormastes/simple/pull/5041), [#5042](https://github.com/ormastes/simple/pull/5042), and [#5043](https://github.com/ormastes/simple/pull/5043). Four related code PRs merged after the freeze: [#5048](https://github.com/ormastes/simple/pull/5048), [#5049](https://github.com/ormastes/simple/pull/5049), [#5054](https://github.com/ormastes/simple/pull/5054), and [#5073](https://github.com/ormastes/simple/pull/5073). Post-freeze changes do not retroactively alter c0 classifications. Documentation/checkpoint PRs #5053, #5057, and #5061 are not code fixes.

### HOST_PROTOCOL scope limits

The red receipt (`exec-f1426a88-b544-492a-9bb1-3e213ab7524f`, exit 1) ran the six-test host protocol suite at baseline `b0d3cf73dc19e75640952c220bf0e069230b5eda`; the source-bound 14 dependency blobs match frozen `c0`. Only the digest/worker argument vector mismatch is admitted. The green receipt (`exec-12af553a-00fe-44f9-b64c-a872d0e83352`, exit 0) was recorded after remedy edits but before creation of `28493de7580915b9fc0fd104cd55cea9bb07edc5`; that commit records the matching code state. It is post-target host protocol evidence, not proof of a current compiler build or full Phase 3.

### Precedence and remaining work

Use V3 as the latest derived classification snapshot, with its single scoped HOST_PROTOCOL exception. V1 and V2 categories, manifests, correction rows, and counts remain historical and byte-preserved. The assessment SHA remains `c0`; later implementation fixes and protocol-only green receipts do not qualify a compiled Simple runtime.

Canonical bug database application and runtime-qualified build evidence remain held pending the user's exception. No bug status or closure was applied; no bug database was modified; and no compiler, system test, or live database was run for this documentation correction. This remains partial progress, not a full 1,602-report audit PASS.
