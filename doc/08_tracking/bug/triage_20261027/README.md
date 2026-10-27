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


## V4 final residual consolidation

V4 keeps the V3 scoped aggregate as its immutable base and replaces its 505 residual classifications with the final residual evidence set: `first_half_final_triage.csv` (13 accepted, 2 still needing evidence) and adjudication groups `v2_16` through `v2_31` (461 accepted, 29 still needing evidence). The additions contain 505 unique IDs and exactly equal the V3 residual-ID set. Therefore V4 contains 1,571 accepted classifications and 31 residual IDs, with no missing or foreign IDs. The [V4 merge receipt](merge_receipt_v4.sdn) records the row-level additions; [manifest_v4.sdn](manifest_v4.sdn) binds every source hash.

- The 1,097 accepted V3 rows are carried forward field-for-field; the V3 `HOST_PROTOCOL` source-policy reproduction scope is preserved in [reproduction_scope_v4.sdn](reproduction_scope_v4.sdn) with its portable evidence copied into [evidence_v4](evidence_v4/).
- The 474 newly accepted rows have their titles, source receipts, classifications, evidence references, and review rationales in the per-lane V4 evidence pages. The remaining 31 rows and their rationales are in [residual review details](evidence_v4/residuals.md). Residual status means not admitted as final; it does not mean every row lacked report/source review. Their reproducibility remains untested.
- Exactly one record is reproducible in `HOST_PROTOCOL` scope; the other 1,601 remain untested. No compiled Simple runtime is qualified, and full Phase 3, compiler build, and normal CLI qualification remain `UNRUN`.
- The Bungee font registry row remains the only eligible invalid candidate, with no closure applied. The rejected cross-engine invalid proposal remains valid and keep-open.

This checkpoint does not mutate canonical bug status, apply invalid closures, or claim a full compiler build/runtime pass. Canonical writes and runtime-qualified build evidence remain pending the user's build-exception decision. V3 and all older artifacts remain immutable historical checkpoints. No compiler, system tests, or live bug database were run for V4.


## V5 residual31 revision 2 consolidation

V5 supersedes the V4 residual classification with the independently approved revision 2 overlay. It preserves the V4 1,571 accepted rows and applies the 31-row overlay exactly once: six accepted (cases 4, 6, 9, 10, 11, 26) and 25 `needs_more_evidence`. The resulting partition is 1,577 accepted / 25 residual / 0 missing across the same 1,602 authoritative IDs. Revision 1’s all-31 acceptance was withdrawn and is not used.

The approved source CSV, Markdown, author receipt, independent GO report and delta receipt are copied byte-for-byte under [evidence_v5](evidence_v5/); [row-level evidence updates](evidence_v5/residual31_revision2.md) preserve each row’s evidence references, rationale and correction. [V5 categories](reviewed_categories_v5.sdn), [residual IDs](residual_ids_v5.sdn), and [merge receipt](merge_receipt_v5.sdn) record the admitted fields and accounting. [Manifest V5](manifest_v5.sdn) binds the V4 lineage, approved overlay, review receipts and V5 outputs.

Among these 31 updated residual rows, only release-wrapper case 4 has a known source remedy, marked `fixed_pending_verification`; all 31 overlay rows remain `untested`. V5 adds no invalid-closure candidate. One inherited HOST_PROTOCOL source-policy record remains the only reproducible record; no compiled Simple runtime is qualified, full Phase 3 remains `UNRUN`, and 1,601 records remain untested.

For current classification lookup use V5; V1–V4 files remain immutable historical snapshots. This is still partial triage progress: no canonical category write, invalid closure, runtime qualification, compiler build or SSpec was performed. Canonical application and runtime qualification remain held pending the user’s build-exception decision.
