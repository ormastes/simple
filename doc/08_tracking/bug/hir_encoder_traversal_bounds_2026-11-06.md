# HIR encoder traversal continues after refusal — 2026-11-06

Owner: release100_memory_mcp_lsp / debug_truth.
Status: claimed; implementation awaiting owner scope admission.

## Evidence

`HirCodecWriter.create_canonical_bounded` caps charged writes but has no node
or recursion-depth entry contract. Generated hc_enc_* functions keep accessing
fields and traversing lists after writes poison the writer. Generated dictionary
paths call `.keys()` and key-order routines without invoking the existing
writer account_key_snapshot/account_*_key_order methods. Direct callers such
as ownership body hashing therefore cannot claim bounded traversal merely
because final output is refused. `put_text` also reaches the legacy escape path
without an initial poisoned-writer guard.

## Repair contract

Keep the existing3-argument bounded constructor compatible, add a finite default
node depth and explicit override, and balance node entry/exit through generated
public wrapper/private body pairs. Every generated operation and container
iteration must short-circuit poisoned state. Charge node/element work and admit
key snapshots/sorting before materialization. Stop hand-written text scans on
poison/output limit. Preserve valid canonical bytes and legacy unbounded writer
callers; reject deep/oversized values with explicit bounds reasons.

## Verification prerequisites

No admitted generator/test runtime is available to this lane. Source generator
and checked-in projection must carry equivalent transformations, but mechanical
projection editing is not a regeneration PASS. Canonical generated availability
remains false until the repository generator/freshness check and actual HIR
regressions run with admitted provenance. The canonical commands are
`bin/simple run src/app/compiler_schema/main.spl codec` and
`sh scripts/check/check-hir-codec-complete.shs`; use the admitted runtime only.

Source repair and focused regression obligations prepared. See `doc/07_guide/compiler/hir_codec_traversal_bounds.md`; runtime and actual generator reproducibility remain pending.
