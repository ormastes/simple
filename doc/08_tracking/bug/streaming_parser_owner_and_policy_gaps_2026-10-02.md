# Streaming parser ownership and provider gaps

Status: narrow source candidate; native/SSpec **UNRUN**. No default routing
change and no claim of complete 7 GB memory qualification.

Reviewed pinned source08e1e3cfc72655614fe5a30d7ace67700faf6f6c and release base
1538f7da26270bd58cc8083f37326f1de3ed7160. Ordinary parser repair2170 retained
seven native parser owners, last-parse metadata and dirty cache memo owners.
Existing streaming surface/HIR boundaries still preserved only four semantic
registries. Cold token slots could therefore remain non-nil after their scope
freed them, and first/changed shared-authority memo roots could dangle.

Selected-provider and surface-extraction errors were also returned/read after
scope teardown without owning their Result/text. Registry-finalization errors
had the same lifetime problem. The HIR streaming reparse selected the Reference
entry with zero provider identities, despite phase2 honoring the context's
chosen provider/policy/cache identity.

The candidate reuses the existing generation-aware owner helper, preserves
error Results/text before closing, and uses the selected borrowed frontend for
HIR reparsing. The parse-error cleanup helper also preserves complete frontend
owners. Full streaming phase2 already initializes its private memo before
scopes; that is not claimed as a separate full-route defect. Existing target
cfg receipt handling remains; containing-map ownership is not newly qualified.

Before general enablement, additional work is required. The active
reverse-reference collector stores source aliases, facts and known families in
process globals; lowering can append scoped payloads that are not separately
owned. Its fix should accumulate per-module pending facts/aliases, preserve
only that bounded batch, and publish after scope end while preserving global
deduplication/order and current-module reads. Promoting the complete growing
phase graph per module would introduce quadratic work and is not acceptable.
The same audit must cover MIR transient producers, not just streaming HIR.

General parity must compare complete source/alias sets and HIR behavior for
generics, trait defaults, enum defaults/aliases, resources, decorators/effects,
supported macros/domain blocks, async transformations, diagnostics, cold/warm
caches and admitted provider identities. Coverage/MC/DC, full-inventory and VHDL
remain separate contracts. The focused native fixture in this change covers
cold slots, metadata, selected-provider rejection, error recovery and retained
HIR; it explicitly does not activate the reverse-reference collector.

Windows70da full CLI hit the cap during parse2096/2493. The separate uncapped
diagnostic processed2493 sources but eventually exited1 with130 failed parse
sources after surface freeze, peak8,281,864KiB. It never reached HIR. Processed
progress counters are not successful-parse counts. Neither the uncapped result
nor this source repair is a capped acceptance PASS.
