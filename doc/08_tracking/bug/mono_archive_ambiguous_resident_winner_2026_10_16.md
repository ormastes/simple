# BUG-MONO-ARCHIVE-AMBIGUOUS-RESIDENT-WINNER-20261016

Date: 2026-10-16. Status: source-confirmed repair candidate; native verification UNRUN. Database registration pending: no admitted database tool is available in this lane.

## Trigger and ownership gap

Base `67ba74d9acbaa998d5efcb3c162bf61a63f839d0` includes `7a3ddf580c5`, which correctly removes an ambiguous display name from `MonomorphizationPass.named_types`. Sequential archive registration still retains the first resident winner:

1. Collect/publish module A declaring `Shared`; the owner receives `NamedType("Shared", ...)`.
2. Collect module B declaring a distinct `Shared`. `record_named_type` rebuilds the worker map without that name and marks it ambiguous.
3. The delta collector iterates only remaining `worker.named_types`, so it emits no replacement/removal row for `Shared`. Its actual typed `NamedAmbiguous("Shared", true)` row carries the collision fact.
4. The installer previously wrote only the ambiguity flag. `owner.state.facts.named_types["Shared"]` retained A's old declaration while reporting ambiguity. Reversing A/B retained the other owner.

The existing `hir_mono_archive/main.spl` assertion added by `7a3ddf580c5` expects no resident winner, but this installation path does not establish it. This report does not claim that assertion was executed in this lane.

## Minimal source repair

`src/compiler/40.mono/mono_archive_registration_v1.spl`, installer `NamedAmbiguous` arm: after installing the original flag, a **true** value removes the corresponding resident `named_types` entry, if present. It rebuilds only that dictionary index and explicitly writes the updated facts back to the owner. All unrelated keys and other indexes remain unchanged. A false ambiguity row does not delete a named type.

This uses the same fresh-dictionary removal pattern already present in `record_named_type`; `Dict.remove` has divergent interpreted/native return contracts. It does not mutate an aliased dictionary while iterating it, promote a worker/full-index snapshot, or add a competing deletion protocol. The new index is allocated during the resident installer, after the existing scratch scope has ended.

Typed rows, predecessor/epoch checks, exact archived recollection, receipt seals, source/body/provenance bindings, ordered schedule digest and admission checks are unchanged. Only the resident application of an already admitted collision fact changes.

## Real regression and qualification plan

Two real source fixtures declare `A.Shared(value:i64)` and `B.Shared(value:text)`, plus unrelated `OnlyA`/`OnlyB`. The existing native archive fixture parses and lowers them, stores real HIR body archives, captures/recollects actual registration receipts, and publishes through the existing owner API in both A/B and B/A order.

Each control checks the initial unique `Shared`, the final true ambiguity marker, absence of a resident `Shared`, preservation of both unrelated types, actual owner epoch/archive/order, and the final admission seal's facts. Existing collision and forged receipt controls remain intact. No caller-created row/receipt or mocked HIR facts substitute for authority.

The current base should fail each new control at `ambiguous display name retained a resident winner`; the candidate must pass both with the same real runtime/provider admission inputs. This is a source prediction, not executed evidence. New checks return named failures/nonzero status, not empty or hardcoded passes. Native build and runtime checks are UNRUN; no constructor qualification retry, cache graft or attempt-count reset is authorized by this repair.
