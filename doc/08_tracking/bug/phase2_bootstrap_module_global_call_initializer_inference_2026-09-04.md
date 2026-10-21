# Phase 2 bootstrap cannot infer a module-global call initializer
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Open compiler inference defect; the focused bootstrap admission probe uses an
explicit type annotation so cross-module global identity remains testable.

## Reproduction

With `SIMPLE_NO_STUB_FALLBACK=1`, the admitted-candidate Phase 2 macOS arm64
compiler rejects this otherwise typed initializer before MIR linking:

```simple
fn initialize_value() -> i64:
    42

val initialized_value = initialize_value()
```

The failure is `bootstrap MIR lowering: cannot derive module static type from
unresolved initializer; add an explicit annotation`. The function return type
is already explicit, so bootstrap lowering is failing to propagate it into the
module-global declaration.

## Required fix

Bootstrap MIR type resolution must use the resolved callee return type for a
module-global call initializer. Admission requires the unannotated form to
build under strict no-stub mode and retain the existing cross-module exit-42
identity behavior. Until then, the canonical module-global identity probe uses
`val initialized_value: i64 = initialize_value()`; this does not change its
runtime identity assertion.


## 2026-10-21 imported record constructor reproduction

The noGC owned-lease native diagnostic reproduces this inference defect with
imported record constructors, not only imported function calls:

```simple
use std.nogc_sync_mut.ptr.weak.{WeakLease}
use std.nogc_sync_mut.ptr.lease.{LeaseView}
var saved_view = LeaseView(view_id: -1, epoch: -1)
var callback_lease = WeakLease(token_id: -1, generation: -1)
```

The first native lease diagnostic build failed at
`test/fixtures/compiler/nogc_lease_view_probe.spl:6:18` and `:8:22` because the
module-static initializer types remained unresolved. The diagnostic fixture
now states `saved_view: LeaseView` and `callback_lease: WeakLease` explicitly,
preserving the imported constructor, payload, lifetime checks, and exit-backed
failure guards. This is a bounded verification workaround, not a compiler fix.
The inferred source forms above remain OPEN pending a producer that propagates
resolved imported constructor result types into module-static declarations.
The annotated fixture retry was not run by this editing agent.
