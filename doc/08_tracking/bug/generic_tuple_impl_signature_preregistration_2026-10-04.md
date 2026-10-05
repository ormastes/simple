# Generic tuple impl receiver lowered before its parameter scope

The source9737/Cranelift Phase2 producer776ce2 bootstrap cohort recorded a failed HIR module, `src/lib/nogc_sync_mut/src/hash.spl`, while continuing independent modules. Its nine diagnostics were unresolved T1/T2, T1/T2/T3, and T1/T2/T3/T4. The earlier composite-parser defect produced unresolved `[`/`(`; this is a distinct later declaration pass failure.

`declare_module_symbols` registers impl method signatures at module scope. `declared_callable_type` defers a method with its own generic parameters, but the caller failed to account for enclosing impl parameters. A tuple receiver lacks a named owner symbol, so its full receiver type was lowered before those parameters existed. `lower_impl` already creates the correct scope and registers the parameters before lowering the receiver.

The repair keeps symbol preregistration but leaves generic-impl method and inherited-default signatures untyped, matching existing generic callable policy. Full impl lowering still checks the types and marks templates. Nongeneric signatures and unresolved names remain checked; no unknown type is accepted globally.

Eight executable regression scenarios cover tuple arities2/3/4, array parameters, inherited defaults, invalid generic and nongeneric targets, and sibling scope isolation. Native execution is PENDING: current live builds are frozen, host memory admission is unavailable, and their producers do not contain this source repair. No PASS or full hash/runtime qualification is claimed.

Evidence: `runtime/windows-restart-20261004/phase34-post-link4/hir-fatal-observation.json`, module terminal `fc239535632759152ebad8c1eac90d06a942d1efc262e7ec8a9088bfcc416cb7.terminal` in the retained Phase3 HIR queue.
