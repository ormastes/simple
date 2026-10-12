# Actual monomorphization archive transaction boundary

Status: source analysis and concrete implementation contract, following the
first shared HM consumer adapter. This document does not implement or activate
a bounded monomorphization route. No native jobs, RSS improvement, full CLI PASS,
or original promoted HIR reclamation is claimed.

## Actual retained owners and consumers

`40.mono/monomorphize_integration.spl:process_modules` currently collects all
modules, rewrites every non-template root into `rewritten`, drains all requested
specializations into `specialized_functions`, reconstructs all result modules,
and reconstructs them again while pruning. Its `generic_functions` contains
canonical full bodies. Registration also puts original bodies into
`Monomorphizer.generic_functions`; `request_specialization` mirrors each request
into `MonomorphizationTable.pending_functions`. The integration pass never
drains or reads that engine table. These are actual body references, not just
declaration rows. Removing a dictionary alias cannot free promoted objects in
the no-GC runtime.

The five template reads in expression/return inference, call rewriting and
generic-method lookup use only name, parameters, return type and type
parameters. `request_specialization` is the sole integration consumer of the
full canonical template body, through `specialize_function_with_types`.
`collect_generic_impl_methods` additionally reads the original function flags
and performs a specific canonicalization recipe. These semantics must survive
the archive boundary; deferred access cannot substitute an empty body.

`HirParam` contains a default `HirExpr`. A resident inference signature cannot
contain `[HirParam]` and still claim exclusion of expression graphs. Its exact
minimum fields are name, ordered parameter `HirType`s, return `HirType`, and
ordered `HirTypeParam`s. Type parameters include bounds/default types and symbol
identity, all of which stay intact. Signature types may retain their required
type-level data; function defaults, contracts and executable bodies belong to
the complete archive.

`module_symbols` is read by the integration pass only through
`mono_type_identity`: symbol lookup, declared name, defining module, fallback
module, and `hir_symbol_owner_module` normalization. A compact identity table
keyed by the original module and SymbolId can preserve those exact results,
including imported aliases. It must not substitute a global leaf-name map.
Full owning symbol tables remain in each module archive for final symbol
registration and downstream consumers.

## Smallest sound shared implementation boundaries

Introduce a typed `MonoTemplateSignatureV1` and change the real inference
implementation to accept it. Existing public HirFunction-taking methods can
forward through the projection for compatibility. Both retained and archived
body sources must use that same implementation. The signature extractor must
be applied to the exact canonical recipe; it cannot use the parser surface or
replace provider-private declarations with public ABI rows.

Next separate request identity from body instantiation in the actual
`request_specialization` implementation. During a root/body rewrite, a request
allocates its deterministic SymbolId, dedup/display key, owning module and FIFO
record, and derives its concrete return-type fact using the canonical signature.
It does not decode another provider module inside the current lease. The
existing instantiation routine performs no diagnostic publication; its return
type is `substitute_type(template.return_type, substitution)`, so the signature
can supply exactly the same enclosing-call inference fact. The current depth
refusal, mangling collision suffix, diagnostic ordering and dedup must remain
shared code rather than a second implementation.

Drain the FIFO through complete-body transactions. Each entry admits the exact
provider archive, retrieves the original function by SymbolId, verifies its
canonical signature/recipe digest, canonicalizes the actual complete body,
calls the existing `specialize_function_with_types`, assigns the already
reserved display name and SymbolId, and invokes the same body rewrite logic.
New requests append to the FIFO. Persist the fully rewritten specialization
before ending its scope. A missing/mismatched body aborts the semantic epoch;
it cannot leave a fabricated specialization receipt or permit MIR admission.

Preserve root order before FIFO draining: module dictionary key order, then
`sorted_function_indices`, then request order within each rewritten body.
This retains current SymbolId allocation and diagnostics. Template collection
keeps current overwrite/rejection behavior: ordinary function name keys are
not silently replaced with a new owner-qualified resolution policy, and
duplicate generic-method keys remain rejected as they are now.

Generic inherent method locations need a recipe with original module/function
SymbolId, declared method name, synthesized template name, ordered complete
canonicalization type parameters, and ordered bound type parameters. The
current recipe temporarily assigns all impl/method parameters, clears
`is_method`, renames the function, canonicalizes, then replaces type parameters
with the deduplicated bound list. Canonicalizing only the bound list would lose
symbol-spelled references for repeated parameter names and change semantics.

## Scope ownership and publication

The existing mutable `MonomorphizationPass` cannot simply be borrowed inside a
transient scope. Rewriting writes resident dictionaries and arrays with new
scratch references. Its retained changes are specialization display/SymbolId
maps; specialized return/name facts; template/owner records; FIFO additions;
diagnostics/warnings; once-only report keys; unresolved template flags; stats
and the next SymbolId. Local inference environment, match hints and suspended
return types are scratch only. Full specialized body values cannot escape.

Use an enumerated transaction delta for those retained changes. Read-only
resident summary maps remain borrowed. Fresh scratch overlays handle request
dedup, symbol facts and reporting within a transaction. Publish transformed
bytes first; pause; promote only the typed delta and descriptor; clear cache
warning aliases and any scratch references; end; apply the admitted delta to
the resident owner. Do not promote the pass, a closure capturing it, or the
whole combined summary table. Refusal or scope failure publishes no semantic
completion marker. Promotion/pause/end failures retain the existing fatal
ownership policy. Failure after disk publication leaves an uncommitted artifact
that the semantic epoch cannot consume.

An epoch tracks completed original roots, requested/emitted specializations,
and complete final module coverage. It inserts specialization symbol rows into
the real archived owning SymbolTable and raises that owner's counter to the
final pass counter, preserving the three rules at `MONO_SYMBOL_BASE`.
`template_was_specialized` must consult emitted specialization receipts, not
requests alone; unresolved and zero-instantiation templates remain present.
Final module assembly can stream actual function bodies into complete archived
modules; it cannot rebuild a persistent map of all rewritten roots.

## Immutable archive stages and validators

The existing first adapter admits only `lowered-unresolved-v1`. That is not a
valid substitute for the actual method-resolved/advice-transformed input to
mono. A new archive stage must bind the previous semantic receipt, all relevant
feature policy, exact producer/codec source, admitted runtime/provider bytes,
source content and full closure, and actual complete body digest. Distinct
resolved input, rewritten root, instantiated specialization, rewritten
specialization, and final post-mono module stages must not overwrite an old
pre-mono cache key. Descriptor/key mismatch is a rejection, never a fallback.

`80.driver/driver_hir_pipeline_passes.spl:monomorphize_with_policy` still requires
collection analysis and HIR phase admission, publishes leveled mono diagnostics
and pass receipts, rejects unresolved calls, and runs
`post_mono_verify_modules` under the same robust/critical policy. Its verifier
must visit every final real archived module and aggregate the exact existing
counter/diagnostic order. All earlier HM, safety, Any, enum, layout, effect,
criticality, aspect/advice and collection consumers remain required. MIR's
provider-body API is a later compatibility boundary; mono archives alone do
not make the full compiler memory bounded.

## Finite acceptance and implementation sequence

1. Extract shared signature inference without changing results, covering
   argument/result binding conflict, nested return-only generics, imported
   nominal identity, generic methods and default-expression exclusion. This is
   a real consumer seam, with no memory-repair claim by itself.
2. Introduce the exact request delta and complete-body FIFO transaction, using
   an actual imported template with a body value that distinguishes providers,
   nested generic requests and two specializations. Compare names, SymbolIds,
   return facts, diagnostics and complete output body digests to the retained
   route; read receipts after end and after second-scope allocation growth.
3. Reject wrong source/closure/runtime/producer/stage, altered recipe or body,
   missing required provider, occupied/nested scope and incomplete output
   coverage. Prove no request-only record permits template pruning.
4. Qualify streamed final module assembly and every post-mono validator before
   replacing the driver's full-map call. Archive initial HIR from an owned
   allocation transaction rather than retaining the original promoted graph.
   Only after the remaining aggregate/MIR adapters are sound should the root
   run the unchanged full CLI inventory and RSS cap again.

No activation flag or projected placeholder provider graph is proposed.
The immediate extraction and request/body separation are focused prerequisites;
complete bounded mono is an explicit remaining feature with the contracts above.
