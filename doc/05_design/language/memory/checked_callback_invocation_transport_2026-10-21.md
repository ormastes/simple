# Checked callback invocation transport

Date: 2026-10-21. Status: proposed prerequisite; **not implemented or qualified**.
Scope: AC-BOR-04 synchronous fresh views through an actual indirect callback invocation.

## Current dependency

`checked_sync_callback_regions` in `src/compiler/35.semantics/param_effects/callback_contracts.spl` returns function-symbol → callback-parameter-position → fresh argument positions. Its proof walk checks direct explicit owner parameters but does not retain the invocation's owner-symbol association, access mode, or stable call identity. This table cannot authorize a mutable loan or establish the provenance of an actual MIR callback argument.

`record_short_call_contract` in `src/compiler/55.borrow/borrow_check/mod.spl` resolves checked effects from exact constant named callees. A callback represented by a local operand receives no such contract. `MirSignature` function types establish shape, not checked non-retention, permission to mutate, or fresh owner authority. Existing imported callback receipts do not authorize reference-bearing signatures merely because scalar callback receipts are supported.

The design below requires a new admitted producer receipt. Copying the existing positional table into MIR is insufficient.

## Proposed typed records

These are proposed fields, not declarations that currently exist.

`HirCheckedCallbackInvocation`:

- `module_path: text`: canonical declaring module identity.
- `function_symbol: SymbolId`: unique, symbol-table-validated enclosing definition.
- `callback_parameter_symbol: SymbolId`: unique parameter owned by that definition.
- `invocation_id: text`: stable identity of this actual call expression within the admitted body; a source span alone is insufficient.
- `argument_modes: [text]`: full positional checked `read-short`/`mutate-short` modes; scalar positions explicitly identified by a separate slot classification, not omitted.
- `fresh_positions: [i64]`: positions authorized to introduce a fresh view.
- `owned_source_symbols: [SymbolId]`: aligned with `fresh_positions`, naming actual explicit owner parameters used at this invocation.
- `owner_capabilities: [text]`: aligned with those owner symbols; validated read or exclusive permission, independent of whether the owner is unique/shared.
- `body_digest: text`, `signature_digest: text`, `proof_version: text`: bindings to the complete admitted definition and proof rules.

`MirCheckedCallbackInvocation` on `MirFunction` and `MirBody`:

- `callback_local: LocalId`: exact emitted callback operand local.
- `block: BlockId`, `instruction_index: i64`: exact invocation site; terminator sites need an explicit site-kind tag.
- `argument_modes: [text]`: full original positional modes and arity.
- `fresh_positions: [i64]`, `owned_argument_locals: [LocalId]`, `owner_capabilities: [text]`: aligned invocation-specific authority.
- `origin_boundary: i64`: enclosing short boundary, never the nested call's incidental point number.
- `proof_identity: text`: canonical module/function/invocation identity plus admitted signature/body/proof-version binding.

Records must have typed constructors and validation. Parallel arrays require equal lengths, unique valid positions, full arity checks, and valid owner/local IDs; malformed records provide no authority. An optional future record-per-slot representation may remove alignment hazards without changing the semantics.

## Producer and lowering

The callback proof producer validates the enclosing definition, parameter ownership and uniqueness against the module symbol table, including collisions with globals. It proves synchronous direct invocation, non-retention, no suspension, a bounded fresh region, actual explicit live owner sources, and each requested access permission. Pairwise actual argument places must be compatible: repeated readonly access may be valid; overlapping exclusive access is rejected. A shared owner is not by itself permission to mutate.

Only a wholly admitted report publishes receipts. Bind receipts to complete body/signature identities; provisional, diagnostic-bearing, stale or imported-unvalidated rows remain unavailable.

During actual call emission, lowerer maps callback and owner `SymbolId`s through its authoritative `local_map`. It binds the receipt to the exact emitted block/site and argument order. A matching basename, `FuncPtr` type, lambda parameter type, inferred mutability or arbitrary local initializer cannot supply authority. Missing or ambiguous mappings invalidate the row. The function/body owners preserve receipts explicitly; serialization must version the new schema and invalidate old incompatible caches.

## MIR and NLL consumer

For `Call`/`CallIndirect` or a supported call terminator with local callee operands, require exact receipt site, callback-local identity, arity, modes and owner argument mapping. Resolve actual place/provenance through the existing NLL alias state rather than source-order assumptions.

Fresh owner arguments introduce an invocation-scoped loan and close it on synchronous return. Forwarded short arguments retain their original boundary; a receipt never widens it. Check all simultaneous argument footprints and all non-delegated active loans using the call-loan checker. Reentrant conflicts remain errors even when origin tokens match. Copies, projections or callback results must not erase retained loan origins. Escaping results, stores, captures and suspension remain forbidden for the fresh view.

Unknown callback contracts fail closed when a borrowed argument or requested fresh-view privilege depends on them. Ordinary scalar calls acquire no irrelevant borrowing requirement. Unwind, suspension or retained-callback routes remain unsupported until they have explicit region exit/lifetime rules; a synchronous receipt does not authorize them.

## Transform preservation and invalidation

Any local, block, instruction, argument, callee or body rewrite must remap and revalidate the receipt or remove it. Function cloning/specialization needs a new proof identity and correct source-to-target symbol/local mappings. Inlining must remap boundaries without merging independent invocation regions. Outlining cannot inherit an enclosing receipt implicitly. Dead-site removal removes its receipt. Merely copying a function's metadata after changing its body is insufficient.

Cache, codec and optimizer round trips must preserve the same owner and site identity or invalidate the authority. This design does not add destructor metadata or change a global cleanup policy.

## Required acceptance evidence

Positive controls must traverse source → admitted HIR receipt → actual MIR local-callee invocation → NLL, inspecting the receipt and resulting scoped loan:

- Repeated readonly invocations borrow an explicit live owner separately and end each fresh region before the next.
- A scalar callback invocation and an independent scalar loaded within the view return successfully without retaining a loan.
- Proven exclusive views of disjoint fields succeed only with validated mutable capability and actual nonoverlapping places.
- Valid synchronous forwarding preserves the original boundary across nested call sites.

Negative controls must reject shared-owner-to-mutable permission escalation, repeated/overlapping mutable arguments, reentrancy against a live conflicting loan, escaped/stored/captured views, suspension, owner consumption before invocation, unknown dynamic callbacks, changed boundary, unknown owner mappings, named-argument reordering without normalization, arity mismatch, duplicate/global-colliding symbols, stale body/signature digests, wrong callback local/site, and optimizer/codec receipt drift.

No new tests or builds accompany this design. Existing source checks and library lease probes do not establish this end-to-end acceptance. AC-BOR-04 remains open pending implementation, independent review and executable evidence.
