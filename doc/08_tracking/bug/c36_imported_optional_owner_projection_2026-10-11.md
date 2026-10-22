# Imported Optional payload loses provider ownership

Issue: https://github.com/ormastes/simple/issues/3025

Status: source repair and production-API regression authored; execution pending.

## Mechanism and bounded scope

At C36 manual source `aeb2517fac0a3f287aed4347d75235ac8976161d`,
`imported_surface_type` recursively projects tuples, arrays, functions,
references and pointers through the declaring module. It omits
`TypeKind.Optional`, although the frontend dependency walker visits that
payload. Its catch-all calls `lower_type` in the consumer scope. A registered
qualified payload can therefore be missed or replaced by a same-spelled
consumer type. The rich parser's Optional and flat parser's Named Option are
distinct inputs; the latter already recurses into named arguments.

The fix uses the existing two-argument Optional accessor and recursively
projects the payload through the same provider. Its fallback is an Error node,
never the outer Optional, so an accessor fallback cannot cause recursive
re-entry on that outer node. An Error payload produces an explicit diagnostic
and HIR Error before the existing lower_type fallback can erase it to Infer.
Legitimate Infer payloads still use existing inference lowering. No parser
accessor, malformed-AST representation, symbol registration, import visibility,
or unresolved-name lookup policy changes.

## Actual evidence and limits

Retained C36 manual evidence is under
`build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-reviewed-fixes/`
in `/home/yoon/dev/simple-bootstrap-c06-20261011`, in the compiler-driver and
bootstrap-k1-selected fatal-group receipts. Driver recorded 57 fatal events
across 16 modules; bootstrap recorded 38 across 10. Several innocent consumers
report unresolved ImplBlock or MirType without naming those types directly.
`trait_solver.spl` returns `ImplBlock?` from two methods and
`mir_types.spl` declares `MirVariantDef.payload: MirType?`.

These are source-backed witnesses, not runtime provider-binding proof that all
retained failures took this path. Owner tracing was not enabled. LocalId,
SymbolId, MirSignature and other failures remain independently unqualified;
this patch must not be described as a complete CLI or whole-HIR repair.

An external uncommitted 22-line prototype was used only as a design handoff.
Its one-argument nullable accessor differs from C36's existing API. No external
dirty implementation or duplicate accessor was copied into this candidate.

## Focused regression and qualification

`test/01_unit/compiler/hir/imported_optional_owner_projection_spec.spl` uses
real HirLowering methods and real allocated provider symbols. Cases cover
qualified-only Optional, a conflicting consumer Payload, existing Named Option,
and plain Named. Both Optional cases also exercise the projected entrypoint;
all assert the exact provider SymbolId and zero diagnostics. Two further controls
distinguish rejected Error payloads from legitimate inferred payloads.

No compiler construction, seed test, native execution or SSpec run was performed
for this source candidate. Independent source review and coordinated affected-
file manual HIR/MIR/object validation are required before integration claims.
