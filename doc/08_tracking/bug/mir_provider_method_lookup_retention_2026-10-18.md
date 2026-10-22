# Per-consumer provider method lookup retention

Bug ID: `mir_provider_method_lookup_retention_2026-10-18`.
Bug DB reconciliation pending: the qualified normal DB tool is unavailable.
Base: `afc7a68d38eb707058c4d5d540d5465222df03a7`, fetched from release_phase3.
Status: source fix proposed; native behavior and RSS effect are unverified.

Five `MirLowering` dictionaries are rebuilt at the start of every consumer
module: `struct_method_syms`, `struct_method_ambiguous`,
`struct_method_return_names`, `struct_method_return_is_array`, and
`struct_method_return_is_optional`. Provider registration visits methods across
the provider inventory, relocates their SymbolIds into the consumer symbol
table, and writes dispatch and return-shape lookup rows. Their consumer-local
identity is precisely why `lower_module` resets them before the next module.
Promoting them at the completed module boundary makes obsolete map versions
permanent before the next consumer replaces their roots.

The lifecycle is also present in the executing producer's baked `ee3` source
tree, `C:/dev/simple-phase2-value-diagnostic-producer-20261017`: resets begin at
`module_lowering.spl:1933`, while `transient_owner.spl:99` begins the five field
promotions. The target source is not being substituted for producer evidence.

Readers are MIR provider registration, receiver/operator resolution and
return-shape lowering. Lifted lambdas borrow the maps and lower synchronously;
their returned MIR functions contain instructions and signatures, not a
MirLowering owner or these lookup dictionaries. Driver and backend consumers
have no readers of these fields. Archive secondary lowering rebuilds method
rows and carries completed MIR/symbols/thunks, not the method dictionaries.

The patch detaches exactly these five roots after `lower_module` returns and
before normal transient-scope promotion. All completed MIR, symbol tables,
callable link metadata, declaration/default/layout facts, trait implementation
maps, global mirrors and thunk roots retain their existing lifetime. No child
allocation is explicitly freed; genuinely shared children remain protected by
the existing output/owner promotion paths. Scope-refused fallback and the
separate archive-owned scope are unchanged.

The executable regression uses real provider surfaces and two importing
consumers. Provider methods return a record, a record array and an optional
record; consumers call all three and project their results. An unscoped control
proves the fixture populates dispatch/return lookup tables. The scoped cases
check retirement, call targets, output signatures, borrowed input, and the
first instruction graph after the second consumer closes. Diagnostic JSON is
only an instruction-graph comparison, not a lossless archive.

This candidate is structurally capable of retaining provider-wide rows for
every consumer, but no cardinality, highest-impact ranking, RSS reduction or
83-GiB budget sufficiency is measured. Native regression/core/full-CLI checks
remain UNRUN while the qualified runtime is unavailable and the live build
owns the memory reservation. The base still has the known MIR source-guard
failures; the independent inventory/guard repair is PR #3653 and is not folded
into this three-file cohort. Passing fixtures from that lane are not evidence
that this independent tree passes its source or runtime gates.
