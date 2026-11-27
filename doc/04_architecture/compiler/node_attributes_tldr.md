# Managed node attributes: TLDR

The accepted [architecture](node_attributes.md) retains ordinary field syntax,
whole-node construction obligations, exact schema types and explicit owner access.
Its canonical schema owner is `src/compiler/00.common/data/`; do not create a
parallel NodeAttribute resolver. Existing StorageLayoutPlanV1, CollectionPlan,
trace and `.sprof` owners keep their authority.

The [V2 structural extension](../../05_design/compiler/data_schema_v2_contract_extension.md)
adds explicit views and stored/computed/forwarded property contracts over frozen
V1. Use its outer versioned digest for full semantics; the V1 projection cannot
prove V2 readiness or represent all type qualifiers. Canonical type/symbol binding
and generated access/lifecycle enforcement remain consumer work.

Resolve and freeze per context on the cold path. No SDN parsing, string schema
lookup or new profiler is added to managed field hot paths. Exact logical input
or contract changes invalidate semantic identity; physical/profile identities
stay separate. Profiles rank already-safe candidates and never establish safety.

Read the [program matrix](../../08_tracking/data_attributes_program_progress_2026-11-07.md)
for landed foundations and outstanding W0–W10 evidence. The current V2 unit/manual
artifacts are authored; admitted runtime execution, docgen and full integration
qualification are pending. A structural slice is not whole-feature completion.
