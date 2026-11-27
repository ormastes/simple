# Canonical data schema V2: structural extension

Date: 2026-11-07. Package: W0/W1a of the
[accepted program](../../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md).
Status: implementation/test source approved by Astra, including UTF-8 byte bounds; runtime qualification pending.
<!-- codex-architecture -->

## Existing authority and compatibility

The release baseline is `98669e12655ab2be54aec09acc118aeb43ee8ff0`.
PR #7220 already established `compiler.common.data.data_schema_contracts` and
`data_schema_resolver`. V2 extends that owner; it does not introduce a separate
NodeAttribute resolver or change frozen V1 field meanings and digests.

`data_schema_resolve_v2(authority, views, decls, aliases)` invokes
`data_schema_resolve_v1` once for tree-wide attribute names, exact flat nominal
types/aliases, requiredness, defaults and applicability. V2 then validates the
additional logical contract. A successful V2 surface contains its V1 projection,
explicit views, resolved property contracts, contract version 2 and a separate
SHA-256 semantic digest in the `simple.data-schema/v2` domain.

The V1 projection digest remains useful for V1 compatibility. It cannot identify
the full V2 schema or authorize V2 lifecycle operations. AttrId ordinals remain
one-based and schema-local; V2 consumers must bind them to the V2 digest/context.
V1 construction facts do not enforce computed/forwarded readiness merely because
a V2 caller passes them `surface.base`.

## Contracts and layer boundaries

The three new modules stay under `src/compiler/00.common/data/`:

| Module | Responsibility |
|---|---|
| `data_schema_contracts_v2.spl` | Pointer-free versioned input/output contracts, explicit view identity, property kind and access facts, size bounds |
| `data_schema_resolver_v2.spl` | Canonical base reconciliation, authority/applicability checks, property agreement, dependency validation and V2 digest |
| `data_schema_sdn_v2.spl` | Dedicated versioned schema-document normalization using the existing shared SDN parser |

There is no storage allocation, file I/O, RuntimeValue, compiler HIR object,
physical layout enum, collection algorithm or trace provider in these contracts.
Existing StorageLayoutPlanV1, CollectionPlan, `.sprof` and trace owners retain
their authority. A future driver adapter supplies already-bound canonical symbols
and explicit build authority; SDN cannot grant itself an owner by declaring one.

## Semantic reconciliation

Views are explicit, including fieldless views. An attribute may only use a
declared view in the authorized tree. Equivalent declarations merge provenance;
all declarations of one attribute must agree on property meaning across views.
Only applicability unions. The property includes kind, visibility plus explicit
restriction owner, writability plus mutation owner, accessor/forwarding symbols,
phase key, read/write effect declarations and dependencies.

Stored properties have no accessor/forwarding target. Computed properties require
a canonical getter and, if writable, setter. Forwarded properties name an
applicable target with the same exact type; writable forwarding requires a
writable target. Computed/forwarded properties carry Required readiness and no
default initializer. These facts do not execute accessors or prove readiness.

Public visibility forbids a restriction key. Restricted visibility and writable
properties require explicit canonical owner keys; provenance never supplies them
implicitly. Read-only properties forbid mutation-owner/write-effect claims.
Effects are declared facts awaiting compiler/body checking. Empty explicitly
declared effect lists are not structural proof that an implementation is pure.
Phase keys are retained semantics, not a claim of execution-phase support.

Dependencies include forwarding targets. Every target must exist and apply in
every applicable source view. Indexed adjacency and an in-degree queue provide
O(V+E) dependency elimination and reject self/indirect cycles;
this version does not admit construction groups. Effect/dependency names are
sorted and deduplicated. The V2 digest includes explicit views and every property
field, while excluding declaration order and provenance. Variable fields and
lists are length-prefixed to avoid delimiter aliases.

V1 supports flat nominal type arguments only. V2 validates dotted identifier
spellings before calling it, rejecting commas, generic punctuation, whitespace,
empty segments and malformed alias targets. It deliberately does not introduce a
generic/type parser. Full nested generics, qualifiers and language symbol binding
remain a later extension of the canonical type owner.

## SDN, costs and invalidation

The [input guide](../../07_guide/compiler/data_schema_v2_input.md) defines the
dedicated `simple.data-policy/v2` schema document. It produces the same
`DataSchemaInputV2` values as constructed SPL declarations. Unknown/unsupported
keys, duplicate keys, wrong shapes, missing explicit effects, unsupported versions
and count limits are errors; no usable partial surface is returned.

Resolution is a cold per-context operation. The inherited V1 grouping plus bounded
sorting have polynomial cost; new indexed dependency traversal is O(V+E).
No schema lookup/parsing is added
to a field-access hot path. This slice does not add an ambient cache. Future driver
contexts should freeze one resolved snapshot and invalidate it when exact logical
inputs or contract versions change. Physical/profile identities remain separate.
No latency/RSS target is claimed verified by source inspection.

## Tests and outstanding work

`test/01_unit/compiler/data/data_schema_resolver_v2_spec.spl` asserts SPL/SDN
equivalence, retained provenance, explicit empty views, unchanged V1 projection,
semantic digest differences, access-contract errors, forwarding/dependency
validation and malformed input refusal. Tests are authored, not executed here.
The [manual](../../06_spec/01_unit/compiler/data/data_schema_resolver_v2_spec.md)
is manually maintained; admitted docgen/maintenance output is pending.

Frontend extraction, real canonical symbol/type binding, build off/enabled mode,
driver freeze, LSP, managed places, must-resolve cleanup, runtime storage and
observation remain separate work packages in the
[program matrix](../../08_tracking/data_attributes_program_progress_2026-11-07.md).
This structural extension does not complete W0/W1 or the wider feature.
