# Archive provider enum metadata is omitted from the declaration prescan

Status: confirmed source omission; focused runtime reproduction and campaign
causality remain unverified. Bug DB reconciliation pending: no callable bug DB
interface or qualified self-hosted CLI is available in this review environment.

## Evidence and limits

Reviewed compiler baseline: `1e93dca4ce3d7be2187da1b67cfeb1180179682e`.

`src/compiler/80.driver/cache/hir_mir_archive_consumer_v1.spl` calls
`prescan_module_declarations_v1` for the final repository's declaration order,
inside a transient scope, before lowering complete bodies. That prepass in
`src/compiler/50.mir/_MirLowering/declaration_providers_v1.spl` registers
struct/class layouts and callables, but never consumes `module.enums`.

`archive_borrowed_module_v1.spl` deliberately supplies an empty complete-body
provider array to `lower_module`. The latter registers only the active complete
module's enums. Consequently, the rich archive declarations cannot independently
populate the cross-module enum variant registry before a provider body is lowered.

The nominal overlay is not a substitute: `MonoArchiveNominalDeclV2` carries
symbol identity and ownership, but no variant names, discriminants, or payloads.
The rich `MirHirEnumDeclarationV1` summaries already retain that information,
including exact expression artifacts for explicit discriminants.

PR [3493](https://github.com/ormastes/simple/pull/3493) reports B5b in
`SdnValue.is_null` and says its unique-owner fallback did not resolve the failure.
Its public body/comment supplies no failing artifact path or executable command.
This report does not establish that the prescan omission caused that occurrence:
an active module retaining its own enum should register it during `lower_module`.
The failing logical module, its own enum declarations, and the repository's
provider declarations must be inspected to prove the connection.

## Focused reproduction to add

1. Project a complete provider containing a named enum with a unit variant,
   tuple payload, named payload, and explicit discriminant into the existing
   body-free declaration repository.
2. Prescan its declaration with a fresh lowering instance, without lowering the
   provider body. Assert the qualified variant owner and explicit discriminants
   exist; the current prepass cannot satisfy that assertion.
3. Lower a consumer before the provider, with colliding numeric SymbolIds and
   another enum sharing the same bare name. Assert correct qualified ownership,
   payload types/layouts, and variant-test MIR shape.
4. Retain the known unrelated typed-capture regression: `Op` matched by bare
   `Return` owned only by `Kind` must bind, never borrow that discriminant.

## Repair boundary and verification still required

Use rich declaration metadata and existing `register_enum_variants` /
`register_enum_runtime_id` semantics. Existing exact expression artifact loading
can recover explicit discriminants; `relocate_provider_type` handles nominal
payload references. Preserve runtime names, explicit values, payload kinds,
generic parameters, collisions, and transient ownership promotion.

Relocation is consumer-specific: the declaration prescan is a phase barrier,
while `lower_module` replaces its active SymbolTable for each consumer. A patch
must not retain payload HirTypes relocated only into the initial consumer's
numeric symbol space. The proposed `declaration_enum_metadata_v1.spl` adapter
loads exact artifacts at the phase barrier, retains ID-free owner indexes and
payload kinds/names, and lazily relocates only demanded payload types. It shares
the normal payload writer and propagates deferred metadata into lifted lambdas.
Runtime qualification remains pending; this is not a fixed claim. Do not relax
bare-name capture classification to conceal the omission.

Relevant existing specifications are `archive_borrowed_module_mechanics_spec.spl`,
`enum_bare_name_collision_dual_key_spec.spl`,
`generic_nominal_transport_spec.spl`, and
`bare_variant_untyped_subject_reject_spec.spl`. The new reproduction must execute
real prescan/lowering assertions; text-presence checks are insufficient.

Runtime status: **NOT EXECUTED**. No fixed claim or merge admission is established.
