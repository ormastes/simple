# Rich semantic type data schema resolver V3

Source: `test/01_unit/compiler/data/data_schema_resolver_v3_spec.spl`.
Requirements: structural part of REQ-001 and REQ-013.
Status: manually authored companion; examples UNEXECUTED. Admitted runtime
docgen/maintenance results and actual language binding evidence are pending.

## Declare explicit views and property contracts

Supply a complete semantic-owner identity for a nested nominal/reference type.
Resolve it under the authorized tree and explicit view. The result must preserve
the complete identity, schema-local AttrId and V3 version. Keep source/config
locations as provenance rather than using them as access authority.

## Reject incompatible logical contracts

Changing reference mutability, nominal declaration or declaring module must
prevent a conflicting attribute merge. Reject forged identity versions/byte
lengths. Forwarding must preserve the exact rich type and use the shared property
dependency rules; missing/unauthorized inputs fail without a partial schema.

## Verify canonical identities

Full type qualifiers and explicit fieldless views change V3 semantic identity.
Equivalent bound identities, reversed declaration order and repeated matching
origins retain it. Exact type equality comes from the semantic-owner descriptor,
not from the resulting schema digest.

## Resolve source and configuration through the language owner

The dedicated SDN V3 decoder retains the full type expression as explicitly
unbound syntax with its source location. Legacy `args` and wrong versions fail.
The frontend/type-binding lane must turn that syntax into a validated semantic
identity before it can enter the rich resolver. The common transport fixtures
alone do not demonstrate parsing/import/alias parity or generated field behavior.
