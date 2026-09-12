# L7 semantic-owner revision V1 schema inventory

This focused manual records the closed, data-only schema for the five semantic
owner revisions used by the L7 scope contract. It does not create an owner,
issue a handle, validate a pin, or grant authority. Production liveness and
owner implementation remain outside this slice.

Requirements: REQ-CSM-003, REQ-CSM-006, REQ-CSM-008, REQ-CSM-012,
REQ-CSM-017, REQ-CSM-024, REQ-CSM-027.

## Scenario: derive the frozen schema

1. Read the actual `SemanticOwnerRevisionSetV1` and
   `SemanticOwnerRevisionV1` declarations through the bounded, fail-closed
   `declaration_schema_extract` source extractor. No `pub` normalization or
   copied field inventory is used.
2. Verify their seven fields in declaration order: set `schema`, `revisions`;
   then revision `owner`, `owner_instance_digest`, `owner_generation`,
   `revision_digest`, and `authority_serial`.
3. Extract the actual five stable owner variants and verify their tags 1
   through 5: declarations/reexports, trait candidates/coherence, aspect
   candidates/ordering, macro/CTFE lookup, and body dependency closure. The
   frozen variant contract includes each name, payload text, and annotation
   list; all five V1 payloads and annotation lists are empty.

Expected result: the source-derived contract matches the frozen V1 layout.
There is no parallel runtime field/variant inventory that could agree with
itself while drifting from the structs or enum. Adding a field or variant is
therefore an intentional V1 schema change requiring review/versioning.

The focused executable also extracts a synthetic public struct containing a
declaration annotation, a field annotation, `pub val`, `private var`, defaults,
and trailing `@bits`. It verifies that each modifier is retained in the schema
rather than normalized away. The extractor has fixed source, line, member, and
annotation caps. Missing declarations, duplicate fields, dangling annotations,
methods, and unknown modifiers return an error instead of a partial field list.
Tab-indented struct fields and enum variants are also rejected explicitly, so
unsupported leading whitespace cannot masquerade as declaration dedent and
silently truncate the extracted schema.

## Scenario: reject schema drift

The executable mutates the actual declaration source by adding both
`pub extra: i64 = 0` and `var extra: i64 = 0`, and verifies that both legal
forms appear as additional schema fields. Default presence is a separate tag
from default text: an explicit `= none` mutation cannot collide with an absent
default. The executable also removes and reorders fields,
and removes, reorders, and renames owner variants. Separate mutations add an
enum payload and an enum annotation, proving those facts cannot be discarded
by a name-only comparison. Declaration-level visibility and annotations are
also compared for both structs and the enum; private-header and annotated-
header mutations cannot retain the public, annotation-free V1 contract.

Expected result: the declaration-derived drift spec fails. Unknown additions
do not become silently accepted V1 semantics; they require a schema revision.

## Scenario: preserve collision-free scalar identity

The canonical frame prefixes UTF-8 byte length. Delimiter-bearing components
such as `a|b` and `c` cannot alias `a` and `b|c`. Composed and decomposed
Unicode text remains distinct because V1 preserves exact UTF-8 bytes; NFC is
not silently inferred at this identity boundary. `None` is encoded with an
absent tag, while `Some("")` has an explicit present tag and zero-length
frame, so the two are distinct. Signed decimal encoding keeps
`-1` distinct from `1`.

## Scenario: canonicalize maps and ordered sequences

Each map key and value is length-framed before ordering. A bounded, bottom-up,
stable merge sort orders those encoded entries by encoded key; duplicate keys
are rejected only after equal keys become adjacent. The selected entry emits
its already-framed value directly—no dictionary relookup or library sort path
exists. V1 bounds a map to 1024 entries. Reordered maps therefore have the
same canonical representation. Ordered sequences preserve their input order,
so `[a,b]` and `[b,a]` remain different semantic values.

## Scenario: validate and fingerprint the five revisions

The set must contain exactly five revisions in the frozen owner order. The
executable checks the complete set plus explicit missing, reordered, and
negative-generation cases. Each revision requires a valid owner-instance
digest, nonnegative generation, valid revision digest, and positive authority
serial. It then mutates `owner`, `owner_instance_digest`, `owner_generation`,
`revision_digest`, and `authority_serial` one at a time and verifies that each
changes the per-revision canonical identity. That is only serialization
evidence: it does not prove owner liveness, authority, receipt admission, or
tamper detection. Those claims belong to the later owner layer.

## Traceability

| Requirement | Executable spec | Manual | Coverage |
|---|---|---|---|
| REQ-CSM-003/006/008/012/017/024/027 | `semantic_owner_revision_schema_inventory_spec.spl` | This file | Actual modifier-aware schema, field/variant drift mutations, malformed-source refusal, collision framing, map bounds, invalid sets, and every-field identity binding |

## Evidence boundary

The executable spec is source-contract evidence only. No Rust seed result is
used, and no runtime admission claim follows from this inventory. A current
qualified self-hosted runner and Astra semantic/ownership review are required
before any owner implementation or availability change.
