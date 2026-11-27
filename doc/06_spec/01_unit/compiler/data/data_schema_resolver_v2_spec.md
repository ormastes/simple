# Shared SPL and SDN data schema resolver V2

Source: `test/01_unit/compiler/data/data_schema_resolver_v2_spec.spl`.
Requirements: REQ-001 and structural portion of REQ-013.
Status: manually authored companion; examples UNEXECUTED. No SPipe/docgen or
`sspec-maintain` result is claimed; those require an admitted runtime.

## Declare explicit views and property contracts

Declare typed views independently of fields, including a fieldless view.
Describe each property's stored/computed/forwarded behavior, explicit access
owners, phase, effects and dependencies. Resolve the complete input under the
tree's explicit authority. Missing views and unauthorized owners must fail.

## Resolve equivalent SPL and SDN inputs

Construct a declaration in SPL and normalize the equivalent dedicated V2 SDN
input. Both enter the same resolver. Their outer digests and exact canonical
types must agree; each origin and source location remains available. Matching
dual declarations retain both provenances without changing semantic identity.

## Reject incompatible logical contracts

Reject exact nominal type conflicts, per-view property disagreements, missing
access authorities, malformed stored/computed contracts, invalid forwarding and
missing/nonapplicable dependencies. Self, indirect and forwarding cycles fail.
Unknown SDN keys, duplicate keys, wrong scalar/list/mapping types and unsupported
versions must produce diagnostics rather than partial usable schemas.

## Verify canonical identities

The V1 projection remains unchanged for legacy consumers. The V2 digest also
identifies explicit views, access owners, kinds, accessor symbols, phase, effects
and dependencies. Declaration order and repeated equivalent declarations do not
change it. A fieldless view or restriction-owner change does. Reject malformed
flat nominal names instead of allowing delimiter-based type collisions.

These examples validate structural values only. They do not demonstrate source
annotation parsing, body/type binding, generated field access, purity, lifecycle
enforcement, storage conversion or runtime observation.
