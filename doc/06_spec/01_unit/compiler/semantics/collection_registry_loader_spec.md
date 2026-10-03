# Collection operation registry loader

Status: AUTHORED, UNEXECUTED. Tests precede implementation; no runtime RED/GREEN
or production admission is claimed. Fixture receipts are deliberately synthetic.

The executable specification is
`test/01_unit/compiler/semantics/collection_registry_loader_spec.spl`.

Acceptance covers strict SDN/schema/field validation, duplicate keys/rows and
backend names, typed counts and consistent allocation facts, expected/worst
cost projection, empty pending-admission defaults, and subset binding.

Bindings require explicit resolved symbol IDs and exact receiver, signature,
backend, receipt, metadata version and source digest. Unknown operations,
negative IDs, duplicate bindings, forged cached rows and mutated source are
rejected. Bare method spelling never supplies symbol or signature evidence.

`module_path` is required: the single-registry API rejects mixed owners; the
batch API `collection_registry_bind_modules` validates captured source once
and returns separate registries keyed by owner path. Equal numeric symbol IDs
in different modules never share one registry. The driver must verify the path,
actual declared signature/receiver, and current backend before consuming it.

Parser limits are 65,536 source bytes and 256 operation rows; admission accepts
at most 4,096 bindings. Closed enums reject unsupported receivers, operations,
costs, allocations, backend names and key contracts. Worst cost cannot be an
amortized/expected claim or less than expected work. Keyed operations require
a key contract; non-keyed operations require `not-keyed`. Legacy summary fields
default to unknown/empty when their callers provide no admitted metadata.

The checked-in `config/compiler/collection_operations.sdn` contains no operation
rows. Comparing receipt strings checks consistency, not cryptographic identity
or evidence certification; those remain owned by the caller's admission boundary.

This unit slice supports REQ-003. Production pipeline ownership, evidence
authentication, cross-engine operation certification, and runtime checks remain
separate requirements; an empty default registry is not completion evidence.
