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

This unit slice supports REQ-003. Production pipeline ownership, evidence
authentication, cross-engine operation certification, and runtime checks remain
separate requirements; an empty default registry is not completion evidence.
