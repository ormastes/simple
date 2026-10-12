# Generic annotation preservation

User scope: finish generic implementation and verification as part of the robust
release bootstrap. This repair addresses H-ANNOT in the generic instantiation
model; it does not claim to discharge the other holes in that document.

| Requirement | Acceptance evidence |
|---|---|
| REQ-GENERIC-ANNOTATION-PRESERVE | The flat parser retains the nominal base and ordered arguments of local and forward generic annotations, including nested instances. `local_generic_annotation_spec.spl`. |
| REQ-GENERIC-ANNOTATION-OWNER | Inference compares nominal declaration ownership, not module-local ids. Imports of one declaration match even with different ids; different declarations fail even with colliding ids. The rule applies recursively under containers. `generic_annotation_owner_binding_spec.spl`. |
| REQ-GENERIC-ANNOTATION-FIELD | Text operations through generic parameter, result, local and struct-field annotations generate text concatenation; integer instances generate integer arithmetic. `generic_struct_composite_field_spec.spl` and `generic_struct_field_instance_paths_spec.spl`. |
| REQ-GENERIC-ANNOTATION-DIAGNOSTIC | Invalid type arguments of a locally resolved declaration retain the HIR diagnostic instead of recovering to `Any`. |

Qualification requires the specs on an admitted self-hosted runtime and native
execution of both text and integer cases after a successor includes the repair.
Seed-interpreter results or LLVM-text assertions alone do not establish native
behavior. Fresh producer-bound caches must be used for candidate verification.

Formal scope is separate: a substitution model proof does not establish parser,
HIR transport, module ownership, MIR lowering, or native ABI refinement.
