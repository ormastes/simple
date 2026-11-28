# Requirements: generic substitution model

Owner: compiler types. Plan row: `doc/03_plan/language/type_system/no_any_inference_plan.md` S3-F0.
Implementation: `src/compiler/30.types/generic_subst/`.

- **REQ-GSUBST-001:** Substituting type arguments into a type is idempotent for a closed range, composes, keeps closedness and leaves unknown and unbound variables unchanged.
- **REQ-GSUBST-002:** One-way matching and call-site inference bind exactly the evidenced variables, report conflict or shape mismatch, and never default a variable without evidence.
- **REQ-GSUBST-003:** The specialization key is a deterministic, injective, byte-framed encoding that decodes back to the same type and equals the template projector's key text.
- **REQ-GSUBST-004:** Every variable-change kind (binding, assignment, argument, return, field, element, entry, optional, closure, pattern, loop) commutes with substitution, preserves closedness and invents no variable.
- **REQ-GSUBST-005:** Types, substitutions, matches and inference results render readably and independently of insertion order, for diagnostics only; identity always uses the key encoding.
