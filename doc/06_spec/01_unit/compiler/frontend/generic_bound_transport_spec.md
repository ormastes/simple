# Generic bound transport manual

Requirement REQ-GENERIC-BOUND-TRANSPORT: ordinary function trait bounds in existing source syntax survive canonical parsing, flat conversion and HIR lowering with binder identity and structured type arguments.

The ten actual frontend API scenarios cover inline+where conjunction order, structured trait arguments, declaration isolation, hardware-list exclusion, actual HIR trait symbol identity, malformed/undeclared subjects, unknown trait resolution, cold invalid-capture suppression, warm valid restore after pool reuse, and malformed warm restore refusal.

Executable: test/01_unit/compiler/frontend/generic_bound_transport_spec.spl. All ten scenarios UNRUN. Tests were installed before production; RED is source-predicted only.

The separately reviewed parsed_generic_bound_inference_spec.spl is deliberately excluded: active HM inference has not landed on this base. This port does not claim call-site bound enforcement, generic extern binding, parameterized-trait solving, generic defaults or impl transport. Existing extern [] behavior is preserved; ordinary function conversion uses the new shared-name helper locally. Compiler/source identity must invalidate old flat caches that omitted inline rows; no wire schema change is introduced.
