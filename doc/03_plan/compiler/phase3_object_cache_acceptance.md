# Phase 3 ordinary object cache acceptance

Scope: retain compact source/dependency/resolution facts before graph reclamation, and combine them with actual current MIR, layouts and configuration in the existing native capsule witness. All sources are still parsed and checked.

Authored verification: native_module_complete_witness_wiring_spec.spl and native_retained_input_facts_spec.spl exercise actual positive and negative witness/fact behavior. object_reuse_driver_spec.spl contains 16 native candidate scenarios with isolated frontend/HIR/native reference caches and real executable comparison. Runtime verification is UNRUN pending the root-owned producer. Apply-check is only patch compatibility evidence.

All 12 performance/memory feature groups remain pending full acceptance. Header/body omission, SCV/managed async service, parallel dispatch, split entry output, archive lease emission/full MIR decoding and NFR measurement receipts are excluded from this narrow candidate. Existing plain cache tests do not qualify those features.
