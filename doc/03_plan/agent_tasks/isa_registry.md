# ISA registry ownership

Base a9cf82179cd3f0212a46b39d63032a788d8196b8; isolated work/isa-registry-tdd-20261021 lane.

- Architecture, detail design, acceptance/manual: astra_isa_registry_design_tests.
- Source implementation: implement_isa_registry_tdd; model/parser/generator only, plus agreed implementation documentation/schema.
- Build/runtime qualification and CPU-heavy execution: phase3_build_recovery exclusively.
- Merge owner and final integration reviewer: root; independent normal/highest-capability review required before admission.
- Lower-model sidecars: N/A. No delegated code generation.

Interfaces, manual steps, fixtures and real failure checkers are frozen in doc/05_design/isa_registry.md before tests. No placeholder helper returns acceptance. Tests intentionally import not-yet-implemented APIs; status UNRUN, not an observed RED. Official authority integration remains pending user selection, without reducing full D0 acceptance.
