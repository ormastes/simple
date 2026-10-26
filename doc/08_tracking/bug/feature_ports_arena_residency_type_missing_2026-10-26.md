# ArenaResidency and *_residency port fields do not exist

- Date: 2026-10-26 | Owner area: src/lib/common/compute/placement_contracts + src/compiler/85.mdsoc/feature/*/app ports | Size: M
- Symptom: test/01_unit/compiler/mdsoc/feature_ports_spec.spl 8/35 fail: `semantic: function \`ArenaResidency\` not found`
  (all "constructs ..." output/result structs, spec lines ~113-409).
- Evidence: `ArenaResidency` is defined nowhere under src/ (handles.spl:3-12 has ObjectRef, EntityRef, ResidentView only);
  spec imports it at feature_ports_spec.spl:25 and builds `token_residency`/`syntax_residency`/`input_residency`/
  `output_residency` fields; no `*_residency` field exists in src/compiler/85.mdsoc (lexer_output_port.spl etc.).
  Other specs reference it too: test/01_unit/lib/gpu/object_vm/gpu_mmu_placement_contracts_spec.spl:5,14,
  test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl, test/01_unit/lib/structural/layout/layout_framework_spec.spl,
  test/01_unit/lib/common/ui/draw_ir_v3_emit_spec.spl.
- Verdict: spec is ahead of the implementation (feature not landed), not a stale spec. Import itself resolves (handles.spl is in the module).
- Repro: `bin/simple.exe test test/01_unit/compiler/mdsoc/feature_ports_spec.spl --no-session-daemon`
- Fix: land ArenaResidency<T>(object, entity_count, byte_len) in handles.spl and the residency fields on the ports, or retire the specs.
