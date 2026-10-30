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

## Resolution (2026-10-27) - NOT FIXED; history found, left filed
- History: ArenaResidency<T>(object: ObjectRef<T>, entity_count: u64, byte_len: u64) DID exist, in handles.spl plus
  `*_residency: ArenaResidency<AnyObject>` fields on the mdsoc ports (parser_input/output, linker_input/output), at
  e274cd33719 (2026-09 "merge all share-history worktree branches"). It was dropped by fcbec1c3b62
  "fix(merge): restore src/compiler and src/lib to origin for phase 1 bootstrap" (an ancestor of HEAD), which reverted
  handles.spl, semantic.spl (AnyObject), backend/planner and the ports. So the specs are not ahead of a never-landed
  design; the feature landed and was deliberately reverted for bootstrap. Related gpu symbols (hash128, GpuCasStore,
  DescriptorTable, placement_object_state) went the same way (see gpu_lib_removed_apis_specs_red_2026-09-16.md).
- Not restored: it is a multi-file revert (handles, semantic AnyObject, 4+ ports, EntityRef relocation to
  common.structural.identity.entity_id) well over the minimal size, and it undoes a bootstrap-motivated revert.
  Owner decision needed: re-land from e274cd33719 (`git show e274cd33719:<path>`) once the phase-1 bootstrap reason is
  cleared, or retire the 5 specs.
