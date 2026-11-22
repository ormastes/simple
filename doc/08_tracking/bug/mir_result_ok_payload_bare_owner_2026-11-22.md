# MIR records bare struct owner names for Ok/Optional/unwrap/method results

- **id:** mir_result_ok_payload_bare_owner_2026-11-22
- **status:** fix committed (branch work/mir-ambiguous-owner), not yet executed on a rebuilt Stage 2
- **layer:** src/compiler/50.mir

## Symptom

Full-CLI native-build p4-cli-f23 (Stage 2 from pinned 8d850c2, 2026-11-21) failed MIR
lowering in ~15 modules with:

```
MIR lowering error: field 'is_dir' on ambiguous struct/class owner 'DirEntry': no exact layout
```

Same shape for `FileStat.size`, `FileHandle.id`, `TaskContext.rip/rsp/rax/rflags`,
`Fat32Bpb.bytes_per_sector` (fs_driver fat32/ramfs/mount_table, kernel user_entry*,
scheduler, loader managed_image_authority_v1).

## Root cause

When two modules in one build declare a struct with the same short name, the field
reader (`_MirLowering/function_lowering.spl` ~2429) correctly refuses the short name.
Upstream writers recorded a value's struct type by short name instead of the
declaring-module layout key:

- A. Ok/Optional return-type pre-scan tables (`module_lowering.spl` ~2329,
  `declaration_providers_v1.spl` ~615/645); the two pre-scans also disagreed for
  Optional, so the entry was dropped as ambiguous.
- B. `match local: Ok(v)` binding (`switch_operators_calls.spl` ~5192, fallback ~1705).
- C. `opt.unwrap()` copied the receiver's short name before the declared payload
  (`method_calls_literals.spl` ~1634).
- D. own-module struct-returning methods (`module_lowering.spl` ~3743).

## Fix

Record the declaring-module layout key (`record_shape_layout_key`), falling back to the
previous short name when no exact layout exists (never another declaration's layout).

## Evidence

- Five-module repro reproduces all four shapes on the 8d850c2 Stage 2 binary.
- Spec: `test/01_unit/compiler/50.mir/stage2_ambiguous_struct_leaf_owner_spec.spl`
  (decoy module with the same names in a different field order). Not executed: no
  full-CLI test binary on the host.
- Remaining check: rebuild Stage 2 with the fix and re-run the full-CLI native build.
