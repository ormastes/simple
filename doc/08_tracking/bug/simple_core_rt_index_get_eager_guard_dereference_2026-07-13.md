# Simple-core `rt_index_get` eagerly dereferences an invalid collection

## Symptom

After the optimizer tuple-state fix, filesystem `emit-llvm` reaches HIR and MIR and then faults in `rt_index_get` at target address `0x10392869`, with `CR2=0x0` and page-fault error `0x5`.

## Root cause

The Simple-core string guard is written as one compound condition:

`collection >= 4096 and (collection & 7) == 1 and spl_load_i64(collection & -8, 0) ...`

Target disassembly shows the header load executes unconditionally before the combined boolean is tested. For a nil or otherwise small collection, the masked pointer is zero and the load faults. The hosted C owner is already safe because `rt_core_as_array` and `rt_core_as_string` validate before dereference.

This is the same confirmed native lowering defect where `and`/`or` operands are evaluated eagerly instead of through short-circuit control flow.

## Fix and evidence

The unsafe string fast path was redundant and has been deleted. The remaining path checks dictionaries, validates the numeric index, calls guarded `array_is_valid`, and finally uses `rt_string_char_at`, whose `string_ptr` rejects wrong tags and zero before its header load. This reuses the existing owner instead of duplicating nested validation.

Runtime archive and sysroot SHA-256 are both `eff65d42dec1ce2824494d657ce00b784cc7a76460226c3ea718b7c8b5de5ab5`. Target disassembly contains no old `0x53545231` fast-path compare; every remaining header read is branch-dominated. Live execution passed the former `rt_index_get` PC and reached the separately tracked optimizer `local_count_index` failure.

The broader native eager-`and`/`or` source defect is now fixed at the shared MIR
binary-expression owner with branch-and-join lowering. The RHS is isolated in a
conditional block and boolean results merge as i64 for LLVM/Cranelift parity.
The fixed-lifetime merge slot is emitted in function entry so a loop does not
allocate it on every iteration. The textual-LLVM SSA repair accepts those MIR
`Alloc`/`Store` instructions, rewrites both store operands, and renames a
cross-block allocation destination before spilling it. Focused MIR CFG, combined
SSA/loop, and dual-backend parity regressions are present; executable proof
remains pending a known-good pure-Simple native test CLI.
