# Verbatim struct word stores omit integer SSA width conversion

Bug: BUG-LLVM-STRUCT-WORD-STORE-WIDTH-20261017. Database reconciliation pending.

Introduced by c9a3c966172f921d4dbbc8f0958f68bc432379d5 in store_field_bits_verbatim. The new integer arm returns the original operand for every integer width. The Struct caller emits_store uses native_int(), which is i64 on 64-bit targets and i32 on 32-bit targets. translate_operand(Copy/Move) returns the existing SSA name, and get_operand_type returns that local's declared LLVM type. The mapper preserves I8/I16/I32 widths. Therefore a genuine i32 SSA argument is stored as `store i64 %input` even though its definition is i32. LLVM rejects this. Context-polymorphic integer literal tokens alone do not prove the defect; narrow SSA operands do.

Source witness at exact c9a3:

- aggregate_intrinsics.spl:174-184 selects native word, invokes verbatim helper, then emits native-word store.
- aggregate_intrinsics.spl:373-391 returns all i8/i16/i32/i64 operands unchanged; is_integer_type does not include i1.
- core_codegen.spl:2721-2730 translates Copy/Move through local_value_text; 2949-2961 obtains declared local type.
- llvm_ir_builder.spl:268-271 emits the supplied store type with no conversion; 685-689 classifies only i8/i16/i32/i64 as integer.
- llvm_type_mapper.spl:113 and adjacent cases preserve narrow integer widths; Bool maps i1 and is outside the new integer arm.
- aggregate_intrinsics.spl:304-321 already loads one native word and truncates to narrow field width, confirming physical storage contract.

The repair retains raw values only when operand width equals native word width. Other integer widths use existing emit_value_type_conversion directly, avoiding the sticky value_types map that value_as_type and value_as_type_signed consult. That helper does not read the map. Its pure select_cast_instruction chooses signed extension for i8/i16/i32 widening and truncation for wider sources. This preserves the old store_field_bits extension convention, including signed negative values, rather than introducing an unsigned storage-policy change. Readback truncation retains unsigned low bits too. Pointer, float and bool branches are unchanged. The independent sticky metadata owner problem is not claimed fixed.

Focused LLVM 23 assembler controls: four hand-authored raw SSA stores were rejected with actual type-mismatch errors (i8/i16/i32 to i64, i64 to i32); their four explicitly converted counterparts, two equal-width stores and a signed-negative sext store were accepted. Receipt: external aggregate-word-store-c9a3-review/llvm-controls-receipt.json. This checks LLVM grammar/type contracts, not compiled execution of the Simple helper. Signed-negative runtime semantics were not executed; sext preserves -1 by LLVM's instruction semantics. An initial PowerShell wrapper stopped on expected native stderr; retained script then handled expected rejection normally.

A real Simple unit spec exercises the actual helper with stale pointer metadata, narrow integer widths, native32 truncation, equal width, signed-negative constants and the unchanged pointer branch. These controls and required compiler/core/MCP checks remain UNRUN. No complete aggregate consumer, Phase3 build, or release admission is claimed. The fix must remain draft until required gates qualify.
