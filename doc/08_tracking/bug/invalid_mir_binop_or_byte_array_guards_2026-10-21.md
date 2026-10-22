# Invalid MIR Or variant in byte-array guards

Status: source fixed; bounded native object qualification pending.

The checked byte-array copy guards in switch_operators_calls.spl used MirBinOp.Or twice for boolean empty-count/non-null-pointer predicates. The actual MirBinOp declaration in mir_instruction_support.spl defines BitOr, with no Or variant. The admitted r17 field fallback therefore reports undefined variable MirBinOp rather than a precise missing-variant diagnostic. Explicit owner imports do not repair an invalid variant.

Both predicates now use MirBinOp.BitOr with the same boolean operands and result type. This preserves inclusive boolean OR, pointer/count validation, allocation ownership and all fail-closed branches. No new opcode, ABI provider, or type-check relaxation is introduced.

Evidence: manual module attempts7/8/9 retain the unresolved-MirBinOp failure; constructor traces localized and subsequent attempt8 eliminated all payload failures. Existing exact declaration enumeration showed only these two invalid MirBinOp namespace references across owned compiler source. Actual source-to-MIR byte-array copy controls and backend behavior still require executable verification with a qualified new compiler. No acceptance criterion is closed by this source fix alone.
