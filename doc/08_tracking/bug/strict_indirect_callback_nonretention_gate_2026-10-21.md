# Strict indirect callbacks without non-retention authority

Status: source control-flow defect confirmed by Astra; repair authored and source-reviewed, execution pending. No acceptance closure or landing.

A strict shared-owner parameter can reach a function-value call without an existing short-loan alias. HIR shared-parameter effect handling does not prove the callback target non-retaining. The MIR borrow adapter previously discarded CallIndirect signatures; unknown-contract checks skipped arguments with no aliases.

The repair rejects strict indirect calls unless a retained source-proven scalar signature, fixed arity and scalar actual operands establish that no reference-bearing inputs/results are being granted. Direct named-call contract handling is preserved. Dynamic Call and CallTerminator also require retained local function signatures; missing metadata rejects. All indirect calls retain the existing alias/NLL event, so scalar ABI casts do not erase borrowed provenance.

Source scalar eligibility precedes ownership erasure: only primitive scalar types and recursively scalar tuple/union/optional/result types retain the new scalar-admissible signature marker. Any, Weak, other ownership wrappers, named/unknown/function/reference types do not. Strict legacy fallback without the HIR source proof is rejected. No callback-reference receipt is fabricated.

The compiler-owned closure environment is explicitly cast to the existing I64 ABI; this cast preserves loan aliases. Its prefix is not exempted from checking. Scalar source regressions require both actual closure/raw CallIndirect branches; reference, unknown signature, weak/Any, and borrowed-to-I64 cases must reject. Tests use driver-admitted HIR and declaration SymbolIds rather than MIR linkage-name guesses.

This closes a rejection-path gap only after execution verifies it. Full AC-BOR-04 fresh reference callback support, actual-target authority and other broad acceptance rows remain open.
