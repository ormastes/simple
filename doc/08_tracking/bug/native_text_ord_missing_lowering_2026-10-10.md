# Native MIR lacks text.ord lowering

Observed with pure producer 6d0b845e6e67e070f7872d8485284a247ecf27b8f4ddad168a1db7ef08fedb6b: real 51-module HirSymbol closure passes HIR but reports unresolved ord at parser_types_utils.spl72:24 (and two other sites). Complete MIR family receipt: /mnt/c/Temp/simple-if-val-payload-owner-evidence-20261010/focused-validation/review.json. Ord is only one of 49 normalized diagnostics; no claim this repairs the closure.

MIR text foreach already yields codepoint-sized text via rt_string_chars and Opaque(str), mir_lowering_stmts3532–3549. Missing dispatch is independently visible: owned Simple compiler contains no ord builtin route. Existing owned Rust interpreter string.rs474–480 specifies first Unicode scalar/empty0; LLVM functions.rs2925–2940 maps it to rt_string_char_code_at(index0). This analysis does not execute the Rust seed.

Proposed change extends existing guarded char_code_at lowering only for zero-argument ord on proven text, after declared custom-owner dispatch. It does not change foreach, runtime ABI, nontext receivers, or unsupported arities. Tests include ASCII/Unicode/empty/multichar/non-BMP/custom and rejection cases. Every new native/spec criterion remains UNEXECUTED. Latest integration base fd6e9cb61; production change is isolated to method_calls_literals.spl.
