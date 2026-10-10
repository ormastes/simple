# Native text.ord contract

All cases UNEXECUTED. `positive` checks ASCII, Unicode scalar (not UTF-8 byte), empty zero, first scalar of multichar strings, non-BMP Unicode, allocated concatenation text, unchanged foreach text loop, and declared custom ord precedence. Expected stdout is pinned in manifest.json. `wrong_arity` and `nontext` must reject without object emission; preserve real diagnostic and phase, never count an unrelated parse failure as contract success. Run only after the new producer's actual Hello PASS, with immutable source/producer/runtime pins and private caches.

Contract authority: owned Rust interpreter_method/string.rs474–480 and codegen/llvm/functions.rs2925–2940 at fd6e9cb61, read-only. No seed execution. Both specify first Unicode scalar, empty0; existing rt_string_char_code_at(receiver,0) implements it. Structural text_ord_lowering_spec remains UNEXECUTED until a supported runtime exists.
