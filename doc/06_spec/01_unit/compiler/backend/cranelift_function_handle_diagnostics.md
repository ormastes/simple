# Retain the first Cranelift function-handle refusal

Authored manual for native Rust bridge regressions; not generated SSpec output.
The three native Rust library tests passed on Linux arm64. The canonical
Simple producer rebuild and original manager diagnosis remain pending.

1. Declare an imported function returning i64, then redeclare the same symbol
   returning f64. Require the actual Cranelift incompatible-signature error
   with the symbol, module and both types. The exported bridge must return zero.
2. Begin a caller and import the original valid declaration. Require a usable
   function reference, proving the failed redeclaration did not erase it.
3. Distinguish an absent declaration from an absent active context. Both refuse
   admission, while a valid declaration remains usable.
4. Distinguish an unknown signature from an unknown module, retaining the
   requested symbol in the diagnostic.

Focused native test filter: `function_handle_diagnostic_tests` in the
`simple-compiler` crate. Passing these regressions proves the diagnostic and
recovery contracts; it does not resolve or qualify the BuildRunner closure.
