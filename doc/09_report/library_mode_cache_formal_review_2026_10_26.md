# Explicit library mode: cache model review

Status: INCOMPLETE / NOT_RUN. Reviewed against source base `9ce3db18d9b7c61c80c4aba1447a7969afb0f019`. This does not authorize a source-binding repin or merge.

CI run 40201295765 correctly rejects the changed `compile_options_hash_compute` binding. The implementation appends a length-framed `library-mode-v1` component only for a nonempty explicit semantic mode. Equivalent GC flags or allowed-family lists cannot substitute for that input: explicit mode also controls generic import resolution. The live-key model previously omitted this additional compile-option input.

The schema now adds scalar component `opts_library_mode` at position 48 and increments inputs_total from 47 to 48. Existing positions and known-gap accounting are preserved. Empty mode omits the implementation component and preserves legacy bytes; nonempty modes have distinct framed canonical input, subject to the model's stated digest collision assumption. No source-directory inference is introduced.

Still required: regenerate Generated/LiveKey.lean with the repository's Simple generator; inspect its new field, component accounting and change-visible theorem; run Lean/formal checks and configured/legacy hash regression cases; then repin the reviewed declaration with the source-binding tool and run the failing gate. Generated files and source_bindings.txt are deliberately unchanged until these steps can be performed. No verified compiler is currently admitted for the generator; no Rust-seed fallback is used. The schema change is preparatory and does not make the current model or CI passing.
