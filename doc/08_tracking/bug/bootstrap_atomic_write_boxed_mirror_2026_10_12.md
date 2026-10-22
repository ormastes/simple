# Bootstrap mirror omits atomic tagged-text arguments

Status: OPEN; helper correction qualified, whole backend/runtime roundtrip pending.

Exact release_phase3 020e419f Rust boxed_text_arg_indices only contains string_builder_push. Both Cranelift calls and LLVM delegate to this registry. Rust rt_file_atomic_write consumes RuntimeValue path/content; C rt_file_atomic_write and its mode variant likewise require tagged text. Missing entries permit generic raw pointer lowering, matching the actual P2 atomic snapshot failure debugger evidence.

Add both names at indices [0,1]; scalar mode index2 and foreign providers remain unchanged. The extracted exact changed source helper plus authored unit test passes seven assertions (one Rust test). The same test against the actual prior helper fails exit101; corrected test exits0. Evidence /mnt/c/Temp/simple-bootstrap-atomic-mirror-20261012/receipt.json. This is bootstrap-only source qualification, not production Rust CLI fallback, full Cargo test, complete backend qualification, or native atomic roundtrip PASS.
