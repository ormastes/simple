# Windows C compiler authority

These requirements were selected by the user's explicit Windows compiler policy.

- WINCC-001: Windows C compilation uses LLVM 23.1.x clang or clang-cl; the default authority is C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe. The same validated official distribution may live at another root, including a CI workspace root.
- WINCC-002: Windows settings reject cl, GCC/G++, MinGW, clang++, and C++ compiler selections. Windows GNU is not an admitted ABI. Non-Windows compiler settings retain their platform policy.
- WINCC-003: Cargo's Windows MSVC target may use link.exe as the Rust linker. The linker must never be accepted as the C compiler.
- WINCC-004: The canonical lint registry contains an executable deny rule for Windows compiler selections, with focused SSpec coverage. Acceptance requires an official LLVM 23.1.x distribution marker, a root-bound C driver, and a fail-closed exact version-family predicate bound to the queried compiler output; a bare `--version` token or unrelated matching text is insufficient. Generic and target-specific CC/CXX assignments use the same deny policy. A missing admitted self-hosted runner is reported as pending, never replaced with Rust-seed evidence.
- WINCC-005: Shell selection fails closed for a missing compiler, a failed version query, or a non-23.1 version. The Windows bootstrap environment removes stale LLVM_SYS_180_PREFIX and delegates C authority to this selection.
- WINCC-006: Verification retains a real failing prior-source shell case, passing candidate shell cases, C-only native/CMake execution using LLVM23.1.1, Cargo MSVC linking, and paired time/memory evidence on the same C workload.

The current bootstrap backend is Cranelift. Changing Rust llvm-sys feature pins or admitting an LLVM compiler backend is outside this change and remains a separate migration blocker.
