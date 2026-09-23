# Windows C authority local research

The shared LLVM environment previously exported clang.exe and clang++.exe for Windows and could fall back to LLVM18. The Windows bootstrap environment separately pinned LLVM18. The Windows CMake toolchain configured C and C++ explicitly. Cargo lacked an explicit MSVC linker setting and included a Windows GNU/GCC override.

Canonical source lint providers are StaticLintRule entries in src/compiler/90.tools/lint/static_rules.spl. LintUnit carries source path/content; non-Simple source reaches the static table before the Simple parser-specific extension check. This existing seam can enforce build-file policy without introducing a separate linter or runtime bypass.

The original candidate's reported SSpec green used the Rust seed, and its earlier red was an oracle-construction error. Both were rejected as admission evidence. The replacement shell red executes the same current contract against actual prior Git source. Real LLVM23.1.1 native probes are retained separately from selection fixtures.
