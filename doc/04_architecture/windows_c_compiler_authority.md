# Windows C compiler authority

The shell toolchain owner selects and validates the installed C compiler before exporting generic and target-specific CC. The Windows bootstrap environment supplies MSVC headers, libraries, and linker paths, then delegates compiler selection to that owner. CMake validates the same version family at configuration time and configures C only. Cargo keeps its MSVC Rust linker distinct from the C compiler.

The static lint plugin consumes LintUnit path/content through the existing LintRule interface and canonical static rule table. It reports deny findings for Windows compiler selection settings. The lint provider has no environment reads, file access, or subprocesses; the outer lint owner supplies source content. It recognizes an official LLVM 23.1.x Windows MSVC distribution independently of its install root, then requires a root-bound C driver plus a fail-closed version command and exact 23.1.x predicate. Platform selection and compiler assignments are evaluated separately so Linux settings, documentation, and MSVC link.exe remain outside the prohibited C-driver classification.

Executable compiler validation is the runtime authority. The source lint catches configuration regressions; it does not authenticate arbitrary executable bytes or replace the version/hash checks in the Windows workflow.

The separate CI change in PR1216 pins the official LLVM23.1.1 archive, verifies its published SHA-256, and logs hashes of the four LLVM tools. This change does not edit that workflow.
