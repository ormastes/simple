<!-- codex-research -->
# Build Intermediate Lifecycle — Domain Research

- Ninja keeps incremental outputs and provides explicit cleaning tools; normal builds avoid broad clean-first behavior because it destroys reuse.
- CMake exposes `cmake --build --clean-first` as an explicit user choice rather than the default.
- Cargo separates final artifacts from internal build artifacts, places them under configurable target/build directories, and provides explicit scoped `cargo clean` and dry-run reporting.
- Clang removes ordinary temporary compiler products but retains internal results only when `-save-temps` is requested; crash diagnostics have a separate explicit directory.

The common policy is to preserve reusable dependency artifacts, automatically remove ephemeral scratch, and make broad cleanup or diagnostic retention explicit. Simple should follow that policy while constraining every managed path to its centralized user/worktree roots.

References: Ninja manual (`ninja-build.org/manual.html`), CMake CLI `--clean-first` (`cmake.org/cmake/help/latest/manual/cmake.1.html`), Cargo build cache and `cargo clean` (`doc.rust-lang.org/cargo/reference/build-cache.html`, `doc.rust-lang.org/cargo/commands/cargo-clean.html`), and Clang `-save-temps` (`clang.llvm.org/docs/CommandGuide/clang.html`).
