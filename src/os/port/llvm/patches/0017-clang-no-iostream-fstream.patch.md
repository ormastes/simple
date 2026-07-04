# Clang no-iostream/fstream SimpleOS patch

SimpleOS builds libc++ with `_LIBCPP_HAS_LOCALIZATION=0`, so Clang code built
for `*-unknown-simpleos` must avoid standard iostream, fstream, stringstream,
locale-backed formatting, and related runtime pulls on the target side.

This patch replaces the remaining target-side Clang uses with LLVM Support
facilities:

- `clang/lib/CrossTU/CrossTranslationUnit.cpp`: replace `std::ifstream` and
  `std::ostringstream` with `llvm::MemoryBuffer` and `llvm::raw_string_ostream`.
- `clang/lib/Analysis/IssueHash.cpp`: replace `std::ostringstream` with
  `llvm::raw_string_ostream`.
- `clang/include/clang/Analysis/Analyses/ThreadSafetyCommon.h` and
  `ThreadSafetyTraverse.h`: replace ostream/stringstream dependencies with
  `llvm::raw_ostream` and `llvm::raw_string_ostream`.
- `clang/lib/Analysis/UnsafeBufferUsage.cpp`: replace local
  `std::stringstream` formatting with `llvm::raw_string_ostream`.
- `clang/lib/Driver/ToolChains/BareMetal.cpp`: replace multilib diagnostic
  `std::stringstream` formatting with `llvm::raw_string_ostream`.
- `clang/lib/Frontend/LayoutOverrideSource.cpp`: replace `std::ifstream`
  layout loading with `llvm::MemoryBuffer`.
- `clang/lib/Frontend/CompilerInvocation.cpp`: replace
  `-frandomize-layout-seed-file` `std::ifstream` loading with
  `llvm::MemoryBuffer`.

The behavior stays equivalent for successful reads and diagnostics while
removing target libc++ iostream/fstream dependencies from the SimpleOS Clang
artifact.
