# Producer-qualified MSVC LLVM dependency

**TEST_BLOCKED — authored manual; Simple execution and docgen pending.**

Executable: `test/01_unit/compiler/linker/windows_native_all_llvm_dependency_spec.spl`.
Requirement: `REQ-WINDOWS-NATIVE-ALL-LLVM-DEPENDENCY`.

Five scenarios exercise the production pure selector. They model admitted-file
presence as an input fact; they do not simulate successful native linking or
prove LLVM ABI compatibility.

| Scenario | Required assertion | Evidence |
|---|---|---|
| Producer archive pair | Exact authority-root LLVM-C.lib follows backfill/native-all | TEST_BLOCKED |
| Existing exact dependency | Import library appears once, after preserved archive order | TEST_BLOCKED |
| Aggregate absent | Core-only or unrelated target inputs remain unchanged | TEST_BLOCKED |
| Combined input sources | Configured foreign/bare LLVM libraries cannot suppress the qualified library when native-all arrives through objects or selected runtime | TEST_BLOCKED |
| Refusal contracts | Missing bytes, wrong target, relative/traversing roots, foreign aggregate/import library fail | TEST_BLOCKED |

Both internal COFF and external MSVC link paths call the same dependency
selector. Managed preflight validates the library against the existing sealed
runtime snapshot. Independently, the bootstrap shell custody test verifies
actual copy/hash behavior; fixture byte custody is not LLVM semantics evidence.
Actual qualified compiler Hello compile/run, linked DLL identity and native
Phase2/Phase3 products remain required before admission.
