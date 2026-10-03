# Native assert call resolves to incompatible libc __assert

Phase 2 producer `8f817f2b6d5430ab6a18f36e8c9e136857783341adfea8741acfe7a5aea552d4`, source `fcb35f85cdcc27f606b149274fb6f3432b50d24f`, successfully compiles and links `class_optional_metadata_native.spl`, then the executable exits 139.

The retained GDB backtrace shows `__simple_main -> __assert -> libc` with an invalid pointer. Disassembly shows `counter.read()` returning 37, a comparison against 37, and the boolean result passed as the sole argument to `__assert@plt`. The call is unconditional. libc's `__assert` takes assertion text, filename, and line number; the generated single-boolean call is ABI-incompatible and crashes even for a passing condition.

The failing assert fixture remains unchanged as a regression. A separate `class_optional_metadata_control_native.spl` checks the same values using explicit mismatch output and early returns. Its runner must require exactly `class-optional-metadata-ok`; a mismatch is a failed test, not a placeholder pass. This control isolates the class metadata repair from the separately unresolved assertion bug.

Evidence is retained under the pinned source's `build/native_probe/class-fix-validation/class-run-debug/gdb.log` and `class-check` binary. GDB exit zero is not an inferior execution PASS. No assertion lowering fix is claimed by the control fixture.
