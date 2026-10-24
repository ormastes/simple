# Windows LLVM-MinGW link explicitly requests unavailable GCC runtimes

Status: the repaired compiler produced and ran a real core-C Hello. The
24-case/145-assertion standalone regression remains **UNEXECUTED** because its
compile stopped at an independent MIR imported-provider ambiguity. Unit specs,
shared-library execution and broad compiler/core checks are not claimed PASS.
No Rust seed rebuild was used for this repair.

The retained candidate SHA256
`a722b2f67bd1f3b909fbe7b0a0d490a3aa7b143211fde2e7b7972d9c3caf9fd9`
completed source capture, parse, HIR, MIR and object generation, then its real
Hello build exited 1 at the Windows GNU executable link. LLVM-MinGW 23's actual
Clang invocation contained explicit `-lgcc_eh` and `-lgcc`; LLD could not find
those libraries. The selected LLVM-MinGW toolchain supplies compiler-rt and
libunwind. This is a driver-runtime selection defect, not proof of a runtime
provider failure. Hello was not run; the candidate still has 97 generated stubs
and is not admitted by this diagnosis.

Original evidence is retained unchanged under
`C:/dev/simple-gnu-secure-temp-hello-cc-20261024`: `evidence/hello-failure.sdn`,
`compile/compile.combined-stdout-stderr.log` and the generated command under
`output/*.link-command.txt`. Exact command SHA256:
`e29fca7d4fd12775a599844089d88be1bc93853a00dc771da63d314573f57e30`.
The compile owner requested 24 jobs, native/raw exit 1, quiescent 1; peak RSS
241,804 KiB. No codec retry or dependent phase is authorized by this failure.

The actual `_link_native_mingw` and `_link_shared_mingw` owners accept only a
Clang CC. Both now call `native_mingw_clang_link_args`, which selects
`--rtlib=compiler-rt` and `--unwindlib=libunwind`, preserving all existing
Windows aggregate support except the exact GCC-runtime inputs. The generic
GNU support function remains unchanged, including its GCC dependencies. The
managed caller's exact linker authority is preserved; no later `-fuse-ld`
override is introduced. Rust's existing native link owner already selects the
same two LLVM runtime flags. Extra driver flags cannot remove explicit library
inputs, so adding those flags alone to the old command would not repair it.

The unit spec extends the existing Windows aggregate SDK tests. Standalone
`test/fixtures/bootstrap/windows_mingw_runtime_flags/main.spl` calls the real
production helper for 24 archive/nonarchive/path cases and 145 assertions. It
checks LLVM selection, absent GCC libraries, retained Windows support, generic
GCC preservation and core-only behavior; no mocked flag oracle is used.

Actual validation, with 24 requested jobs and the unchanged 5,859,375 KiB guard:

- `C:/dev/simple-gnu-linkfix-relink-storage-20261025/attempt1` records native/raw
  exit 0, quiescent 1, four compiled units and 1,484 genuine normal-cache hits.
  The unchanged seed and corrected runtime were reused; total time was 52.4s.
  Candidate SHA256 is
  `2cc51dc392b19a3f2fceffcac2d42d0b54fd32caf87eea7c69302656633ac7a7`.
- The actual default Hello command under
  `C:/dev/simple-gnu-linkfix-hello-20261025/output` has SHA256
  `9d4f24cb3c0d27b7c49f797ef4a3ea8b43b8eb2b69bf3b6530bbedf55c05c85c`.
  It selects compiler-rt/libunwind and no longer requests `-lgcc` or `-lgcc_eh`.
  That link then fails on distinct duplicate C providers; this is not a default
  native-all Hello PASS.
- `C:/dev/simple-gnu-linkfix-corec-hello-20261025` records real public
  `--runtime-bundle core-c-bootstrap` compile/run exit 0, quiescence, no cleanup
  remnants and exact combined output `warm-candidate-hello\n` (21 bytes).
  Program SHA256 is
  `4c8ef125cbb06d7d4449c108ac554cf10f61aa72392a9e1b6594f97800c78ffa`.
  This qualifies the standalone C target profile, not native-all targets or
  Rust/Cranelift descendants. The compiler binary retains its existing DC022
  runtime lineage and 97 generated unresolved stubs; formal admission is none.
- `C:/dev/simple-llvm-flags-corec-fixture-storage-20261025/compile/compile.log`
  records the attempted standalone regression: HIR 63, then 22 successful and
  103 failed MIR units due to ambiguous imported extern-provider ownership.
  Native/raw exit is 1, quiescent 1, cleanup not needed, no job remnants; peak
  RSS is 3,917,484 KiB. None of the 145 assertions ran. The unchanged failing
  fixture was not retried or replaced by a passing surrogate.

Full regression execution still requires resolving that independent MIR
boundary. POSIX, generic GCC and shared-library runtime qualification remain
unverified by this repair. No broad compiler/bootstrap readiness is asserted.
