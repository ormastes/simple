# Windows resource watchdog rejects target-prefixed Clang

Status: implemented; focused production-function regression passed. Full compiler and native workload qualification is separate.

The process-tree RSS watchdog accepted `clang` and `clang-cl`, but rejected the genuine LLVM-MinGW executable `x86_64-w64-mingw32-clang.exe` before installing its Windows session helper. That prevented a valid compiler selection from reaching normal resource containment.

Accept only the additional architecture-w64-mingw32-Clang spelling, including the existing optional version and .exe suffixes. Keep the independent Clang identity check, supported Windows target check, mandatory LLD flags and GCC/cl/wrapper rejection unchanged. No resource limit, job/session policy, executable, cache or compiler source is changed.

The permanent regression scripts/resource/windows-clang-flags-test.pl extracts and calls the actual production selector and target functions. Its sole platform substitution supplies the Git shell path; no compiler is launched. Seven accepted spellings each require LLD, eight rejected compiler names remain rejected, and five target/identity checks make27 assertions. The original-source negative control previously failed the four prefixed-Clang acceptance/LLD pairs; that retained evidence is not rerun here. The newly generalized permanent test runs once against the current release-based candidate using its default source lookup.

Retained evidence: build/review/seed-stale-binary/watchdog-prefixed-clang and build/review/watchdog-clang-landing-42f8/evidence. These assertions qualify argument selection and validation. They do not claim a new helper build, compiler workload, native MCP result or full bootstrap admission.
