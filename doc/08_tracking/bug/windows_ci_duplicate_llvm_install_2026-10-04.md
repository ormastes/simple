# Windows CI repeats LLVM installation after successful pinned provisioning

GitHub run 37160571374 on main passed `Install LLVM 23.1.1` and `Verify LLVM
23.1.1 authority`, then failed the later `Install LLVM (MSVC)` step. That
obsolete step asked Chocolatey for unavailable llvm 23.1.1 and exited 1. It
also contained an override redirecting SIMPLE_LLVM_PATH from the verified
archive to Program Files. The missing seed upload was downstream, not a
separate compiler failure.

Remove the duplicate installer and unreachable MinGW host setup left behind
in the MSVC-only job. Existing pinned archive/hash verification and the
explicit LLVM_ROOT clang-cl binding remain the single host authority. The
separate MinGW cross-target relocation linker check is unchanged.

Validation: Windows CI Clang authority check failed before the repair and
passes afterward. Added guards reject duplicate Chocolatey provisioning and
the Program Files runtime override; both negative mutation probes reject
the offending configuration. Working/staged environment ownership guards and
whitespace checks pass. The complete hosted CI build has not been rerun by
this change; no local LLVM installation was modified.
