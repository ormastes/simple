# Phase 2 native probe does not produce a runnable executable

Status: OPEN. Source integration and feature qualification remain incomplete.

Compiler: `C:/dev/simple-bootstrap-storage/rel-s2rebuild/frozen/simple.exe`.
SHA-256: `b0e786b3c74c9c2e8bb125967829cdb083d21480c526739d254ff6b5390c566c`.
Its frozen Phase 2 capsule receipt binds the same digest. This is a staged
pure-Simple compiler supporting compile/native-build, not the full CLI.

Release candidate source worktree: `C:/dev/simple-traceability-phase2-release-20261011`,
baseline `f92764f2b97`. A minimal main prints `TRACEABILITY_PHASE2_PROBE_OK`.
The probe tests host build prerequisites only; it is not a traceability acceptance
test and cannot qualify any feature obligation.

Observed diagnostics while establishing the host prerequisites:

- An external temporary source root was refused as unsupported SCV inventory scope.
- The new checkout required explicit SCV cold initialization.
- Native compilation initially failed because llc was absent from PATH.
- A reused native capsule referred to an absent immutable source snapshot.
- With isolated caches and pinned LLVM, native compilation succeeded but linking
  failed. With the frozen runtime provider selected, the diagnostic identified
  missing `src/runtime/runtime.c` in the sparse worktree.
- The runtime subtree was restored and SIMPLE_PROJECT_ROOT bound to this
  checkout. The final attempt still exited 1 with no produced probe executable;
  the retained log ended after HIR worker completion. No inferred link success,
  execution result, compiler crash classification or root cause is claimed.

The pinned LLVM bin is the installed llvm-msvc-23.1.1 toolchain. The Windows
BuildTools vcvars64 environment and frozen runtime provider were explicitly
selected. Cache paths were private to this probe. The original diagnostics and
launcher are retained under the user's temporary `traceability-phase2-probe`
directory. No seed run was substituted. Stop repeated attempts until a fresh
failure diagnosis or corrected admitted compiler changes the relevant inputs.

Close only after a native executable is produced and its actual marker/exit
observed, followed separately by the feature's full required acceptance scope.
