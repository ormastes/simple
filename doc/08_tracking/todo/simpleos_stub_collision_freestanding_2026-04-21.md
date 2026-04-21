# SimpleOS Freestanding-Stub Symbol-Weakness Collision (2026-04-21)

## Scope

Compiler-level bug in the native-build freestanding (baremetal) toolchain.
This is a compiler issue, not an OS source issue. It blocks live QEMU
re-verification of FR-SOS-024 Phase 3 against HEAD.

## Symptom

When building a baremetal OS image with the Simple native-build pipeline,
symbols defined in the Simple source tree (e.g. syscall shim handlers, OS
dispatch functions) are silently shadowed by weak stub symbols emitted from
`baremetal_stubs.c`. The result: syscall dispatch routes to the weak
`-ENOSYS` stub instead of the real handler, causing the OS to behave as if
the syscall is unimplemented even though the correct Simple source is compiled
and linked.

Observed manifestation: in the FR-SOS-024 Phase 3 live run, the syscall 14
(EnterUserBlocking) handler was reachable in the pre-blocker run but
subsequent builds (mid-session) reverted to stub-collision behavior. Syscall
dispatch markers stopped appearing in the serial log even though no OS source
changed.

## Isolation

- The OS source code (Simple `.spl` files) is correct. The pre-blocker live
  run at commit `a3f4f666` produced the expected end-to-end markers without
  the collision.
- The collision is a linker symbol-priority issue in how the Simple
  native-build pipeline resolves weak vs. strong symbols when linking
  freestanding archives alongside user object files. Likely root: strong
  symbols from user objects are emitted *before* the weak stubs but the
  linker sees both at archive-extraction time and picks the wrong one.
- The fix location is identified as
  `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs`.

## Fix Shape

The native-build pipeline must ensure that weak stub symbols in
`baremetal_stubs.c` are never resolved in preference to strong symbols
defined in compiled Simple modules. Options:

- Emit strong aliases (not `__attribute__((weak))`) from the pipeline for
  symbols that are defined in the Simple source graph.
- Or: link the Simple-compiled archive *after* the C stub object file so the
  strong definition wins at link time.
- Or: strip the weak stub for any symbol that appears in the import map.

The parallel Codex compiler agent owns this fix. No OS source changes are
needed once the compiler toolchain is corrected.

## Impact

- FR-SOS-024 live re-verification is blocked until the fix lands. The OS-side
  implementation is complete (see
  `doc/08_tracking/feature_request/simpleos_os_requests.md` FR-SOS-024 Notes
  for the pre-blocker evidence).
- Other freestanding build lanes (arm32, arm64, riscv64) may be affected if
  they share the same stubs pipeline.

## Owner

Parallel Codex compiler agent. Fix branch: none (jj, work directly on main).

## References

- FR-SOS-024:
  `doc/08_tracking/feature_request/simpleos_os_requests.md`
- Phase 3 design:
  `doc/05_design/simpleos_fr_sos_024_phase3_ring3_entry.md`
- Phase 3 todo (residual blockers section):
  `doc/08_tracking/todo/simpleos_syscall13_direct_handoff_2026-04-20.md`
- Fix file (compiler):
  `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs`
- Commit that exposed the collision: `a3f4f666` (pre-blocker run was clean;
  collision observed mid-session in subsequent builds)
