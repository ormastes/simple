# Select a canonical SimpleOS guest

**Draft manual. Native SSpec and SPipe generation UNRUN.**
Source: `test/01_unit/os/qemu_target_selection_v1_spec.spl`.
Requirements: platform REQ-001, REQ-011, REQ-016, REQ-022.

1. Select x86_64 by short alias, prefixed alias and canonical userland triple.
   Each resolves to the same catalog architecture.
2. Select adjacent ARM/RISC-V and 32-bit userland identities. Check the
   architecture actually returned, rather than merely checking acceptance.
   Follow both RV64 userland spellings through machine inspection and require
   the unchanged 64-bit RV64GC catalog identity and userland profile.
3. Submit an unknown target, hosted triple, bare-metal kernel triple or board
   identity. Both registry lookup and the actual CLI inspection entry refuse it.
4. Configure RV64 as the environment default. Confirm that it remains selected
   and that explicit inline/separated CLI flags take precedence. Restore the
   environment before making assertions. The executable scenario captures the
   observed selections; no capture was produced in this session.
5. Supply unknown discovery or an invalid default. Check that the error remains
   visible and cannot become x86_64. An explicit valid CLI flag still wins.

Use `doc/03_plan/sys_test/simpleos_cli_target_identity_2026-10-01.md` for exact
resume commands. A unit refusal or source review is not a real guest boot.
