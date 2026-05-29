# SimpleOS Desktop Core Formal Verification — Agent Tasks

## Scope

Break the later proof-bearing work into clear ownership slices after the research-first milestone.

## Kernel Proof Lane

Owner:

- kernel verification worker

Focus:

- trap/syscall/privilege seam
- capability and grant authorization invariants
- scheduler lifecycle invariants

Files:

- `src/os/kernel/arch/riscv64/trap_model.spl`
- `doc/04_architecture/simpleos_interfaces.md`
- `doc/06_spec/app/os/feature/rv64_user_mode_exec_spec.spl`

## Desktop Contract Lane

Owner:

- desktop verification worker

Focus:

- selection/focus uniqueness
- launcher/window provenance
- crash-containment defaults
- desktop readiness marker semantics

Files:

- `src/os/desktop/app_switcher.spl`
- `src/os/desktop/shell.spl`
- `src/os/crash_policy.spl`
- `src/os/qemu_runner.spl`

## Tooling Lane

Owner:

- verification tooling worker

Focus:

- repair `bin/simple verify status`
- restore a trustworthy repo-native verification status path

Files:

- `src/app/verify/main.spl`
- dependent exported modules reached from the current verify entrypoint

## Reporting Lane

Owner:

- docs/reporting worker

Focus:

- claim policy
- assumption ledger
- evidence taxonomy enforcement in reports and docs

Files:

- `doc/04_architecture/simpleos_desktop_core_formal_verification.md`
- `doc/05_design/simpleos_desktop_core_formal_verification.md`
- future verification reports
