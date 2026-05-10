# SimpleOS Kernel MVP Diagnostics and Test Plan

## Goal

Cover the kernel MVP smoke slice without changing production kernel, syscall,
scheduler, or loader code.

## Scope

- `x86_64_ring3_smoke`
- `x86_64_fat32_exec`
- `x86_64_shell_smoke`
- `x86_64_fault_smoke`
- kernel log and `dmesg` exposure expectations

## Evidence Targets

- pure spec coverage in `doc/06_spec/app/os/feature/kernel_mvp_spec.spl`
- runnable system smoke coverage in `test/system/kernel_mvp_spec.spl`
- kernel log ring-buffer coverage in `test/unit/os/kernel/log/kernel_log_spec.spl`

## Gates

### Gate MVP-1: Ring-3 context setup stays correct

- run `doc/06_spec/app/os/feature/kernel_mvp_spec.spl`
- expect:
  - x86_64 user context uses ring-3 selectors
  - user-mode flags are preserved
  - user stack is aligned for process entry

### Gate MVP-2: FAT32-backed x86_64 exec path resolves

- run `doc/06_spec/app/os/feature/kernel_mvp_spec.spl`
- expect:
  - synthetic filesystem-backed executable bytes resolve
  - process-image construction succeeds for x86_64 bytes
  - argv[0] remains stable for launcher-visible paths

### Gate MVP-3: Shell smoke advertises dmesg

- run `doc/06_spec/app/os/feature/kernel_mvp_spec.spl`
- expect:
  - shell help output includes `dmesg [N]`
  - shell command surface remains discoverable

### Gate MVP-4: Fault smoke rejects invalid entry cleanly

- run `doc/06_spec/app/os/feature/kernel_mvp_spec.spl`
- expect:
  - invalid ring-3 entry returns `-22`
  - unknown syscall dispatch returns `-1`

### Gate MVP-5: Kernel log exposure remains ordered

- run `test/unit/os/kernel/log/kernel_log_spec.spl`
- expect:
  - write order is preserved
  - min-level filtering works
  - bounded ring behavior keeps the newest entries

## System Smoke Command

```sh
bin/simple test doc/06_spec/app/os/feature/kernel_mvp_spec.spl
bin/simple test test/system/kernel_mvp_spec.spl
bin/simple test test/unit/os/kernel/log/kernel_log_spec.spl
```

