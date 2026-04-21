# Remote Baremetal Config Switching

**Date:** 2026-04-21
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 191
**Status:** Closed

## Research

- `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` already validates nested remote composite parsing and the checked-in RV32 baremetal ELF fixture.
- `extract_target_from_spec()` and `extract_remote_backend()` already distinguish default remote RV32 from GHDL RV32 configs.
- The missing proof was that one remote interpreter workload can stay fixed while the lane configuration changes.

## Plan

- Add a pure config-switching spec with no hardware dependency.
- Compare `interpreter(remote(baremetal(riscv32)))` with `interpreter(remote(ghdl(riscv32)))`.
- Assert runtime, platform, arch, target, backend, and resolved workload fixture.
- Close row 191 after lint and focused spec verification.

## Fix

- Added config-switching coverage to the remote baremetal runtime spec.
- Verified both configs resolve the same checked-in RV32 workload while selecting distinct lane targets/backends.
- Closed `todo_db.sdn` row 191.

## Verification

```sh
bin/simple lint test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl
bin/simple test test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl
```
