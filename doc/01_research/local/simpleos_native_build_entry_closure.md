# SimpleOS Native Build Entry Closure - Local Research

## Scope

Feature request: `FR-SOS-023` in `doc/08_tracking/feature_request/simpleos_os_requests.md`.

## Findings

- The reported failure is source inclusion breadth, not a required dependency on `wm_entry.spl`.
- `src/os/qemu_runner.spl` builds OS targets by spawning `simple native-build`.
- `NativeProjectBuilder` already supports `entry_closure`; when enabled it walks imports from `--entry` instead of compiling every `.spl` file under each source root.
- x86_64 wrapper targets use broad roots such as `src/os`, `src/lib`, and `examples/simple_os`; without entry closure, sibling entries like `examples/simple_os/arch/x86_64/wm_entry.spl` are eligible for unrelated compilation.

## Selected Fix

Keep the OS build lane on `--entry-closure` and make the generated native-build argv directly testable through `os_native_build_args`.

## Regression Surface

- Unit SSpec: `test/unit/os/qemu_runner_spec.spl`
- System SSpec: `test/system/simpleos_native_build_entry_closure_spec.spl`
