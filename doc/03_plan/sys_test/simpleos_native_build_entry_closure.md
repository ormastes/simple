# SimpleOS Native Build Entry Closure - System Test Plan

## Request

Cover `FR-SOS-023`: native-building `examples/simple_os/arch/x86_64/os_entry.spl` must not compile unrelated sibling entry modules such as `wm_entry.spl`.

## Test

`test/system/simpleos_native_build_entry_closure_spec.spl`

## Assertions

- The generated native-build argv includes `--entry-closure`.
- The generated native-build argv includes `--entry examples/simple_os/arch/x86_64/os_entry.spl`.
- The generated native-build argv targets `x86_64-unknown-none`.
- The generated native-build argv does not name `examples/simple_os/arch/x86_64/wm_entry.spl`.

## Verification Command

`bin/simple test test/system/simpleos_native_build_entry_closure_spec.spl`
