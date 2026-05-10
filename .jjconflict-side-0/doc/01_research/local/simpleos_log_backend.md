<!-- codex-research -->
# SimpleOS Log Backend Research

## Goal
Route SimpleOS baremetal debug output through the shared Simple log library instead of ad hoc `serial_println` calls, while keeping the log library loosely coupled to OS code.

## Findings
- `src/lib/nogc_async_mut_noalloc/log/logger.spl` already provides the minimal baremetal logging API:
  - `log_init(level, targets)`
  - `log_debug/info/warn/error(...)`
  - target bitmask switching via `TARGET_DEVICE`, `TARGET_SEMIHOST`, `TARGET_HOST_FILE`
- `src/lib/nogc_async_mut_noalloc/log/targets.spl` currently hardcodes `print msg` for both device and semihost targets.
- SimpleOS x86_64 already has a serial sink in the runtime boundary:
  - `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
  - `serial_println(RuntimeValue)` and direct `serial_puts(...)`
- Pulling `os.kernel.arch.x86_64.console` into the std log library would create the wrong dependency direction (`std` depending on `os`).

## Chosen Direction
- Keep the shared log library OS-agnostic.
- Add a small runtime hook in the log target layer:
  - `rt_log_target_device_write(msg: text) -> bool`
  - `rt_log_target_semihost_write(msg: text) -> bool`
- Let SimpleOS provide the serial implementation in its baremetal runtime.
- Keep target switching in the shared logger via the existing bitmask API.

## Dependency Outcome
- `std.nogc_async_mut_noalloc.log` stays independent of `os.*`.
- SimpleOS only supplies a sink implementation.
- Boot/test lanes can opt into serial logging with:
  - `log_init(LOG_DEBUG, TARGET_DEVICE)`

## Next Debugging Use
- Keep canonical QEMU/test markers on raw serial for compatibility.
- Use the shared logger for non-canonical debug and diagnosis messages in shell/desktop flows.
