# SOSIX route manifest v1: clock, deadline, and random families

Status: partial RU-001 census at source baseline `e74a3b58235` with the
shared time-arithmetic edit in this lane. This is source-route evidence, not
interpreter/native/SimpleOS parity or release qualification.

| Route | Source and signature | Current owner and migration disposition |
|---|---|---|
| Hosted monotonic snapshot | `src/lib/nogc_async_mut/sosix/time.spl`: `sosix_time_monotonic_now_ns() -> u64` | Hosted `time_ops.time_now_nanos` reads the clock. Keep clock access provider-owned; it is not a Future or a timer completion. |
| Hosted checked clock snapshots | `src/lib/nogc_async_mut/sosix/time.spl`: `sosix_time_monotonic_sample_v1()` and `sosix_time_realtime_sample_v1()` | Candidate source path keeps monotonic and Unix-epoch domains separate, preserves a negative provider sentinel as an error, and refuses an unrepresentable nanosecond instant through the shared contract. Focused runtime evidence is pending. |
| Shared deadline math | `src/lib/common/contracts/sosix/time_v1.spl`: reached/add/ceil-div/ticks-to-ns/deadline-from-ticks over `u64` | Pure common contract now owns overflow-safe arithmetic for hosted and SimpleOS callers. It saturates impossible deadlines at `u64::MAX`; executable proof is pending a source-matched runner. |
| SimpleOS monotonic and sleep | `src/os/kernel/ipc/syscall_log_time_sysinfo.spl`: `_handle_clock_get_time`, `_handle_sleep` | Kernel scheduler supplies 10 ms ticks; the handler now uses shared SOSIX arithmetic for conversion and sleep deadlines. Tick accuracy, wake delivery, and guest execution still need live evidence. |
| SimpleOS poll timeout | `src/os/kernel/ipc/syscall_process.spl`: `_handle_poll` in three blocking branches | Kernel notification/scheduler owner now uses the same shared ceiling and deadline arithmetic. Notification delivery and cancellation still remain OS-private effects. |
| Hosted native clock | `src/runtime/runtime_native.c`: `rt_time_now_ns`, `rt_time_monotonic_ns`, `rt_time_now_unix_micros` | C runtime uses monotonic clock for elapsed time and realtime clock for Unix timestamps. It still exposes raw symbols outside a generated SOSIX registry. |
| Seed interpreter clock | `src/compiler_rust/compiler/src/interpreter_extern/{mod,time}.rs`: `rt_time_now_nanos`, `rt_time_monotonic_ns`, `rt_time_now_unix_micros` | Hand-maintained Rust dispatch; monotonic values use an `Instant` baseline. Seed behavior is only a bootstrap comparison, never product qualification. |
| SimpleOS realtime clock | `src/os/kernel/ipc/syscall_log_time_sysinfo.spl`: `_handle_clock_get_time(clock_id=0)` | Current RTC branch returns seconds since midnight while documenting `CLOCK_REALTIME`. It lacks a date/epoch snapshot, so Unix-time parity is **open**; do not promote this route as a working realtime SOSIX service. |
| Random | `src/compiler_rust/compiler/src/interpreter_extern/{mod,random}.rs`, `src/runtime/runtime_native.c`, `src/os/realtime/random.spl` | Seed/native `rt_random_*` APIs are separately registered. SimpleOS has a deterministic xoshiro256** PRNG in its baremetal realtime profile, with no shared SOSIX random/entropy service or demonstrated compiler-userland route. Do not treat this PRNG as an entropy provider. |

Next admission requires one clock-source and random-service contract, native
and pure-Simple interpreter dispatch from that contract, SimpleOS realtime
epoch policy, exact timer wake/cancel evidence, and guest compiler use of the
same service APIs. The shared arithmetic removes one divergence but does not
close RU-040, RU-041, or SimpleOS release.
