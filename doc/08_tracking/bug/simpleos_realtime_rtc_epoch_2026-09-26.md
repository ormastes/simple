# SimpleOS realtime clock lacks a qualified Unix-epoch provider

**Status:** Partial source repair on the x86 RTC route; release gap open.

The prior `CLOCK_REALTIME` handler returned only seconds since midnight. The
candidate repair reads a matching pair of date/time/mode/century register
snapshots, validates calendar fields, converts to Unix seconds, and returns EIO
when it cannot identify a trustworthy instant. Pure decoder tests cover BCD,
binary mode, 12-hour conversion, leap dates, missing century, and invalid
values. No source-matched pure-Simple or guest runtime result is available yet.

The remaining provider contract is larger than this x86 code path:

1. The kernel RTC path now holds a bounded owner gate across its CMOS index/
   data sequence. The x86 bare-metal atomic SFFI now uses real hardware
   atomics; the previous boxed plain loads/stores could not protect SMP access.
   The standalone WM example still reads ports directly, and guest SMP
   contention and interrupt-context ownership have not been qualified.
2. The century register is platform-defined. The candidate reads 0x32 and
   refuses a missing/invalid century. Physical x86 hardware needs the ACPI
   FADT century address or another admitted full-year source.
3. The calendar-to-epoch conversion requires a UTC RTC. QEMU defaults to UTC;
   physical firmware may configure local time. The boot/provider profile must
   attest UTC rather than silently assuming it.
4. AArch64 and RISC-V 64 need their own wall-clock sources behind the same
   SOSIX realtime service. The x86 CMOS path cannot qualify those targets.
5. Guest tests must compare `clock_gettime(CLOCK_REALTIME)`, libc `time`, and
   the Rust `SystemTime` port against the configured QEMU RTC date, including
   midnight and invalid-provider controls. The monotonic clock must remain a
   separate domain.

The x86 bare-metal atomic source passed a host four-thread contention test for
fetch-add and CAS and cross-compiled for x86 freestanding; emitted assembly
contains lock-prefixed `cmpxchgq` and `xaddq`. The repeatable focused gate is
`sh scripts/check/check-simpleos-x86-baremetal-atomics.shs`. This does not
replace an SMP guest test. AArch64 and RISC-V 64 now have candidate shared
atomic source providers, but linked and guest parity remain a separate release
gate.

Relevant hardware behavior is described in the [Linux kernel x86 timekeeping
documentation](https://docs.kernel.org/virt/kvm/x86/timekeeping.html). QEMU
documents its [UTC RTC default](https://www.qemu.org/docs/master/system/qemu-manpage.html).
