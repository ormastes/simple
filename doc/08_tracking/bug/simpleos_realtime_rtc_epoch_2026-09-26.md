# SimpleOS realtime clock lacks a qualified Unix-epoch provider

**Status:** Partial source repair on the x86 RTC route; release gap open.

The prior `CLOCK_REALTIME` handler returned only seconds since midnight. The
candidate repair reads a matching pair of date/time/mode/century register
snapshots, validates calendar fields, converts to Unix seconds, and returns EIO
when it cannot identify a trustworthy instant. Pure decoder tests cover BCD,
binary mode, 12-hour conversion, leap dates, missing century, and invalid
values. No source-matched pure-Simple or guest runtime result is available yet.

The remaining provider contract is larger than this x86 code path:

1. CMOS index/data access at ports 0x70/0x71 needs one serialized owner across
   CPUs and every RTC consumer. Matching reads alone do not protect against
   another reader changing the shared index between outb and inb.
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

Relevant hardware behavior is described in the [Linux kernel x86 timekeeping
documentation](https://docs.kernel.org/virt/kvm/x86/timekeeping.html). QEMU
documents its [UTC RTC default](https://www.qemu.org/docs/master/system/qemu-manpage.html).
