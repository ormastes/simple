# Stage3 Ignores CPU Baseline and Emits BMI2

The stage3 pure-Simple native builder prints `unknown option '--cpu', ignoring`
for `--cpu x86-64-v1`, then Cranelift emits BMI2 `shlx`. The production QEMU
fixture originally used baseline `qemu64`, causing a `#UD` in PMM bitmap code.

The WM evidence fixture temporarily declares QEMU's `max` model after
`qemu64,+bmi2` still faulted on the emitted `shlx`. The compiler must accept and propagate the CPU baseline or
fail the build; silently ignoring it is not permitted. Once fixed, the fixture
should return to baseline `qemu64` and retain an instruction-set audit.
