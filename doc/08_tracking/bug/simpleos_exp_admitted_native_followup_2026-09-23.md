# SimpleOS `exp` admitted-native follow-up

The Core-C parity selfcheck pins `rt_math_exp(1.0)` to the correctly rounded
binary64 value. Its default host recipe links host libm; that recipe alone
does not verify the SimpleOS provider. The focused
`simpleos_exp_selfcheck.c` is separately linked with `-fno-builtin` against
`simpleos_math.c` and `simpleos_math_ext.c` by
`test/01_unit/os/port/simpleos_sysroot_runtime_provider_test.shs`.

TODO after an admitted SimpleOS Phase 2 compiler/image is available: run
`rt_core_c_utf8_math_array_twin_parity_selfcheck` inside QEMU and attach its
non-vacuous check count plus the image/compiler identity. Host-only evidence
must not be promoted as QEMU admission evidence.

Independent source review and a 200,002-input host-libm comparison confirm
this is a narrow `exp(1)` accuracy repair, not a correctly rounded full-range
implementation. On 100,001 central-range inputs, the observed maximum error
improved from 4 to 3 ULP; on 100,001 inputs from -708 through 709 the observed
maximum stayed at 711 ULP. Some individual results lose one ULP while others
improve, so exact parity outside the regression inputs is not claimed.

TODO(simpleos-exp-range): replace the existing argument reduction and exponent
scaling defects and add independent full-range tests. Both the parent and this
patch return a huge negative value for `exp(-710.0)` and `exp(-745.0)`, while
`exp(709.5)` prematurely returns infinity. Expected results are respectively
`0x0.33802fd28b3c3p-1022`, `0x0.0000000000001p-1022`, and
`0x1.81e9b4b52d0c9p+1023`. Directed rounding and floating-point exception flags
remain outside this narrow value regression's evidence.

Assigned owner: agent
`/root/simpleos_bug_sweep_0923/libc_decimal_float_repair`, after its decimal-float
lane, as recorded by the SimpleOS coordinator.
