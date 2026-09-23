# FreeBSD SCV ordering and provider verification

Owner: FreeBSD remaining-fixes agent; source review: SCV publish agent.
Draft PR: https://github.com/ormastes/simple/pull/1260

TODO: After Linux bootstrap succeeds, run
`QEMU_CPUS=12 QEMU_BUILD_JOBS=12 sh scripts/check/check-freebsd-bootstrap-qemu.shs --full`
from this branch on a Linux host with KVM/QEMU, at least 64 GiB available host
disk, the admitted FreeBSD 14.4 amd64 BASIC-CLOUDINIT image, and SSH credentials.
Use an unused SSH port if the existing guest on port 2222 remains live. Do not
restart or modify the existing guest (host PID 2253062): its frozen source
predates the LLVM 23.1 provider change and cannot validate this revision.

Require native Stage 3 canonical SCV inventory admission, returned value-struct
array fixture success, cold inventory time/RSS evidence, and matching LLVM 23.1
provider receipts before and after native smoke/parity. The existing source
changes and host contract checks do not establish any of those guest outcomes.

Inside the fresh FreeBSD guest, preserve command output, `/usr/bin/time -l`
maximum-resident-set-size, runtime SHA-256, source revision, and exit status for
each of these exact post-bootstrap checks (replace `<stage3>` only with the
admitted guest Stage 3 binary):

```sh
env SIMPLE_NATIVE_COMPILER=<stage3> SIMPLE_NO_STUB_FALLBACK=1 \
  <stage3> test test/01_unit/compiler/mir/returned_struct_array_native_spec.spl
<stage3> test test/01_unit/lib/scv/compile_source_inventory_cold_spec.spl
SCV_COLD_REPORT_DIR=build/freebsd/scv-cold \
  sh test/05_perf/scv/cold_inventory_profile.shs <stage3>
sh scripts/check/check-runtime-https-openssl.shs
```

The HTTPS command must compile and execute the OpenSSL fixture on FreeBSD; a
Linux object build or source/header inspection is not acceptance. Record wall
time and max RSS for the full bootstrap, returned-array native build/run, SCV
unit test, SCV cold profile, and HTTPS compile/run. Compare the candidate
receipts with the same commands on the admitted pre-change baseline; candidate
wall time and max RSS must be no worse than 110% unless a reviewed variance is
recorded. Do not run these guest checks before Linux bootstrap succeeds.

The returned `Slice<Struct>` native fixture remains a precise tracked TODO in
`doc/08_tracking/bug/stage2_compiled_program_returned_array_len_zero_2026-09-20.md`;
the array fixture must not be used to claim Slice coverage.

TODO: Run `test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl` with
an admitted self-hosted full CLI once available. The host provider contract
exercises disk rejection through the actual bounded wrapper; it does not stand
in for the entire SSpec file.

TODO: Once the FreeBSD Phase 2 compiler is admitted, run compiler, interpreter,
and loader binary tests with its frozen runtime capsule and phase-specific
tool caches. Preserve caches and the existing three-cycle limit; do not launch
a fourth retry of the already-running Phase 2 verification lane.
