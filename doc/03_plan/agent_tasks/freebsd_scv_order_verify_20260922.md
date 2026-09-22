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

TODO: Run `test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl` with
an admitted self-hosted full CLI once available. The host provider contract
exercises disk rejection through the actual bounded wrapper; it does not stand
in for the entire SSpec file.

TODO: Once the FreeBSD Phase 2 compiler is admitted, run compiler, interpreter,
and loader binary tests with its frozen runtime capsule and phase-specific
tool caches. Preserve caches and the existing three-cycle limit; do not launch
a fourth retry of the already-running Phase 2 verification lane.
