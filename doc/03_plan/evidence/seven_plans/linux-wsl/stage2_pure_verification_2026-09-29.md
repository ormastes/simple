# WSL Stage 2 in-process verification probe

Status: FAIL, prerequisite remains open. This is not Stage 4 admission.

The existing canonical phase verifier was invoked with
`BOOTSTRAP_STAGE2_TEST_DELEGATE=0`, `--phase=stage2`, `--strategy=normal`,
`--profile=slim`, and a bounded 90-second task timeout. No MC/DC waiver or
seed delegation was used. Its recorded execution mode is `in-process`.

Compiler: `/root/simple-bootstrap-main-linux/.simple/storage/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`.
Expected and observed SHA-256:
`59cc994ea150db7ef5ad4b318c06b8c0774e27eb244686f4a5e1189215a331d6`.
The verifier validated the frozen Phase 2 runtime capsule and compiler hash.
Compiler version completed once (exit 0); do not rerun that unchanged criterion.

| Required row | Result |
|---|---|
| Compiler CLI build | TIMEOUT, status 124, 91 seconds, peak RSS 2,528,500 KiB |
| Test runner build | BLOCKED by failed CLI build |
| Compiler-bootstrap, interpreter, loader tests | UNSUPPORTED because no full CLI artifact was built |

The verifier exited 1 with five terminal failures and three unsupported tasks.
This bounded timeout is not proof of an implementation defect or a measured
performance regression; the full CLI may require a longer build. The CLI log
contains no diagnostic that localizes a source failure. No descendant process
from this invocation remained at the final process check.

Work and summary:
`/root/simple-seven-plans-wsl/build/native_probe/stage2-pure-verification/summary.env`.
Retained cache:
`/root/simple-seven-plans-wsl/build/native_probe/stage2-pure-verification-cache`.
Parent log:
`build/native_probe/index-compatibility-tdd/wsl-stage2-pure-verification.log`.
Clang frontend was explicitly selected through `CC` and `SIMPLE_CC` as
`/root/llvm/LLVM-23.1.1-Linux-X64/bin/clang`, with LLVM tools from
`/root/llvm-2311-prefix/bin`. No successful compiler invocation is inferred
from environment selection alone.

Resume owner: parent bootstrap lane. Resume the failed CLI producer with retained
cache and a realistic bound, then the blocked runner/tests. Do not promote the
existing Stage 2 admission receipt to passing compiler tests or Stage 4; retain
the failed matrix until the required executable rows actually pass. The original
other-session bootstrap checkout was used as source input, not modified source.
Its HEAD is `bb3f6ab8ab2`; its pre-existing dirty bootstrap and sanity-gate
scripts remain untouched and are not included in this change. This result
does not certify the publication branch's newer source.
