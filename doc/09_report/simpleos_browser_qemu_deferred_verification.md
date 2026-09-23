# Browser QEMU fixture source correction and deferred verification

Issue #7 described missing prebuilt browser ELFs. Current system specs build
their entries in each scenario, but both copies still hardcoded the Rust seed;
the legacy copy additionally selected the removed `examples/simple_os` source
root. Their desktop case converted a missing filesystem into a green
assertion, so it could not prove the advertised launcher/WM completion.

Both specs now use one explicit fixture build selector. It verifies the
self-hosted Stage-4 provenance and runtime identity receipt through the same
canonical gates used by the NVFS QEMU builder, selects current source paths,
requests 12 compiler workers, caches each fixture separately, bounds build
time and rejects concurrent browser fixture builds through a shared lock.
No Rust fallback or committed binary artifact is introduced. Desktop mount
failure remains a failing requirement instead of a passing skip. The desktop
case requires `SIMPLEOS_BROWSER_DESKTOP_IMAGE` and attaches that image as NVMe
with snapshot writes, preserving the supplied disk. QEMU receives an argument
array rather than a shell-expanded command; comma-containing image names are
rejected because QEMU parses commas within its drive option.

The lightweight selector/refusal contract checks all four real source paths,
the 12-worker plan, unknown-target rejection and absent-admission rejection.
It does not launch a compiler or QEMU and cannot prove target execution.
Astra source review accepts this admission/path correction; it adds no guest
memory allocation or hot-path overhead. The build lock covers this browser
suite, not unrelated bootstrap jobs; the platform coordinator must supply the
global memory/process budget before executing any fixture build.

TODO (SimpleOS QEMU owner, after successful Linux bootstrap and an admitted
self-hosted runtime): export `SIMPLE_RUNTIME_PATH`, `SIMPLE_STAGE4_PROVENANCE`
and `SIMPLE_RUNTIME_RECEIPT`, then build each selector with
`sh scripts/check/build-simpleos-browser-qemu.shs <selector>`. Run
`test/03_system/app/browser_engine_in_qemu_spec.spl` using the admitted test
runner and prove all four scenario bodies execute, including the browser-soft
PASS marker and desktop launcher/WM/remote-grouping markers. Provision the real
desktop app disk and provide its path through `SIMPLEOS_BROWSER_DESKTOP_IMAGE`.
Missing disk provisioning must stay RED. Retain compiler/runtime identity, ELF hashes,
fresh serial logs, faults, elapsed time and peak RSS. Keep issue #7 OPEN until
this target build and guest execution evidence exists.
