# FreeBSD QEMU bootstrap CPU contract

The bootstrap LLVM backends currently select x86-64-v3. Under TCG the wrapper
uses `-cpu max`, because `qemu64` lacks AVX2 and generated Stage 2 executables
can fail with SIGILL before `--version`. KVM continues to use `-cpu host`.

Immediately after guest SSH access, the wrapper compiles a baseline x86-64
CPU detector using the FreeBSD base clang. Its AVX2 builtin includes operating
system AVX state support. Failure stops before dependency installation, source
transfer, or bootstrap. This is an AVX2 admission check, not a complete formal
verification of every x86-64-v3 instruction.

On the current 20-core host, request resources explicitly:

```sh
QEMU_CPUS=16 QEMU_MEM=64G SIMPLE_FREEBSD_SELFHOST_JOBS=14 \
  sh scripts/check/check-freebsd-bootstrap-qemu.shs --full
```

Defaults remain 4 vCPUs, 8G RAM and one build job. `QEMU_BUILD_JOBS` provides a
wrapper-level job setting; `SIMPLE_FREEBSD_SELFHOST_JOBS` takes precedence.
More TCG vCPUs do not guarantee linear speedup.

The host-only behavioral regression is
`sh test/01_unit/freebsd_bootstrap_qemu_tcg_isa_test.shs`. It checks actual
launch arguments, the guest probe command, explicit resource settings, job
override precedence and unsupported-guest rejection. Its historical qemu64
mutation must fail the required CPU selection. Fake tools avoid starting QEMU.
The canonical `--full` check remains required evidence for actual Stage 2 and
Stage 3 compilation and execution; unit success does not establish that result.
