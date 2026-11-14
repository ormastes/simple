# KernelImageDigestV1 native probe — 2026-11-14

## Result

The Linux `kernel_image_digest_v1()` owner returned the SHA-256 of the running
probe executable. The value was stable across two calls in one process and
matched an external `sha256sum` of the immutable probe binary:

```text
actual_host=linux
kernel_image_sha256=ff16ecbc3a6ec7dcda7580fea5320d08806205c02d0ad2a3128dccca8bf6e022
kernel_image_sha256_repeated=ff16ecbc3a6ec7dcda7580fea5320d08806205c02d0ad2a3128dccca8bf6e022
sha256sum(probe)=ff16ecbc3a6ec7dcda7580fea5320d08806205c02d0ad2a3128dccca8bf6e022
```

The probe was compiled and executed on Linux/AArch64. Its compiler was the
admitted P2 binary at
`/home/yoon/dev/simple-jit-free-s1-20261114/build/bootstrap/pinned-src/pinned-33bc5c6d1d80/build/bootstrap-jitfree-s1/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
whose SHA-256 was
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
The path includes `stage3`, but this binary is classified as the admitted P2
compiler; this evidence does not qualify a Phase3 compiler.

The probe build used the default LLVM backend, `--runtime-bundle core-c`, one
thread, an explicit isolated cache, and a 4 GiB tree-RSS cap with a 300 second
timeout. It completed successfully in the recorded systemd scope. The earlier
2 GiB attempt was killed by the OOM killer; it is not counted as probe
qualification.

## Reproduction artifacts

- Probe source: `/tmp/simple-kernel-image-probe/src/app/test/kernel_image_digest_native_probe.spl`
- Probe source commit: `9ef6183b5d871d36890209e825d5b2ef58cce8b0`
- Immutable probe executable: `/tmp/simple-kernel-image-probe/build/kernel-image-probe/probe`
- Executable SHA-256: `ff16ecbc3a6ec7dcda7580fea5320d08806205c02d0ad2a3128dccca8bf6e022`
- Successful native-build log: `/tmp/simple-kernel-image-probe/build/kernel-image-probe/native-build-4g.log`
- Owner implementation commits: `83d4cf83879` (Linux observation owner),
  `19cfd677de2` (lazy typed resolver in compile context)
- The external executable hash was obtained with `sha256sum` on the immutable
  executable; the two same-process owner results are printed by the probe.

For the successful run, the process was launched with `OS=Darwin` and
`SIMPLE_NATIVE_BUILD_TARGET=x86_64-apple-darwin`; a second run used
`OS=FreeBSD` and `SIMPLE_NATIVE_BUILD_TARGET=x86_64-pc-windows-msvc`. In both
cases the owner reported the actual host as Linux and returned the same
digest. The executable itself is an AArch64 Linux ELF, so these runs test
resistance to misleading environment labels, not true cross-target execution.

## Scope and limits

This qualifies the Linux/AArch64 current-kernel-image observation factory for
this probe. It does not establish Phase3 lineage, the identity of configured
Phase2 semantic producers, dynamically loaded library identity, or a complete
code-closure digest. The non-Linux unavailable branch has an authored
source-string assertion only; that spec is unrun and was not run on a
non-Linux host. No unit spec or full compiler check was run as part of this
native probe.
