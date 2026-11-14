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

## Separate session-lifetime attempt — incomplete

A fresh-process probe was prepared at
`src/app/test/kernel_image_digest_session_native_probe.spl` in source commit
`736713173624b01d6182ef8d0289c0ec5a3c87a1`. Its first version imported the
real compiler `BuildSession`, began explicit session allocation, captured
through the real digest memo, ended the allocation and session, then checked
the RC root and reread the memo. It did **not** reach executable production or
runtime execution.

The one authorized native build used the same admitted P2 compiler
(`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`),
LLVM/core-c, one thread, private cache, and a 4 GiB user cgroup with a 180
second deadline and an 8 GiB live `MemAvailable` stop threshold. The actual
closure expanded to 460 source/HIR modules, compared with 71 for the earlier
owner-only probe. At the deadline it had completed 73/460 HIR modules. The
owned scope ended by the watchdog with exit 143 at 180 seconds; last cgroup
current was 3,647,954,944 bytes and `memory.events` reported `oom=0`,
`oom_kill=0`, `oom_group_kill=0`. Start and terminal `MemAvailable` were
56,747,964 KiB and 49,532,952 KiB. There was no executable, no probe output,
and no runtime lifetime evidence. No retry was made.

The closure increase came from the high-level `BuildSession` import and its
compiler-store dependencies. A narrower, separately authorized probe is now
being prepared against the runtime session ABI owned by
`src/lib/nogc_sync_mut/sffi/transient.spl`, which already declares session
begin/end and allocation begin/end. Such a run can test actual runtime session
reclamation with the actual digest memo, but it will not qualify the
`BuildSession` compiler-store reset wrapper. That wrapper spec and its
fresh-process cold-first-capture scenario remain unrun.

Attempt artifacts are retained under
`/tmp/simple-kernel-image-digest-v1/build/kernel-image-session-probe/`:
`native-build.log`, `watchdog.env`, `provenance.env`, `systemd-run.log`, and
`source-inputs.sha256`. This incomplete attempt does not change the earlier
probe's narrower Linux image-hash qualification and does not qualify the new
RC lifetime path.
