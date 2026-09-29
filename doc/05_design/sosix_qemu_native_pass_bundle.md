# SOSIX QEMU native PASS-bundle producer

The collector accepts a PASS row only from
`scripts/check/produce-sosix-qemu-native-pass-bundle.shs`. Matrix wrappers may
publish blocked or failed rows directly, but must not hand-write PASS
`evidence.env` files.

The producer runs after a guest verifier succeeds. It requires a closed host
admission receipt, the exact one-line QEMU argv and version records, the guest
transcript, the kernel, selected guest image, filesystem program, firmware,
and an ordered marker contract with a distinct one-shot boot-correlation
marker. It derives all SHA-256 identities itself and
atomically publishes `ROOT/HOST/GUEST/run-NONCE/evidence.env`. A
compiler-free row retains nine artifacts. A designated compiler row retains
thirteen: the same nine plus `compiler-version.txt`, `compiler-hello.txt`,
`compiler-aliases.txt`, and `compiler-manifest.env`.
The source identity is derived from a clean Git commit and tree; callers cannot
supply it.

Admission binds the detected and requested host, resolved QEMU executable,
QEMU executable hash and version, requested accelerator, advertised
accelerator, and successful runtime probe. Publication rechecks the binary
hash and version. Every firmware stage and the boot-correlation marker must be
an exact, unique transcript line in order. The execution nonce may repeat in
post-entry compiler receipts but must never occur at or before `guest-entry`.
Every row-specific required marker remains ordered. Existing output is never
overwritten.

All six guest names share this contract. Unix wrappers invoke the shell owner;
the native Windows implementation is
`scripts/check/produce-sosix-qemu-native-pass-bundle.ps1`. The Windows matrix
calls it only after the executable SPipe row passes and only when that run has
emitted the closed `build/os/systest/GUEST.native-pass.env` descriptor. A
missing, open, duplicate, or incomplete descriptor changes the row to failed;
it never falls back to a handwritten PASS. The PowerShell producer mirrors the
same admission recheck, source-lineage, transcript, artifact, and atomic
publication rules, including repeatable post-entry nonces and exact-line
firmware markers. Native PowerShell execution was unavailable on the
implementation host; the tracked policy therefore keeps every Windows
compiler designation `false` until a Windows run proves it.

For a designated row, the collector does not accept hashes alone. It requires
the two canonical receipt paths, the exact host/guest/run nonce, mounted
`/usr/bin/simple`, canonical `/tmp/sosix-hello.spl` and
`/tmp/sosix-hello` paths, zero compile/program exits, target-native markers,
and `hello-RUN_NONCE` stdout. It also requires a closed target-emitted readback
receipt for `/usr/bin/simple`, `/bin/simple`, `/sys/apps/simple`,
`/sys/apps/simple_compiler`, `/sys/apps/simple_interpreter`,
`/sys/apps/simple_loader`, and `/SYS/SIMPLETOOL.SDN`. The `/usr/bin/simple`
readback digest—not the kernel digest—is the compiler payload identity. The
manifest binds that payload, the selected image, clean source, nonce, and
placement receipt. This proves target readback; it does not infer image
interior contents from a host-side image hash. Every receipt line must occur exactly once in the
uniquely hash-selected retained transcript. A caller that changes forged bytes
and updates both artifact and transcript hashes still fails semantic
correlation.

The focused self-test is
`scripts/check/check-produce-sosix-qemu-native-pass-bundle.shs`. It uses a
temporary clean Git repository and synthetic artifacts; it launches no guest.
Negative controls cover failed admission, open-schema admission, QEMU binary
replacement after admission, absent nonce, multiline argv, dirty source, and
missing/out-of-order markers. Its compiler controls cover missing/one-sided
receipts, path and inode aliases, mid-copy mutation, and non-designated claims.
The collector self-test separately covers post-publication tampering and forged
receipts whose artifact/transcript hashes were recomputed.

PowerShell was not installed on the 2026-08-12 Linux implementation host, so
its live parser/self-test remains an explicit Windows-host verification item;
the shell contract test and static diff checks do not substitute for it.
