# FreeBSD 14.4 riscv64 toolchain provisioning: default pkg bootstrap unavailable

Status: reproduced; repair pending. Owner: RISC-V FreeBSD bootstrap lane.

## Real guest evidence

The official FreeBSD 14.4 RISC-V UFS qcow2 image was downloaded and its
compressed SHA-256 matched `CHECKSUM.SHA256`:
`26cd996ec53a9569e6030eba593e6e8eba617c029aa817c828a49072cc166099`.
`qemu-img check` reported no errors. A separate persistent 64 GiB overlay
booted with QEMU 10.2.1, OpenSBI and S-mode U-Boot on Ubuntu WSL x86_64.

Console login as root succeeded. `uname -srm` returned
`FreeBSD 14.4-RELEASE riscv`; the kernel reported four CPUs and 6144 MB RAM.
`clang --version` reported FreeBSD Clang 19.1.7. A trivial C program was
compiled and executed successfully (`GUEST_CLANG_EXEC_PASS`). The expanded root filesystem
reported 54 GiB available. DHCP supplied 10.0.2.15. SSHD was enabled with a
dedicated key and localhost forwarding. An authenticated SSH command returned
`FreeBSD 14.4-RELEASE riscv`. Use `BatchMode=yes`, `IdentitiesOnly=yes`,
`KexAlgorithms=curve25519-sha256` and `HostKeyAlgorithms=ssh-ed25519` for the
bounded emulated-lane diagnostic connection. The first default connection
timed out during authentication; a separately diagnosed local key passphrase
introduced by Windows argument quoting was removed before the successful run.

`env ASSUME_ALWAYS_YES=yes pkg bootstrap -y` failed. The guest log reported
`Error: Not Found` and `A pre-built version of pkg could not be found for your
system` for both:

- `pkg+https://pkg.FreeBSD.org/FreeBSD:14:riscv64/quarterly/Latest/pkg.pkg`
- `pkg+https://pkg.FreeBSD.org/FreeBSD:14:riscv64/kmods_quarterly_4/Latest/pkg.pkg`

The fallback `.txz` requests failed too. Logs remain inside the persistent
guest at `/root/simple-bootstrap-evidence/pkg-bootstrap.log` with a separate
exit-code file. `PACKAGESITE` alone did not override configured repositories.
An explicit `/usr/local/etc/pkg/repos/FreeBSD.conf` selecting `latest` and
disabling `FreeBSD-kmods` then reproduced Not Found for both
`FreeBSD:14:riscv64/latest/Latest/pkg.pkg` and `.txz`. Its log is
`/root/simple-bootstrap-evidence/pkg-latest-config.log`. Thus both repository
choices were tested; repeated retries of these exact routes are not useful.

## Required follow-up

### Verified Rust provisioning route

FreeBSD ports commit `5b43ce42aed12a24ed88c0e9fd9b1cca2b33e150`
(`lang/rust/Makefile`, `lang/rust/distinfo`, `Mk/bsd.sites.mk`) declares
RISC-V bootstrap version 1.98.1, dated 2026-08-20. Downloaded from its
declared `http://distcache.FreeBSD.org/local-distfiles/rust/2026-08-20/`
route and SHA-256 checked before transfer to the guest:

| Archive | SHA-256 |
| --- | --- |
| rustc-1.98.1-riscv64gc-unknown-freebsd.tar.xz | b9bf93cc30a18102d65c3b4f1a6868c93fd395267ac523df6f37c6376fed8f48 |
| rust-std-1.98.1-riscv64gc-unknown-freebsd.tar.xz | d503e6b03091fad9c0c737ebd475959c4165ca91f144c1951fd28e7ae03e28b1 |
| cargo-1.98.1-riscv64gc-unknown-freebsd.tar.xz | 33aee52f70eb9d484c6fadc45e3bd86c9284ed7ffe0fd85a1b39e1b076918805 |

The unlisted HTTPS variant fails certificate hostname validation; the
download.freebsd.org alternate returns 404. The declared HTTP route succeeded
with mandatory independently obtained ports checksums. Do not disable TLS
verification to make the failing HTTPS variant work.

`pkg` source was cloned at tag 2.8.4, commit
`e1d90eb706cbb4588bbd71bf205843b751c0be51`. A Git source archive was
transferred separately; it is not the ports distfile and must not be claimed
to match that distfile's hash. Installation and native source build are
running under guest daemon PID file
`/root/simple-bootstrap-evidence/source-tools.pid`; inspect live process
identity and `/root/simple-bootstrap-evidence/source-tools-install.log`
before resuming. Rustc and Cargo both report 1.98.1. Rustc compiled and
executed a native guest program that printed `riscv-freebsd-rust-ok`, followed
by `guest_rust_status=pass` in the installation log. This verifies the Rust
compiler and standard library; Cargo dependency compilation is still pending.
The installer then advanced to the pkg source phase and stopped at
`./configure: not found`. The file existed; a guest hexdump proved its shebang
ended in CRLF (`23 21 2f 62 69 6e 2f 73 68 0d 0a`). The source archive was
regenerated from the same commit using `git -c core.autocrlf=false -c
core.eol=lf archive`. A separate pkg-only daemon now runs with PID file
`/root/simple-bootstrap-evidence/pkg-source-build.pid`, log
`pkg-source-build.log` and terminal result `pkg-source-build.exit` in the
same evidence directory. It successfully reached `Found C compiler: cc` and
`Host: riscv-unknown-freebsd14.4`. No pkg source-build PASS is claimed yet.
Do not rerun the already passing Rust probe as part of this repair.

LLVM 23.1.3 source was obtained from the release URL declared by
`devel/llvm23/Makefile` at the same ports revision. Its archive
`llvm-project-23.1.3.src.tar.xz` (179220548 bytes) matches the ports SHA-256
`c44186a7762ed28954be72e5ff6df9808e0779d4f1bf014ecc4e7e211d31ee34`.
The verified archive is retained on the host under
`build/riscv-freebsd/toolchain-media/`; no LLVM installation is claimed.

### LLVM build prerequisites in progress

The guest lacks GNU Make, Python and CMake. These source archives were
downloaded from upstream locations declared by the same FreeBSD ports
checkout, checked against its distinfo, and transferred into the guest:

| Archive | SHA-256 |
| --- | --- |
| make-4.4.1.tar.lz | 8814ba072182b605d156d7589c19a43b89fc58ea479b9355146160946f8cf6e9 |
| Python-3.13.16.tar.xz | f4b1bfb3c79b5bb11b8d228a12504163b4c0dab4d679828d8f5f26b6cb6ab35d |
| cmake-3.31.12.tar.gz | 5f3fd5a54dfa65602bdbed64f981a72673cc19f2d304cc2955cf0dfa0cfd8272 |

The sequential prerequisite installer is live under
`/root/simple-bootstrap-evidence/llvm-prerequisites.pid` (PID 3415 at launch).
Its log is `llvm-prerequisites.log`; its terminal exit file is
`llvm-prerequisites.exit` in that evidence directory. At the last check GNU
Make configuration was testing make include support. The independent pkg
configuration had found libarchive, zlib, bzip2, lzma and zstd and was checking
atomic builtins. Do not restart either from the presence or absence of a
receipt alone: inspect the actual PID, command and descendants first.

The LLVM source archive has also been transferred into
`/root/toolchain-media/`. LLVM compilation has not started. A bounded
coordinator is running: PID file `llvm23-supervisor.pid`, log
`llvm23-build.log`, terminal shell result `llvm23-build.exit`, all under the
guest evidence directory. PID 3793 was verified as `/bin/timeout -k 60 43200
sh /root/toolchain-media/build-llvm-after-prerequisites.sh`, with child 3794.
It is currently waiting for prerequisites and does not launch a second copy
of them. It validates the prerequisite PID identity and terminal result,
allows at most six hours for prerequisites, rechecks the LLVM source hash and
30 GiB free space, then builds Release LLVM and Clang with the RISCV target,
LLVM shared library and RTTI, using two compilation jobs. The overall bound
is twelve hours. On install success it runs version checks and compiles and
executes a C probe before emitting its own PASS. This remains toolchain
evidence, not Simple bootstrap admission.

At coordinator verification, prerequisite PID 3415 and pkg PID 3057 were
both live and their configuration logs had advanced. Retain source
directories and intermediate outputs across bounded repair cycles. If the
outer timeout terminates without a shell exit receipt, inspect the timeout
process and its descendants and preserve its log; do not infer success.

Establish an available, provenance-checked riscv64 package source, or build
the required tools from admitted sources. Verify Rust/Cargo and LLVM 23 in
the guest and execute compiler probes before starting the canonical native
bootstrap. Base Clang 19 does not satisfy LLVM 23 provider admission. Do not
claim bootstrap PASS from VM boot or host-installed tools.

## Retained execution state

Host VM directory: `/home/user/.simple/qemu/freebsd-riscv64` in Ubuntu WSL.
Base: `base.qcow2`; writable guest: `guest.qcow2`; PID: `qemu.pid`.
Console listener: localhost 24444; SSH forwarding: localhost 2224.
Launch/preparation diagnostics live under host repository
`build/riscv-freebsd/`. This is local runtime state, not release admission.
Do not launch another guest against the same writable image. Verify the
recorded process is alive and use its existing console on continuation.
