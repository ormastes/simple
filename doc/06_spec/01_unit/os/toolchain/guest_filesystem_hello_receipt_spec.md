# Guest filesystem Hello World receipt

This contract projects a Clang/LLD Hello World candidate only when its supplied material
contains the real target Clang and LLD executables plus the source, object, and
target executable bytes. Each byte array is bounded and must match its non-zero
SHA-256 digest; all three executable payloads must match the target ELF machine.

The structurally consistent command chain uses the fixed paths `/usr/bin/clang` and
`/usr/bin/ld.lld`, binds the requested SimpleOS target explicitly, and keeps
the source, object, and executable on the declared FAT32, DBFS, or NVFS mount.
The executable must be a structurally valid ELF for x86_64, AArch64, or
RISC-V 64, and execution must produce exactly `Hello World` plus a newline.

The projection fails closed when any artifact is absent, a digest is substituted,
the filesystem path does not match the declared backend, PATH lookup or a host
process was used, execution did not occur in the guest, a command exits
non-zero, or output differs. However, `executed_in_guest`, `used_path_lookup`,
and `used_host_process` remain caller declarations. Even a forged candidate
with ideal flags and transcript produces only
`StructurallyConsistentNonAuthorizing`; the authorization query always returns
false. An evidence-service-authenticated handle plus a loader-owned consume-once
ledger token is required outside this module before any guest-execution PASS.

Executable specification:
`test/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.spl`.
