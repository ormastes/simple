# Linux main-image snapshot V1

Status: native Linux AArch64 locator fixture passed; provider integration pending. This
private locator does not admit the public LLVM observer capability.

The resident provider serializes the cold create operation and uses the opaque
handle only after successful preparation. The handle is token 1, never a native
pointer. The immutable snapshot is retained until process exit. Repeated create
checks the new caller's byte/function limits against actual retained usage.

The host leaf uses dl_iterate_phdr's main-program entry, validates all arithmetic
and readable PT_LOAD ownership before reading PT_NOTE, and accepts the exact GNU
20-byte build ID. Weak start/stop symbols identify the loaded semantic section;
no section-name scan, pathname identity or file-offset inference is used.
The leaf copies the section because the compiler's pcsections storage may be
writable. Original section VA remains available for Simple's relative-PC decoder.

The one allocation includes descriptor, 128 range slots, build ID, actual function
table and section copy. Caps are 128 load ranges, 65,536 functions and 8 MiB
section data. Missing instrumentation returns Absent; malformed maps or holes
return InvalidMap; exceeded bounds return Exhausted. Every actual LLVM ID must
resolve inside the main image's executable ranges. DSO registration, unload and
concurrent unsynchronized creation are outside this interface. Simple owns row
parsing, semantic identity validation and session admission.

The header fixes scalar field ordinals and private statuses. Non-Linux64 leaves
return Unsupported, but normal Windows builds must not link this object at all.
The provider link owner explicitly materializes the Linux-only object outside
the default runtime archive; this source alone is not a complete pipeline edge.

Native fixture: scripts/check/check-xray-llvm-image-locator.shs. It compiles a real
LLVM XRay target separately from the uninstrumented cold leaf and links a SHA1
build ID. Present and absent section executables test the OS/runtime boundary;
owned note buffers exercise malformed-note rejection. These tests do not prove
a Simple-generated binary or a fully admitted capture session.

## Native evidence

Source a8611b15cec68abe932fc562992e57ee6d519493 passed 33 present-section
checks and three absent-section checks on Linux AArch64. Clang 23.1.0 revision
ea7d852a70e8bdfaf601d6626a760f9771b2c4b4 linked compiler-rt XRay archive SHA256
64319290b7b1264c34b497da2ab86f85877883eac8805af06047efc48c80da4d.
The single qualification cycle compiled and executed inside a 1 GiB cgroup with
swap disabled and a 60-second bound. Both executables exited zero. Logs and
artifacts are retained in `/tmp/xray-image-locator-native-20261114/`.

Astra preflight requested an explicit function-table alignment invariant; it is
now enforced by _Alignas and a static offsetof assertion. The existing preceding
range-array layout already provided alignment, so this is hardening rather than
a reproduced defect. The platform guard explicitly requires little-endian LP64.
No x86-64 native run, malformed foreign mapping experiment, concurrent creation,
Simple-generated executable or full provider session is claimed by this fixture.
