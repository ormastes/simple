# SimpleOS Guest Toolchain Target Selection

The filesystem-launched focused Simple tool selects one immutable
`SimpleOsGuestTarget` after parsing the command and before any filesystem read,
lowering, code generation, or link. Architecture-specific libc assembly
reports a bounded numeric identity and implements a target-local user-context
check;
the Pure-Simple app owns all policy and rejects every identity outside x86_64,
AArch64, and RV64.

The descriptor binds the canonical target triple, existing `CodegenTarget`,
the LLVM/Clang machine triple, installed sysroot/runtime/CRT/libc/linker-script
paths, and the shared guest linker architecture. RV policy remains
`riscv64gc-unknown-simpleos`, while Clang receives its supported equivalent
`riscv64-unknown-simpleos` plus `-march=rv64gc -mabi=lp64d`; both fields are
validated as one descriptor and the entry object therefore matches the guest
sysroot's RVC and double-float calling ABI. The
CLI sets linker environment from that same value.
The shared linker facade validates that its architecture and configured target
still agree. x86_64 retains its existing userland native-link owner. AArch64
and RV64 use explicit installed-userland branches with the descriptor-bound
CRT, Simple runtime, libc, and linker script; they never enter the sibling
kernel routes that inject boot CRTs, scheduler owners, `boot_main`, privileged
CSR setup, or `wfi`. This avoids a second target decision and fails closed on
confused-deputy calls.

The compatibility entry points remain callable and select once for their own
invocation. The CLI uses the explicit `*_for_target` entry points so compile
and interpretation do not repeat target detection. Target selection is O(1),
allocates no collections, performs no scans, and adds no loop or dynamic
dispatch to source lowering or code generation.

The assembly shim is deliberately architecture-neutral at its API boundary.
x86_64 checks the CS requestor level and AArch64 checks `CurrentEL`, so neither
adds a kernel transition. RV64 U-mode has no readable current-mode CSR; that
implementation executes getpid syscall 4 and accepts only a positive kernel
PID. Thus the RV fallback proves a working U/S trap-return path without a
forgeable constant while keeping the other hot paths register-only.
