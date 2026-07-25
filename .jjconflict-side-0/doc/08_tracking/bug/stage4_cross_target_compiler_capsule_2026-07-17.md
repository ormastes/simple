# Stage4 accepted cross targets without cross compiler capsules

## Symptom

The hosted C plan can legitimately select Linux AArch64 or RISC-V64 cross C
drivers for ordinary native builds. Strict Stage4 reused that path even though
its compiler/backfill capsule is host-architecture-specific. Continuing toward
composition would mix cross-target Simple/runtime objects with a host compiler
capsule.

## Fix and prevention

Strict Stage4 now rejects `hosted_plan.requires_cross` after hosted target and
host-linker admission but before compiler discovery or temporary object
creation. Ordinary LLVM and Cranelift cross builds remain unchanged. The
focused source-order regression pins the guard before compiler, runtime, and
entry compilation; native target rows cover Linux x64/AArch64/RISC-V64, macOS
x64/AArch64, Windows x64, and FreeBSD x64/AArch64.

Real cross-target Stage4 remains deferred until target-specific compiler
capsules have explicit ABI, inventory, and distribution ownership. No runtime
execution is claimed under this session's static-only restriction.
