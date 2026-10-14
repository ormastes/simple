# Optional provider collection types cross a concrete HirType ABI

Status: source repair proposed; native regression and rebuilt producer UNRUN.

The direct positional diagnostic using producer SHA `d657c734623482284f1de1a8eafa923135ebbf436b5b4acdf9633ec54e8bd58f` reached MIR after monomorphization reported zero unresolved calls. PID 1551343 received SIGSEGV at Apport timestamp `Wed Oct 14 05:57:30 2026` (as recorded). Kernel core dumping to Apport explained its later `anon_pipe_write` sleep; this was not a proven logging deadlock or memory-cap kill.

A bounded decode of 2,321,099 compressed bytes produced a 16 MiB ELF core prefix. NT_PRSTATUS identifies PID 1551343, signal 11, PC `0xb87998`, and LR `0xb87974`. The producer's symbol table identifies `MirLowering.relocate_provider_type`. The faulting instruction is `ldr x12, [x11]`; x11 and NT_SIGINFO's fault address equal `0xf198715900000000`.

Disassembly shows the function copying its incoming concrete HirType's second word as a tagged Span pointer. That word is `0xf198715900000001`, matching the RtCoreEnum header at offset 8: Option enum ID 1 and Some discriminant 4053299545 (`0xf1987159`). The captured caller-saved x5 register is not evidence of the first copied word because an allocator call intervened. A Some wrapper entered the concrete HirType ABI. The caller's saved return address lies beyond the bounded core prefix; the precise caller and full backtrace were not recovered.

Two source-proven boundaries in `provider_metadata.spl` pass such wrappers: `HirExprKind.ArrayLit` stores `HirType?`, and `DictLit.value_type` stores `HirType?`, but `relocate_provider_default` checked `!= nil` and passed each optional directly to `relocate_provider_type(HirType, ...)`. Presence testing does not extract the payload. The repair gives each optional an explicit type, binds its present payload with `if val`, and names a concrete HirType local before the call. Absent metadata remains absent. The concrete DictLit key handling is unchanged.

`test/fixtures/compiler/provider_optional_type_native.spl` exercises actual production relocation on Some/None array and dictionary metadata plus absent dictionary key/value metadata, verifies retained integer type and all span fields, preserves child literals, and requires zero diagnostics plus the unique success marker. Native execution is pending.

The core proves the wrapper/concrete ABI mismatch, but not which of these two calls supplied it. Other optional transport defects may remain. Editing target source does not repair the executing old producer; a coherent rebuilt producer is required before claiming the original build fixed. No flag that discards provider defaults or layout metadata is an acceptable substitute.

## Subsequent collector crashes (9ad source)

The repaired-cycle2 baseline and candidate collector builds each exited with SIGSEGV at MIR start after HIR 406/406 and monomorphization. The available compressed core was corrupt and yielded no usable new stack. The historical core above is a different process and run; it does not establish the cause of these new crashes. Their relation to this source defect remains unconfirmed.

This standalone reapplication preserves the original two optional-unwrapping hunks and the existing concrete/nil dictionary-key behavior. It still requires actual fixture execution and a coherent producer rebuild. Applying target source cannot alter the immutable d657 producer executing these collectors, so it must not be described as an effective repair of that current producer's crash.
