# Agent plan: SimpleOS filesystem toolchain and servers

| Lane | Result/owner |
|---|---|
| Server history/runtime audit | lower-model sidecar; complete, merge by root |
| LLVM/Clang FS audit | lower-model sidecar; complete, merge by root |
| Simple role/image audit | lower-model sidecar; complete, merge by root |
| Full-CLI admission / Stage4 recovery | root; parser/native-arena repairs complete, Core-C explicit-path fallback repaired with focused Rust PASS; fresh incremental Stage3 and admission pending |
| ARM64 filesystem launch + server/toolchain | Spark sidecars; mounted one-shot ELF, VFS/readiness gate, bounded argc 1-2 startup frame, stack mapping, and fail-closed copy implemented; runtime proof/process concurrency pending; merge by root |
| RISC-V64 filesystem launch + server/toolchain | Spark sidecar; Sv39 user slot separation, inherited kernel slot, trap Scheduler/exit state, and validated continuation model implemented; live `sret` continuation pending; merge by root |
| Loader and image implementation | root; coordinate with active x86 FS lane |
| HTTP/DB implementation | root; existing TCP/service owners only |
| Generated manuals | root |
| Final review | normal/highest-capability root `$verify` |

ARM64 and RISC-V64 must reuse `resolve_executable_bytes`, the mounted VFS range
reader, existing ELF mapper/spawn, boot TCP facade, and centralized image role
paths. Neither architecture may add a parallel loader or count a prepared task
frame as filesystem execution. Manual helper names and fail-fast policy are recorded in
`.spipe/simpleos_filesystem_toolchain_servers/state.md`.
