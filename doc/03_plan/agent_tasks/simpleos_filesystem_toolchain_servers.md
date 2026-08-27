# Agent plan: SimpleOS filesystem toolchain and servers

| Lane | Result/owner |
|---|---|
| Server history/runtime audit | lower-model sidecar; complete, merge by root |
| LLVM/Clang FS audit | lower-model sidecar; complete, merge by root |
| Simple role/image audit | lower-model sidecar; complete, merge by root |
| Loader and image implementation | root; coordinate with active x86 FS lane |
| Canonical TCB lifecycle identity | Codex lifecycle lane; independent static review PASS, runtime verification deferred |
| HTTP/DB implementation | root; existing TCP/service owners only |
| Generated manuals | root |
| Final review | normal/highest-capability root `$verify` |

Shared interfaces are the mounted VFS range reader, existing ELF mapper/spawn,
boot TCP facade, and centralized image role paths. Manual helper names and
fail-fast policy are recorded in
`.spipe/simpleos_filesystem_toolchain_servers/state.md`.
