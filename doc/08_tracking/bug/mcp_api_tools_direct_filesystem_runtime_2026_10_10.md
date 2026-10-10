# MCP API tools bypassed the SoSix host boundary

Actual a0 source declares and invokes four runtime filesystem externs in the application leaf. This patch routes its existing operations through explicit SoSix aliases to the existing standard filesystem owners. Directory listing uses io_runtime.dir_list, not list_dir (which contains a shell fallback). No new runtime implementation or host-specific fallback is introduced.

Source inspection platform matrix (execution NOT performed):

| Platform | Existing provider authority | Execution |
|---|---|---|
| Linux | runtime_native rt_dir_list POSIX opendir/readdir branch | Pending MCP build and tests |
| Windows | runtime_native rt_dir_list FindFirstFileA/FindNextFileA branch; existing host_path_native | UNEXECUTED; existing ANSI provider limitations unchanged |
| macOS | non-Windows POSIX branch | UNEXECUTED |
| FreeBSD | non-Windows POSIX branch | UNEXECUTED; canonical QEMU --smoke deferred for resources |
| SimpleOS | Host facade is explicitly outside src/os/sosix; native-host provider is not evidence of a SimpleOS guest filesystem provider | UNQUALIFIED; separate target capability required |

File reads/existence delegate to existing file_ops; directory existence delegates to io_runtime.is_dir with host_path_native normalization. All target aliases retain their existing signatures. Missing directory/read failure semantics remain the existing facade semantics. Three genuine assertions scenarios and their manual are authored, UNEXECUTED. Source-boundary review does not qualify any platform. This work is separate from the frozen a0 Phase3/Phase4 diagnostic epoch.
