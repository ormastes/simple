# Process session inspection failures reported as complete enumeration

Linux session enumeration skipped every failed `getsid` and treated any `readdir` NULL as end of directory. macOS also skipped all failed `getsid` calls. Consequently permission or I/O errors could produce a successful empty/member count even though inspection was incomplete. Only ESRCH means an entry vanished benignly.

The enumerator now propagates all other inspection errors; Linux resets/checks errno around every readdir. A separate physical API, `rt_process_owned_child_state`, observes WNOWAIT child status and returns negative ECHILD for a nonchild or reaped child. It never substitutes numeric-PID liveness. The legacy is_running API is unchanged. This new API supplies an ownership observation; it does not promise that a session has no escaped descendants or authorize post-reap signalling.

Native Linux evidence: real owned-child running/exited/repeated nonreaping observation preserves exit7 for exactly one reap, then reports ECHILD. A real live nonchild also reports ECHILD. Enumeration injection reproduced two old failures (EACCES inspection and EIO enumeration); corrected source passes those, the ESRCH vanished-entry control, and actual complete enumeration. All source hashes, commands, exits and logs are [retained](evidence/process_owner_2026_11_15/commands.md).

No full runtime/bootstrap or grouped directory execution ran. macOS and FreeBSD native qualification remains pending; macOS inspection handling has source review only. Scheduler/pin integration is separate and cannot claim admission from this physical API.

## Post-merge CI repair

PR9261's post-merge Code Idiom gate failed local-rt-dual-implementation; it must not be described as green. The new C ABI lacked the Rust-call surface counted by that gate, despite the C translation unit already being linked into the Rust runtime composition. The follow-up adds a reachable Rust-mangled host forwarding module and the Simple process SFFI alias/registration. It preserves one shared C OS implementation and exact errors. Actual Rust+C linkage and real-child delegation pass; sole exported C ABI ownership is verified by nm. [Original CI failure and repair evidence](evidence/process_owner_alias_2026_11_15/commands.md) retain the exact scope. No baseline waiver or policy duplication was used. Simple-wrapper execution and native macOS verification remain pending.
