# Process session inspection failures reported as complete enumeration

Linux session enumeration skipped every failed `getsid` and treated any `readdir` NULL as end of directory. macOS also skipped all failed `getsid` calls. Consequently permission or I/O errors could produce a successful empty/member count even though inspection was incomplete. Only ESRCH means an entry vanished benignly.

The enumerator now propagates all other inspection errors; Linux resets/checks errno around every readdir. A separate physical API, `rt_process_owned_child_state`, observes WNOWAIT child status and returns negative ECHILD for a nonchild or reaped child. It never substitutes numeric-PID liveness. The legacy is_running API is unchanged. This new API supplies an ownership observation; it does not promise that a session has no escaped descendants or authorize post-reap signalling.

Native Linux evidence: real owned-child running/exited/repeated nonreaping observation preserves exit7 for exactly one reap, then reports ECHILD. A real live nonchild also reports ECHILD. Enumeration injection reproduced two old failures (EACCES inspection and EIO enumeration); corrected source passes those, the ESRCH vanished-entry control, and actual complete enumeration. All source hashes, commands, exits and logs are [retained](evidence/process_owner_2026_11_15/commands.md).

No full runtime/bootstrap or grouped directory execution ran. macOS and FreeBSD native qualification remains pending; macOS inspection handling has source review only. Scheduler/pin integration is separate and cannot claim admission from this physical API.
