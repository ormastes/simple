# Windows Container stream reuse audit

Source base: release bbb25521ae79d928ed6a07c3594327eeb3587f4b.

The common V2 stream draft is Linux-specific: its policy and launch template
contain cgroup delegation and the Linux group broker. Windows must use a tagged
V3 policy, template and owned-session variant, never fabricated Linux fields.

`io.windows_pty_owner` already retains ConPTY, asynchronous bounded input,
output channels, exact Job/process handles and cleanup quarantine in one
nonreused slot registry. Its legacy spawn has no hard CPU/memory policy or
launch admission deadline. Its text read is not a byte-stream receipt. The
managed raw extension will reuse that registry without creating ConPTY.

`io.windows_process_owner` supplies typed argument quoting, clean environment
blocks, executable pins and Job memory readback, but its existing output is
file-based. Reuse its codec/pin helpers; do not introduce a third supervisor.

An actual Docker exec instance requires its native Engine exec ID. The Docker
CLI helper PID and the target container ID are not that instance. An ambiguous
exec start cannot be retried or released merely because its helper has exited.
