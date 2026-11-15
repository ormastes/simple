# Windows process admission and collection ownership gaps

Status: SOURCE_CONFIRMED; reproduction and native qualification NOT_RUN.
The existing six-cycle native/bootstrap campaign is closed. This report records
source evidence, not an executed reproduction.

`src/lib/nogc_sync_mut/io/windows_process_owner.spl` has three relevant paths:

- `_windows_process_failed_child_v1` calls `WaitForSingleObject(process, 10000)`
  and `_windows_process_empty_v1`, whose polling loop calls `Sleep(10)`.
  Admission failure can therefore block the control thread while cleanup runs.
- `windows_process_collect_v1` publishes `closed = true` before closing process,
  Job, pin and allocation resources. A failed release returns an error, but a
  subsequent collection cannot retry those resources because the slot is closed.
- Admission accepts a process timeout but no signed launch Unix expiry.
  `CreateProcessW` and `ResumeThread` have no immediate launch-expiry gate.
  A process timeout is not a substitute for grant validity at the effect.

The synchronous Docker provider uses a separate admitted capture path, which
already checks expiry. Moving it onto the old Windows owner without repairing
these differences would regress both responsiveness and authorization.

Required reproduction/prevention inventory (all NOT_RUN): inject Job assignment
or resume failure and verify each owner turn uses only zero-time waits; inject
each handle/allocation release failure and verify the same retained owner can
retry without closing a recycled handle; expire admission before create and
between suspended create and resume, proving no resume occurs; retain uncertain
child/tree cleanup rather than emitting a no-effect or collected certificate.

The new command continuation must also bound stdout/stderr reads, preserve
partial UTF-8 across reads, use an explicit handle whitelist and environment,
and keep the actual Job/process/pipe owner on every post-effect failure.
Legacy owner repair and a consumed cooperative executor are distinct obligations.

The shared finite Host executor also entered Windows `create` directly, whereas
`WindowsDockerRuntimeProviderV1.create` requires its own prepared record. Host
capacity admission does not create that provider record. The cooperative path
therefore sequences actual provider preparation after journal begin and before
create. The signed-journal scripted Windows regression checks command cursor 2
before any create and durable exact creation intent at cursor 7 before start.
Those authored assertions remain NOT_RUN.
