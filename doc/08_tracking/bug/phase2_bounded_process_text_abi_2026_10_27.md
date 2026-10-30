# Pinned Phase 2 bounded process call loses command text ABI

- Canonical ID: `phase2_bounded_process_text_abi_2026_10_27`
- Status: open; source compatibility does not close the underlying bug.
- Owner: DevHub / compiler-runtime owners.
- Created: 2026-10-27.
- Producer: P2 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`.
- Source: `src/lib/nogc_sync_mut/sffi/process_capture.spl`.
- Regression: `test/fixtures/devhub/native_http_curl/main.spl`.

The actual HTTP compatibility probe returned missing command although curl8.21.0 was installed. The existing bounded tuple runtime provider accepts explicit command pointer and UTF8 length; a source adapter can preserve that ABI without changing the compiler or provider.

## Evidence

Frozen-source HTTP and binary probes compiled but returned missing command before any localhost request. The exact tuple-provider source adapter and final actual loopback evidence are owned by the provider lane; no success is inferred by this record.

## Removal condition

Remove the source adapter only after the deployed producer correctly marshals command text, argv, deadline and output bound to the normal bounded process ABI and passes real quoted-argument, Unicode, timeout, output-limit and HTTP transport regressions.

Commit identity and final receipts must be appended through the canonical BugDatabase API after integration. No compiler rebuild, standard SSpec execution or unexecuted matrix is claimed.

## 2026-10-28 runner startup reproduction

A fresh runner built from release commit `6011ef9fee09b3ab3fc8d9b069442ed948caaba1`
using the retained P2 producer SHA256
`0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`
built successfully in 259 seconds (7,420,928 KiB peak RSS), but all 24
explicit green/red/zero calibration invocations terminated with SIGBUS before
emitting a test verdict. This does not qualify any test kind or the runner for
replacement. Candidate SHA256:
`1363e8ce398cd44b94ba9d37963b4d0dab30a0eb533169a7df51cda865ebebb6`.

LLDB locates the startup call through `ensure_kill_monitor_running`, `host_os`,
`_env_shell`, `process_run`, and `_process_run_raw`. The generated native call
passes two C words to `rt_process_run_tuple`: command pointer and argv. The
current C provider requires three: command pointer, command byte length, and
argv. The argv pointer becomes a roughly 34 GiB memcpy length and crashes in
`rt_process_run_array`. This is the unbounded sibling of the recorded bounded
ABI defect, not evidence that the configured child executable is missing.

`test/fixtures/test_runner_native_process_capture/legacy_and_explicit.spl`
reproduces both paths with the same native executable: `--legacy` exits 138;
the explicit native capture bridge exits 0 after verifying child exit 7,
exact stdout containing a space, apostrophe and Korean text, and separate
stderr. The new `main.spl` fixture tests the public facade, empty argv and
arguments, missing/empty commands, timeout evidence, and exact bounded
stdout/stderr truncation receipts. The Phase1 seed-JIT execution passes all
seven assertions. Its timeout marker is `TIMEOUT`; the text capture limit
retains head/tail bytes plus an omission marker, so marker bytes are outside
the requested data-byte cap.

The candidate facade workaround routes native AOT calls through the existing
explicit pointer/length bridge. Both `rt_is_interpreter_runtime` and
`rt_is_jit_runtime` must retain the boxed adapter: seed JIT is not an
interpreter but does not expose the native tuple provider through dynamic
SFFI. The P2 producer itself was not rebuilt. The final native facade regression
passes all seven cases via `scripts/check/check-native-process-capture.shs`.
Its binary SHA256 is
`6afd3a9cfb5afe51aa5c78628f29993a1cb4dee2275bd53e0f213ca88b90fced`.
The rebuilt runner (SHA256
`16b2ed834ec62e95a8affe59bd00c6fa7f36112c7411fffdce9347c70a3b5faf`)
starts without SIGBUS, but all 24 acceptance invocations still exit 1.
BDD/spec runs report child-launch infrastructure failures
(`rt_process_run_timeout execvp: No such file or directory`). The initial
Markdown positive fixture also used an unavailable raw `assert` function in
the Phase1 child; that row cannot establish a Markdown runner defect. This
runner is rejected for replacement, and the working deployed runtime remains
unchanged. The successful seven-case gate qualifies the process ABI facade
only, not the full runner or its compiler child.

On POSIX the unbounded helper calls the original
`rt_process_run_tuple(ptr,len,args)` provider. Native Windows retains its
existing bounded-provider route with timeout zero and output cap `-1`, which
the Windows implementation accepts, preserving its CreateProcess/exit-status
repair. Native Windows execution was not exercised by this macOS probe. A bounded-provider call with cap `-1` was rejected because POSIX
refuses negative bounded-capture limits; the timeout-provider alternative was
rejected in review because its implicit 4 MiB cap changes the original
unbounded stdout policy. The original native unbounded provider returns empty
stderr (visible in the regression diagnostic), an existing limitation left
unchanged here. Separate bounded-capture cases assert stderr contents. No
unbounded stderr fix is claimed.

Local immutable-attempt receipts and LLDB evidence:
`/tmp/test-runner-refresh-20261028/` (`build.status`, `build.rss.env`,
`qualification/`, `crash.lldb.log`, `disassemble.log`, `probe-legacy.status`,
`probe-explicit.status`, `facade-timeout-marker.stdout`,
`facade-v5-check.stdout`, `runner-patched-build.status`, and
`qualification-patched/`).
