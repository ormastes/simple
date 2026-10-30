# Windows V2 owned process foundation

Date: 2026-10-29. Status: implementation and native tests prepared; Windows
compilation/execution and modern SSpec execution remain unverified.

The Windows branch previously answered ENOTSUP for the async V2 family despite
having a real synchronous Job Object owner. The new private owner implements
start, bounded poll, cancellation, result and collection with 128 concurrently
owned slots. Its random 128-bit tokens come from Windows RtlGenRandom. Process
handles and kill-on-close Job Objects remain private; PIDs are diagnostics.

Admission creates a suspended child with an explicit inherited std-handle
list, checks Job Object assignment and ResumeThread, then publishes authority.
Failed admission retains any not-yet-waited child privately. The SRW registry
lock protects state and handles. Active operations hold references across poll
sleeps, so collection cannot invalidate an in-flight owner operation.

Both streams share the V2 retention cap. Null-destination polls consume no
bytes; partial delivery preserves NUL bytes and collection refuses undelivered
capture. Terminal requires an exact leader wait, observed empty job membership
and closed capture streams. Windows termination is immediate Job Object
termination; term/kill flags report the same successful action. Zero timeout
leaves useful work unlimited while descendant cleanup remains finite.

UCRT has no ESTALE: Windows stale authority uses the documented provider code
`RT_OWNED_PROCESS_WINDOWS_STALE_ERROR` (116). Optional resource metrics remain
unavailable instead of relabelling Job commit as RSS or lifetime process count
as peak concurrency. V3 input/opaque facade, sealed executable/cwd pins and
V4 remain ENOTSUP; this does not close full Windows SOSIX/V4 qualification.

Acceptance subcases are REQ-WIN-OWN-001 (retained capture), 002 (lifecycle and
tree cleanup), 003 (eighty live leases and threaded ownership), and 004 (failed
admission without authority/handle leaks). They support the existing Windows
parallel ownership requirements without claiming that application runner
routing or two-wave historical-capacity qualification is complete.

## Validation evidence

- Native macOS Darwin cwd-pin selfcheck: PASS.
- Native macOS non-Unix fallback selfcheck: PASS.
- Both host selfchecks needed `-Wl,-dead_strip`: current Darwin snapshot code
  otherwise references runtime functions absent from those standalone test
  stubs. The linker issue predates this Windows change; no stub was added.
- Windows fixture compiled on macOS: reports SKIP and exits 77. This validates
  only the platform refusal, not Windows source compilation or behavior.
- Windows-native C compilation and all four native suites: NOT RUN; no Windows
  producer or SDK is installed on this host.
- Modern SSpec execution: NOT RUN; it requires the Windows-native fixture.
- `simple spipe-docgen ... --output doc/06_spec --no-index`: BLOCKED. The
  available self-hosted `aarch64-apple-darwin-macho/simple` returns exit 1,
  refusing self-delegation and asking for a seed driver. No seed/P2 rebuild was
  used to manufacture documentation or qualification evidence. The manual is
  explicitly authored until an admitted docgen producer is available.

Build the small native C fixture with
`scripts/check/check-owned-process-windows-async.ps1`; this does not rebuild
the Simple compiler. Then execute the existing native SSpec route against the
four modern scenarios and preserve actual producer/run evidence.
