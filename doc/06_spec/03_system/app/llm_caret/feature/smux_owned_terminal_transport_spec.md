# Real owned helper transfer into smux

Source: `test/03_system/app/llm_caret/feature/smux_owned_terminal_transport_spec.spl`.
Status: **AUTHORED_UNRUN**. No builds, native execution or docgen ran.
This is Linux helper transport coverage, not signed production Container
admission, Podman attachment, a HostHelperLease or a host capacity release.

Run once in a fresh isolated admitted native test process. Set the mandatory
`SMUX_OWNED_TEST_CONFIG` to an absolute regular no-follow SDN config file. Its
exact eight fields are:

| Field | Trusted test-admin input |
|---|---|
| `root` | Fresh empty absolute private broker directory |
| `brokerProgram` | Absolute admitted compiled Linux stream broker |
| `brokerDigest` | Expected SHA-256 of that broker |
| `helperProgram` | Explicit approved regular no-follow shell executable supporting `-c` |
| `delegatedCgroupPath` | Actual delegated writable cgroup-v2 parent |
| `memoryLimitBytes` | Explicit positive fixture memory budget |
| `snapshotDigest` | Actual fixture snapshot identity |
| `cacheIdentity` | Actual fixture cache identity |

Missing, extra or wrongly typed fields fail. The test does not create or chmod
the root or manufacture delegation. Bounded absolute `/usr/bin/id -u` and
`/usr/bin/stat` oracles require a nonsymlink directory with exact mode 700 and
current UID ownership. GNU stat's English file-type output is required; run the
fixture under a C/POSIX locale. The configured path ancestry is trusted test-admin
scope. The test checks root emptiness, actual broker hash and the observed hash
at the explicit helper path. Both helper and broker must be regular no-follow
executables: `/bin/sh` is commonly a symlink and is not assumed valid. The test
never resolves a symlink or substitutes another shell. Missing tools, entropy,
native backend or delegation fail without skip-pass.

The frozen helpers are `smux_owned_fixture_config`, `smux_owned_fixture_start`,
`smux_owned_fixture_adopt`, `smux_owned_fixture_poll` and
`smux_owned_fixture_cleanup`. They now live in the shared
`test/helpers/smux_owned_process_fixture.spl` module, using the repository's
existing `test.helpers.*` import convention. The owned-helper config remains
exactly eight fields; the separate compiled socket fixture uses its own exact
nine-field config and the same validated broker/retention support.

1. **Start through real delegation admission.** Construct the actual
   `GroupProcessStreamLaunchV2` from explicit fixture inputs and fresh nonce.
   The real daemon reserves transport generation, claims the broker root and
   performs native delegation admission. The provisioned shell prints nonce start/tail lines
   with CRLF around a one-second sleep. Child lifetime is bounded to five seconds
   and launch authority to ten seconds. No image/host grant is invented.
   Its fixed script uses absolute `/bin/sleep`; the shell's digest does not
   attest this subsequently executed child binary or a complete filesystem.
2. **Retain every outcome.** `Ready` retains the complete owner/reference;
   `CleanupRequired` retains owner plus optional reference and remains failure;
   `Rejected` fails the prerequisite. A single test carrier retains post-spawn
   authority and errors even when later assertions fail. No `Result` error
   discards a cleanup owner.
3. **Adopt and read through smux.** Use exact epoch/revision/child-incarnation
   fences for full-bundle adoption. Only normal smux polling/capture reads the
   helper stream. Require fresh start and tail markers, explicit EOF, unchanged
   complete transfer and no retained read error within eight seconds/400 turns.
   EOF alone is not process exit or terminal proof.
   With the real owned pane installed, production `smux_server_dispatch` must
   authenticate before refusing stop. Text, command and paste input must refuse
   before queue mutation. These are in-process real-owner guard checks, not
   network acceptance.
4. **Require actual collected terminal evidence.** For a ready helper, wait at
   most eight seconds/160 turns for `group_process_stream_terminal_v2` to validate
   the durable broker receipt: terminal, leader reaped, empty tree and zero active
   processes. Never mint a `GroupedActionLeaseV1` or treat a no-child receipt as
   positive execution evidence.
5. **Clean helper authority once.** Invoke actual smux close once. It must return
   pending/false while committing `helper_cleaned_awaiting_release` and retaining
   the same pane/bundle/ref metadata. A second close must remain pending with
   unchanged state and revision; its committed flag takes the source's one-shot
   branch that skips further native cleanup. Canonical ref validation must report
   retirement. No syscall-counter instrumentation is claimed.
   The same actual authenticated-dispatch stop refusal is required again after
   helper cleanup, while host-release authority remains retained.

An unadopted `CleanupRequired` outcome may attempt the existing canonical cleanup
once; its no-child/cancellation result remains failure evidence. Errors retain
the complete carrier and durable broker root for recovery. If terminal proof is
missing, cleanup is not attempted and ownership remains retained. The fixture
never deletes evidence or retries successful cleanup as if it were idempotent.
An unadopted failed handoff may request one bounded broker cancellation turn
before waiting for collected proof; it never uses a PID fallback.

The cleaned pane still awaits a real verified host reap/release acknowledgement;
that production API is absent. No reservation is marked released, no server bind
route is enabled and no Windows support is implied. References are process-local
and cannot be restored from saved PID/generation fields after restart. Actual
execution and owned cleanup remain unqualified until this authored scenario runs
on admitted artifacts and delegated resources.

Actual spawn, adoption, capture, terminal-proof and direct cleanup error reasons
are retained as bounded diagnostics (1024 UTF-8 bytes per reason, control
characters flattened). Fixture request environment contains no credentials.
The adopted smux close API returns only a pending boolean; it does not expose
its native cleanup error reason, and the fixture never repeats native cleanup
to obtain one. That diagnostic limitation remains explicit.
