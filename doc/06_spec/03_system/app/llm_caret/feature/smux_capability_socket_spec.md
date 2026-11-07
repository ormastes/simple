# Actual compiled smux capability socket client

Source: `test/03_system/app/llm_caret/feature/smux_capability_socket_spec.spl`.
Shared support: `test/helpers/smux_owned_process_fixture.spl`, imported through
the repository's existing `test.helpers.*` convention.
Status: **AUTHORED_UNRUN**. No build, native run, socket test or docgen executed.

Run once in a fresh isolated admitted Linux test process with real native
delegation and group cleanup support. `SMUX_SOCKET_TEST_CONFIG` must name an
absolute regular no-follow strict SDN file with exactly nine fields:

| Field | Explicit trusted test-admin input |
|---|---|
| `root` | Fresh empty private broker directory |
| `brokerProgram` | Absolute regular no-follow compiled stream broker |
| `brokerDigest` | Expected broker SHA-256 |
| `smuxProgram` | Absolute regular no-follow compiled hosted smux client/server |
| `smuxDigest` | Expected smux SHA-256 |
| `delegatedCgroupPath` | Actual delegated writable cgroup-v2 parent |
| `memoryLimitBytes` | Explicit fixture memory budget |
| `snapshotDigest` | Actual fixture snapshot identity |
| `cacheIdentity` | Actual fixture cache identity |

The shared support validates exact keys/types/digests, both executable hashes,
fresh-root emptiness and actual current-UID/mode-700 directory privacy through
bounded absolute GNU `stat`/`id` oracles. C/POSIX locale and trusted path ancestry
are mandatory. The fixture does not mkdir, chmod, resolve executable symlinks,
build artifacts, invent delegation or create a production HostHelperLease.

1. `smux_capability_fixture_start` generates fresh nonce/token, atomically
   creates the private owner file with explicit mode 600, verifies actual type,
   mode and UID, then starts the compiled `--serve-owner-file` process through
   the real owned group profile. Helper lifetime is bounded to 45 seconds and
   launch authority to ten seconds.
2. Bounded publication reads require the original nonce/token, a valid
   OS-selected loopback endpoint, a positive diagnostic child PID and continued
   mode-600 protection. The canonical reference PID belongs to the broker and
   is deliberately not equated to the owner file's smux child PID. No token is
   sent before the complete protected publication validates.
3. `smux_capability_fixture_request` starts separate real compiled `--request`
   processes with five-second/16-KiB bounds. Correct-token capability discovery
   must exit zero and pass the production strict decoder with both installed
   binding/CoreMux flags false. Wrong-token query must exit nonzero with an
   unauthorized response; bind-existing must exit nonzero with the exact
   unsupported/refused schema; fresh legacy list must still exit zero.
4. `smux_capability_fixture_stop` uses the authenticated compiled stop request,
   then reads only this fixture server's stdout until explicit EOF. No other
   helper reads that reference and no agent pipe reader is introduced. Captured
   stdout is discarded, never logged. Credential-bearing diagnostics redact the
   token and remain bounded.
5. The common owner waits for actual durable group terminal proof, then attempts
   canonical cleanup once. EOF is not exit proof. Missing/failed startup or stop
   retains the exact owner and optional reference, requests one bounded broker
   cancellation turn where available, and preserves terminal/cleanup errors.
   Unknown endpoints never trigger port scanning, raw-PID cleanup or guessed
   authentication. `CleanupRequired` and no-child proof remain failure/cleanup
   evidence, never positive server execution.

The single retained test carrier survives post-spawn assertion failure. Neither
successful helper retirement nor the private publication proves Container
attachment, runtime readiness, host authorization or capacity release. Request
process pathname/hash checks are not pinned executable authority. Native source
dependencies must be integrated and qualified before execution; this authored
fixture is not passing socket evidence.
