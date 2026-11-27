# Darwin trusted snapshot runner

This acceptance contract applies only to the explicit
`trusted-snapshot-group` profile. It does not qualify BuildRunner V4.

| Requirement | Manual action | Expected result |
| --- | --- | --- |
| REQ-DARWIN-SNAPSHOT-001 | Query the native runner capabilities. | Snapshot and process-group retirement are available; immutable executable and complete descendant tree are false. |
| REQ-DARWIN-SNAPSHOT-002 | Request `sealed-v4` with a child that would create a marker. | Reject before executable acquisition or spawn; marker absent. |
| REQ-DARWIN-SNAPSHOT-003 | Launch a locally compiled Mach-O fixture with an argument containing spaces, explicit cwd, and environment. | Exact independent stdout/stderr and exit 17. |
| REQ-DARWIN-SNAPSHOT-004 | Launch a TERM-ignoring fixture with a short deadline. | Escalate to KILL, reap the leader, retire its group, return timeout 124. |
| REQ-DARWIN-SNAPSHOT-005 | Launch a fixture producing 10,000 bytes with a 128-byte retention bound. | Drain to EOF, preserve exactly 128 bytes, exit 0. |
| REQ-DARWIN-SNAPSHOT-006 | Launch a local fixture with TMPDIR set to `.` and a different child cwd. | Resolve the snapshot path before cwd changes; exact capture and exit 17. |
| REQ-DARWIN-SNAPSHOT-007 | Supply a FIFO as the executable without starting a writer. | Reject as nonregular with exit 125 without blocking in open. |

Run `sh scripts/check/check-sosix-darwin-snapshot-runner.shs` on macOS.
Other hosts return explicit unavailable status 77. The SSpec acceptance calls
this native check through the standard process facade and asserts its result.
Its native fixture exercises real macOS process behavior; it does not infer
support from source text or a different operating system.

The snapshot requires trusted processes sharing the UID and trusted directory
ancestors. Children may leave the process group with setsid/setpgid. Neither
those children nor a same-UID pathname attacker are contained by this profile.

## Native invocation

Build the standalone executable once and invoke the compiled artifact:

```sh
mkdir -p build/sosix
cc -std=c11 -O2 -Wno-deprecated-declarations \
  src/runtime/tools/sosix_darwin_snapshot_runner.c \
  -o build/sosix/darwin-snapshot-runner
build/sosix/darwin-snapshot-runner --capabilities
build/sosix/darwin-snapshot-runner --profile trusted-snapshot-group \
  --cwd /private/tmp --wall-ms 1000 --output-limit 4096 -- /absolute/locally-built-tool argument
```

The runner inherits the caller's environment, supplies empty stdin, keeps stdout
and stderr separate, and returns the child's exit status. Timeout returns 124;
provider errors return 125; invalid or unsupported profile returns 64. Child
exit 124/125 is consequently ambiguous in this CLI, which is not a structured
V4 receipt interface. A caller requiring typed outcome distinctions must not
use this command as a substitute for the strict ABI.

Only locally built Mach-O fixtures have qualified snapshot execution. Copied
Apple platform-signed system tools are not supported by this evidence:
independent review observed `/bin/echo` terminate with SIGKILL (137) after
copying. Executable-relative library/resource lookup may also change when a
tool runs from its temporary snapshot directory.

## Executed evidence (2026-10-29)

TDD RED: the native acceptance initially failed because the runner C source
did not exist. After implementation the initial five native acceptance scenarios
passed on arm64 macOS. Independent review then reproduced a FIFO preflight
hang and relative TMPDIR failure across child cwd changes. Regression tests
cover both fixes. The final SSpec reported `executed=7 passed=7
failed=0 skipped=0`, using the explicitly selected P1 bootstrap diagnostic
interpreter (`ddd5aa` SHA prefix), not a pure-Simple qualification. No P2
rebuild occurred. Strict immutable-image and escaped-descendant support remain
unavailable and were not counted as successful provider features.
The [captured evidence](evidence/darwin_snapshot_runner_20261029.txt) records
the exact command, full runtime digest, test output, and raw local log digest.
