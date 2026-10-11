# Item 5 app runner watchdog precondition

The app receipt runner required executable permission on the process-tree RSS
watchdog, but Git tracks that Perl source as mode 100644 and every invocation
uses `perl "$watchdog"`. A clean Linux checkout therefore rejected the runner
before any app execution. Require readability, matching the actual invocation.

The runner owns independent bounded child sessions. Reject an inherited
bootstrap session before staging artifacts, with an explicit direct-launch
diagnostic. Do not unset an inherited ownership contract or silently change
watchdog session mode. Callers must invoke this collector directly rather than
wrapping it in another new-session watchdog.

This changes runner preflight only. App output, identity, event receipt, RSS,
quiescence and performance validation are unchanged. The frozen Item 5 candidate
is not modified; any external diagnostic adaptation records both byte hashes
and cannot constitute canonical admission. Actual five-app qualification remains
pending the new compiler and backend Hello gates.

## Focused verification

`sh scripts/check/test-item5-app-runner-preflight.shs` passed five cases on
Linux. It copies the real runner and helpers byte-for-byte, sets only the copied
watchdog's mode to 0644, and verifies their hashes again afterward. The ordinary
case proceeds past the helper gate and rejects a 65,537-byte invalid provenance
sentinel before staging. Four additional cases set each inherited session
variable individually, both nonempty and empty-but-set; all reject with the
specific direct-launch diagnostic. Each case asserts exit 1, no output directory
and no launch-canary marker. The canary exits 97 if invoked; it is not an app
success substitute. Result: five cases, zero output side effects, zero app
launches, unchanged helper bytes. This is preflight regression evidence only.
