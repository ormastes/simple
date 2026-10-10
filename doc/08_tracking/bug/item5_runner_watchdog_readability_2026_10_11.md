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
