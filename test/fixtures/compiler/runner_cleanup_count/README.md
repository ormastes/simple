# Runner cleanup return count (#3077)

Run as a standalone POSIX executable with `sleep` on PATH. The fixture starts
one direct child, registers it with the real process tracker, invokes production
cleanup, verifies returned count 1 and no live child/tracked PID, then verifies
empty cleanup count 0. It registers no containers. Any observed surviving child
gets an additional cleanup attempt before a failure is returned.

Require exit 0 and `runner-cleanup-count: cleaned=1, again=0`. Missing `sleep`
is a failure, never a skipped/pass result. Object compilation alone does not
qualify process effects or counts. No fixture has been executed yet.
