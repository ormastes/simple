# Stale stage2-native-cache.writer marker makes the next run fail, often silently

Date: 2026-10-23
Host: Windows MinGW UCRT lane on release_phase3

## Observation

After a stage2 native-build is killed (timeout or kill), it leaves a
`stage2-native-cache.writer` marker. The next run then either:

1. Exits 1 silently within about a minute with no error text (seen in
   bootstrap run 12 and manual runs B and D), or
2. Aborts with `bootstrap-cache-error: active or unresolved writer ...
   stage2-native-cache.writer`.

The silent variant prints nothing explaining the failure, so the cause is
only found by inspecting the cache directory.

## Expected

A dead writer must be detected (PID liveness check on the PID recorded in
the marker) and then either reported with the marker path and PID, or
reclaimed. A non-zero exit must always carry an error message.

## WORKAROUND

Move the cache and its `.writer` marker aside, or run on a copy of the cache.

## Suggested direction

- Record writer PID (and start time) in the marker; on startup, if the PID is
  not alive, reclaim the marker and log that it was reclaimed.
- If the writer is alive or liveness cannot be determined, fail with the
  existing `bootstrap-cache-error` text rather than a silent exit 1.
- Find why variant 1 skips the error print (silent exit path).
