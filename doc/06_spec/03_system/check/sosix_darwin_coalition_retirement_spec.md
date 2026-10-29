# Darwin kernel coalition retirement

Source: `test/03_system/check/sosix_darwin_coalition_retirement_spec.spl`.

Runs real temporary LaunchAgents and a native C fixture. Session, group, and
double-fork escapes must remain kernel coalition members after leader exit or
kill. A post-census fork must force another retirement pass. A stale audit-token
PID version, the caller's coalition, and an unknown coalition must be rejected.

The three named fixtures require independent `NOTE_REAP` evidence. A separate
unreaped zombie proves that task-exit counters do not establish reaping. Generic
V4/reap capability remains unclaimed.

Required host: macOS GUI launchd domain, C compiler, Python plist encoder.

Validation: one native-backed SSpec executed and passed with no skips/drops on
Darwin 25.5.0 using the designated P1 diagnostic runtime. This is not P2 release
qualification.
