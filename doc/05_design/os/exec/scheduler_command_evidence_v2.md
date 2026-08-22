# Scheduler-owned executable command evidence V2

## Contract

The scheduler is the only owner allowed to attach an executable command to an
execution observation. After validating and independently copying
`ExecutableLaunchArgumentsV1`, authenticated adoption passes that exact value
to `process_execution_observation`; architecture adapters never populate the
evidence record from a command supplied after execution.

V2 evidence contains `command_observed`, `executable_path`, and the effective
`argv`. Empty caller argv is normalized by the existing launch validator to
`[path]` before adoption. Legacy three-argument observations remain available
for compatibility but store `command_observed=false`, an empty path, and an
empty argv. The V2 consumer rejects those rows.

The x86_64, ARM64, and RV64 authenticated adapters preserve their existing
entrypoints. New/extended launch-aware paths return a one-shot evidence token.
They atomically compare the adapter's bounded expected command against the
scheduler-retained command after reap. A mismatch consumes the terminal row
under the observation mutex and returns no token; unknown, not-exited, and
not-reaped rows remain unchanged. This prevents both provenance substitution
and leakage of the fixed 256-row observation table.

## Ownership and bounds

- Mutable observation state: the scheduler observation owner under one mutex.
- Boundary data: validated immutable value copies; the returned token is an
  opaque generation/nonce lease, not evidence itself.
- Path/string cap: 4095 payload bytes per C string.
- argv cap: 64 entries and 32 KiB, with the existing 64 KiB combined launch
  cap enforced before scheduler adoption.
- Observation cap: 256 live rows; stdout and stderr remain independently
  bounded at 64 KiB.

Command comparison is O(total bounded argv bytes), performs no work while the
expected command is malformed, and does one mutex acquisition for lookup,
comparison, and delivery/tombstone. Evidence consumption transfers the two
retained command values into the immutable result while clearing the slot; it
does not reconstruct or reparse a shell command.

## Verification

`test/01_unit/os/kernel/scheduler/process_execution_observation_spec.spl`
covers exact command retention, empty/invalid expected input, V2 rejection of
legacy rows, mismatch tombstoning, stale/replay rejection, interleaved handles,
capacity reuse, and stdout/stderr memory bounds. Runtime execution awaits an
admitted pure-Simple `bin/simple`; the Rust bootstrap is not a substitute.
