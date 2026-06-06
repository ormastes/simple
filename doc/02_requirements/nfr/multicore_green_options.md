# Multicore Green NFR Options

Date: 2026-06-06

Scope: non-functional requirements for Simple host and SimpleOS green-thread
parallelism, profile evidence, and API hardening.

These are options only. Final NFRs require user selection. Unchosen options
should be deleted, not archived.

## Evidence Integrity Gate

Targets:
- No report, guide, or release note may claim Go-like M:N behavior unless the
  row has `used_runtime_pool()` or SimpleOS scheduler evidence.
- Cooperative green rows must remain classified as current-carrier,
  non-CPU-parallel work.
- Profile reports must include OS-thread, cooperative-green, multicore-green,
  C pthread, Go goroutine, large-fanout, RSS, artifact-size, and Go-vs-C stress
  evidence.

Pros:
- Prevents misleading performance claims.
- Low implementation risk.
- Matches the current profile-contract test direction.

Cons:
- Does not set a strict speed target.
- Can pass even when Simple is slower than Go or C.

Effort: Small.

## Performance Parity Budget

Targets:
- Simple native OS-thread and multicore-green rows must stay within documented
  ratios of Go goroutine and C pthread baselines for the checked-in smoke
  profile.
- The large-fanout stress section must prove Go beats one-pthread-per-task C, so
  the benchmark distinguishes M:N scheduling from OS-thread fanout.
- Any miss against the ratio budget must create or update a measured blocker
  under `doc/08_tracking/bug/`.

Pros:
- Directly addresses the C/Go parity goal.
- Forces profile-script changes to carry numeric evidence.
- Keeps weak benchmark comparisons from becoming API claims.

Cons:
- Ratios can be host-sensitive.
- Requires recurring profile refreshes when the benchmark or runtime changes.

Effort: Medium.

## API Stability And Misuse Diagnostics

Targets:
- Public APIs keep meaningful names: `thread_spawn`,
  `thread_spawn_with_args`, `cooperative_green_spawn`,
  `cooperative_green_spawn_value`, and `multicore_green_spawn`.
- Numbered aliases remain rejected by `simple check` with actionable
  diagnostics.
- User code should not need C/Rust rewrites to benefit from optimizer or runtime
  improvements.

Pros:
- Protects user-facing compatibility.
- Matches the user's request to avoid numbered names.
- Keeps Simple as the primary language surface.

Cons:
- Requires compatibility review whenever runtime ABI names change.
- Does not by itself improve scheduler throughput.

Effort: Small.

## SimpleOS Hardware Proof Gate

Targets:
- Hosted SimpleOS specs must prove logical green scheduling, channel wake,
  remote enqueue/IPI state, per-CPU dispatch, and topology growth.
- Live QEMU evidence must be required before claiming hardware/AP behavior.
- Context-switch handoff must remain a blocker until a live guest proves it.

Pros:
- Prevents host-only tests from being misreported as kernel proof.
- Gives a clear path for SimpleOS green-thread hardening.
- Separates current carrier-dispatch proof from final hardware handoff.

Cons:
- Opt-in QEMU tests are slower and environment-sensitive.
- More artifacts must be kept current across kernel scheduler changes.

Effort: Large.

## Selection Needed

Select one or more NFR scopes by name before final NFRs are written. Evidence
Integrity Gate and API Stability And Misuse Diagnostics are low-risk defaults;
Performance Parity Budget and SimpleOS Hardware Proof Gate add stronger
release-blocking evidence.
