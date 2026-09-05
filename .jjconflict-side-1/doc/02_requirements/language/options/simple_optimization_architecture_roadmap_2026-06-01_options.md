# Simple Optimization Architecture Roadmap Feature Options

Date: 2026-06-01

Scope: Lane E persistent SMF profile (`.sprof`) work from
`doc/01_research/compiler/optimization/perf/simple_optimization_architecture_roadmap_2026-06-01.md`.
These are requirement options only. Final requirements must be selected before
implementation.

## Option A: Minimal Durable Hotspot Profile

Persist only the profile facts already consumed by tiered JIT hotspot planning:
function identity, call count, hotness threshold state, selected tier, deopt
count, and safe-deoptimization fact status.

Pros:
- Smallest schema and implementation surface.
- Directly validates the existing JIT hotspot path.
- Lower risk of stale profile data changing behavior.

Cons:
- Does not cover provider history, branch ratios, loop ranges, or migration
  confidence beyond exact identity.
- Limited value for LLVM PGO, BOLT, and algorithm-provider decisions.

Effort: Medium.

## Option B: Full Lifecycle `.sprof` V1

Persist function profiles, branch/loop summaries, inline-cache stats,
provider-selection history, JIT tier transitions, and migration confidence
records.

Pros:
- Matches the full roadmap model.
- Gives compiler, runtime, provider, and optimize-app lanes one shared profile
  source.
- Creates a stable base for migration and long-term optimization feedback.

Cons:
- Larger schema review and more test fixtures.
- Higher risk of premature fields that are not yet consumed.
- Requires stricter versioning and corruption behavior from the first slice.

Effort: Large.

## Option C: Schema-First No Runtime Writes

Define the `.sprof` schema, migration report format, and optimize-app inspection
flow, but defer runtime writer/loader integration to a later implementation
slice.

Pros:
- Unblocks design and system-test review without touching interpreter hot paths.
- Makes migration and safety semantics explicit before data is written.
- Easy to split across parallel agents.

Cons:
- Does not deliver persistent profile speedups by itself.
- Requires a follow-up slice for actual profile collection and consumption.

Effort: Small to Medium.

## Selection Needed

Choose one feature option before final requirements are written. Unchosen
options should be deleted rather than archived.
