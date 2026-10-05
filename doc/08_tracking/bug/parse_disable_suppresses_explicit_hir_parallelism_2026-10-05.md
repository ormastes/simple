# Parse disable suppresses explicit HIR parallelism

ID: `parse_disable_suppresses_explicit_hir_parallelism_2026-10-05`
Status: OPEN. Priority: P1. Native repair admission pending.
Canonical `bug_db.sdn` registration belongs to the root session; this isolated
candidate does not modify the shared database.

## Observed

On Windows on 2026-10-05, the live P3/P4 workers 11308 and 15836 each had one
thread while their parents had requested `--threads 40`. Root observations
recorded CPU time increasing from approximately 249/500 seconds to 564/815
seconds: active computation, not evidence of a blocked or dead process.
The host exposes 80 logical processors. Read-only Windows API queries returned:

| Query | Worker 11308 | Worker 15836 |
|---|---|---|
| GetProcessGroupAffinity | groups 0 and 1 | groups 0 and 1 |
| Thread count | 1 | 1 |
| Thread ID | 5176 | 20720 |
| GetThreadGroupAffinity | group 1, mask 0xffff | group 1, mask 0xffff |

`GetActiveProcessorCount` returned 64 for group 0 and 16 for group 1. Mask
`0xffff` therefore covers every active logical processor in group 1; it is not
proof that BIOS or process configuration limits the host to 16 CPUs. No
affinity, power configuration, running process, or firmware setting was changed.

The active pure producer has SHA-256
`d1e7c13bb00511802e7a719102d6bacb4c67a32cdafc903290fa2040ab084158`, built
from `81bfe2e000da3fd9f5d2dc086fc6d78598346756`. Its `bootstrap_main.spl`
internal `run src/app/cli/native_build_worker.spl` route directly calls the
compiled `cli_native_build_with_environment_variant_policy_v1`. The command
spelling does not imply interpreter staging or use of a Rust seed.

## Cause and bounded candidate

`native_build_hir_shard_count` in `src/app/cli/native_build_main.spl` returned
zero whenever `SIMPLE_PARSE_SHARDING=0`, including when
`SIMPLE_HIR_SHARDING=1` explicitly requested HIR workers. The parse disable used
for the [directory-root validator bug](parse_closure_directory_root_validation_2026-10-05.md)
therefore also disabled HIR process parallelism. Streaming HIR lowering uses a
serial source loop when it is not a shard; its existing shard branch claims
work through `hir_shard_begin`, performs a transaction, and publishes terminal
receipts. Codegen's requested job count does not parallelize that serial loop.

The candidate adds a pure policy selector: ordinary settings retain their
behavior; explicit HIR disable wins; parse disable remains an HIR disable by
default; only explicit HIR enable selects HIR-only admission. Before that route
spawns workers, the parent opens and validates the canonical published source
authority. Invalid identity fails before spawning and restores the prior worker
and warm-candidate environment. Child/cache guards, request-derived worker
count, memory admission, work queue, child-created cache records, recovery,
parent waits, and failed-aggregate handling remain in force.

This does not parallelize surface parsing. With parse warming disabled, HIR
children can each perform source/surface preparation before claiming modules;
replicated parsing and memory may offset the lowering benefit. Native evidence
must measure that cost. No speedup or memory improvement is claimed.

## Verification and constraints

Added SPipe cases to `test/01_unit/app/cli/native_build_shard_admission_spec.spl`
for explicit disable, unset/unknown values, parser disable plus HIR enable,
ordinary routing, and a 20-worker request ceiling. Added native fixture
`test/fixtures/native/hir_shard_optin/main.spl` with ten exact policy/count
checks. Native execution is UNRUN: the active producer does not contain this
candidate and must not be restarted merely to obtain a measurement.

Before repair admission, run the candidate with 20 requested jobs per task under
the shared global 80-job scheduler. Record exact producer/source identities,
actual child concurrency, valid-authority and malformed-authority results,
module claim/completion coverage, output equivalence, warm-cache reuse,
failure/cancellation containment, elapsed p50/p95, and peak/steady process-tree
RSS against the same serial fixture. A policy-only fixture cannot prove actual
20-worker execution. Do not enable this route on the current producer while
the directory-root validator blocker remains unqualified. No freeze fallback,
seed fallback, global hardcoded 20/80 compiler limit, or live build restart is
part of this candidate.
