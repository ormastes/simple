# Windows bootstrap seed fingerprint latency under low headroom

Status: observed performance blocker; cause not isolated. No integrity bypass
or source repair proposed by this report.

Frozen source: `6e03930143983a5c9861321f67aff300b07f16ed` in
`D:/dev/simple-node-attribute-bootstrap-20261106`. Canonical attempt 10 uses
Git Bash, Windows MSVC/LLVM 23, cached Rust/native outputs and one build worker.
The log entered `fingerprint-start` at approximately 2026-11-06 20:40:53 UTC.
At 20:50:15 it still had no completed fingerprint event. A single process
inspection showed three active xargs/sha256sum lanes hashing Rust Windows
dependency inputs; individual sha256sum processes had advanced since the
preceding snapshot. This establishes active hashing, not a deadlock.

The host had approximately 3.6 GiB free physical memory and 33 GiB free commit
headroom shortly before this phase. No disk-throughput, hard-fault or cache-hit
measurement was collected, so memory pressure is context, not a proved cause.
This is not a MIR/codegen failure. Vendored source was not reviewed or counted
as owned code; process arguments only identified the fingerprint input family.

The owner is `bootstrap-from-scratch.sh`'s `seed_inputs_hash pre` call before
seed-stamp validation. The source fingerprint protects seed/runtime identity;
do not skip dependencies or reuse a stale stamp to make the run appear faster.
Future investigation should measure fingerprint elapsed time, bytes/files,
disk throughput and hard faults on the same frozen inputs with adequate versus
constrained headroom. Any cache must preserve content-based admission and detect
changed inputs. An admitted Stage 2 continuation may avoid this seed phase only
through the existing verified-parent route.

Evidence: `build/node-attributes-qualification/bootstrap-attempt10.log` in the
frozen worktree. The preceding attempts reused 1,592 native modules and rebuilt
two, so this setup cost materially delays the small incremental compilation.
