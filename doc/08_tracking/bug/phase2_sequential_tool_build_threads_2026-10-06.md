# Sequential Phase2 tool builds discard the thread budget

Status: scheduler configuration repaired; real multi-thread sequential native
build validation pending.

The original full LLVM matrix exceeded its process-tree RSS cap while CLI and
test-runner closures built concurrently. Setting the thread budget to one
serialized the closures, but also hardcoded each native build to one thread.
The user's full-core request needs a separate concurrency decision.

`BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1` now serializes the closures and
passes the requested build thread budget to each. The default 2 preserves
existing scheduling; the fail-fast default is preserved. Invalid values fail
before work starts. Source, producer, runtime, caches, output identities,
timeout limits, RSS enforcement and qualification gates remain authoritative.

The already-running c6e6449 bootstrap lanes are frozen and do not include this
orchestration change. Use it in the next native verification matrix, record
the actual command-owner threads and memory receipt, and do not claim native
qualification from syntax/configuration validation.
