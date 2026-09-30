# Bug-linked workaround implementation evidence

STATUS: TEST_BLOCKED — implementation and executable scenarios authored;
general self-hosted runner qualification and release verification remain open.

Source lane: `D:/wk-workaround-tags-20260930`, base `0814a6dfa5e`.
Remote integration has advanced separately; this lane does not modify running
bootstrap producer sources or claim main/release landing.

## Runtime observation

Inspected the retained compiler at
`D:/dev/simple-windows-stage2-finish-existing-20260929/build/retained-stage2-83a7-attempt2/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe`.
Its actual SHA256 is
`83a7f5f163c27308c8d2c35748dac75af0f210dcd62f51998ff2e8d5f6493668`,
matching adjacent `stage2-provenance.receipt` and `stage2-sanity.receipt`.
The provenance identifies a pure-Simple Stage 2 trust root; sanity says pass.
The isolated `--help` diagnostic exited 1 with no stdout/stderr. This is not
a supported general runner or an executed test result. A separate `test --help`
probe also exited 1 without output. No Rust seed was used.

The repository's minimal-bootstrap composition guide requires an admitted
general runner for SPipe/docgen. Pending commands are:

```
<admitted-runtime> test test/03_system/app/bug/feature/bug_linked_workarounds_spec.spl
<admitted-runtime> test test/02_integration/app/bug_workaround_store_spec.spl
<admitted-runtime> check src/compiler
<admitted-runtime> check src/lib
<admitted-runtime> check src/app/mcp
<admitted-runtime> check src/app/simple_lsp_mcp
```

Also pending: required MCP runtime/native smokes, SPipe generation/manual review,
warm query latency measurement, branch coverage evidence, and release gates.
No passing counts, performance improvement, or release readiness are inferred.

Static checks completed once after source review: `git diff --check` passed;
`scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` both
reported `STATUS: PASS`; the staged check covered an empty staging area.
The `doc/06_spec` executable-spec count was zero. These are structural checks,
not execution evidence for the newly authored `.spl` scenarios.
After staging all 25 owned files, the staged env guard also passed on the actual
change. Normal local commit hooks examined all 25 text files and passed without
bypass. This does not establish runtime verification or release admission.

## Source review

The native-build parent calls one incremental coordinator. Its worker marker
excludes recursive workers, and shard entrypoints do not import the coordinator.
Ordinary bug queries join stored records and current BugDatabase state; they do
not call source discovery or Git. The SOSIX seam forwards existing bounded
reads/processes, locks, and atomic publication without new runtime externs.
Refresh reloads after taking the writer lock, parses the whole replacement
batch, validates canonical bug IDs, checks HEAD stability, and publishes once.
Malformed batches preserve previous bytes. Missing/changed revision coverage
is explicit. Fullscan alone enumerates tracked plus nonignored untracked files
or repairs index corruption. Queries always state current checkout freshness
unchecked; they do not label historical completeness as live branch coverage.

Limits: the existing no-follow reader protects the final component, not ancestor
replacement races; Git/source changes are not globally frozen during indexing;
nonempty canonical bug WAL requires checkpointing before validating linked IDs.
No mtime-only content cache is used. The index reflects a refresh snapshot,
and read-only queries explicitly name its revision and freshness boundary.
