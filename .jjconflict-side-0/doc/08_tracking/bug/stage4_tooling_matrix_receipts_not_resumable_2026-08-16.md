# Stage 4 tooling matrix receipts were not resumable

## Status

Claimed by `/root/lib_root_triage` for the scoped Phase 4 bootstrap recovery
after ownership transfer from `/root/sweep_planner`.
Stage 3 provenance files are explicitly outside this bug's ownership.

## Reproducer

The preparatory `stage4-tools-only.sh` linked one anonymous output and wrote a
receipt whose smoke field names did not match the typed
`ToolingLinkReceiptV1` contract.  The bootstrap phase verifier truncated its
summary on every invocation, so an interrupted verification reran already
green work.  No production runner froze the approved CLI, MCP, and LSP-MCP
entries or emitted one durable receipt per tool.

## Root cause

The tools-only linker boundary and the phase scheduler were developed as
separate preparation.  They had no deterministic matrix identity, atomic
per-row state, validated PASS reuse, approved-tool identity, or explicit
`BLOCKED_UPSTREAM` and `UNSUPPORTED` terminal semantics.

## Fix contract

- Freeze the CLI, MCP, and LSP-MCP tool IDs and entry paths.
- Bind every row to the admitted Stage 3 manifest and exact tool journal.
- Publish named outputs and canonical `ToolingLinkReceiptV1` fields atomically.
- Require both `compiler_sources_compiled=0` and
  `stage4_compiler_files=0`.
- Resume only when the matrix identity is byte-identical, and skip a PASS only
  while its receipt, log, output, and input fingerprints still validate.
- Terminalize unavailable optional capabilities as `UNSUPPORTED` and missing
  required predecessors as `BLOCKED_UPSTREAM`; neither is a false PASS.
- Keep Rust-seed orchestration and diagnostic inventories outside Stage 4
  acceptance.

## Verification plan

Before execution, the final reviewer receives the exact owned file set and
focused commands.  Verification is limited initially to shell syntax and one
fake-authority integration fixture covering successful publication, resume,
tamper invalidation, blocked input, and optional unsupported behavior.  No
bootstrap build is part of this bug's focused contract test.

Provider token usage and comparable completed-bug average: unavailable.

## Expanded acceptance matrix

The first resumable runner revision covered only the three linked artifacts,
the legacy aggregate test/lint/duplicate gate, MCP/LSP smoke, and one optional
Simple-core capability.  That was durable orchestration but not complete
Stage-4 tooling admission: required Linux compiler/library/tool checks and the
remaining public pure-Simple commands had no terminal rows.

The matrix now records separate required rows for compiler, library, MCP, and
LSP checks; compiler bootstrap and full unit tests; CLI/MCP/LSP help and
version; independent MCP and LSP stdio evidence; and the supported Linux
test-daemon, examples-check, fmt, fix, verify, SPipe doc generation,
native-build, security, build, run, and doc-coverage surfaces.  VS Code and
Electron dispatch/help are required, while their external npm-backed build
operations are optional and may be `UNSUPPORTED` only when the exact external
prerequisite is absent.  A supported optional operation that fails, crashes,
or times out now fails the aggregate.

Every row input fingerprint includes the matrix/config identity, admitted
compiler manifest, dependency receipts, relevant linked artifact/receipt, and
the content hash of its scripts, source roots, fixtures, or test tree.  Test
rows accept PASS only with `--assert-ran`, a parsed nonzero `Results:` count,
and zero failures.  Link journals must repeat the admitted source, producer,
backend, target, ABI, archive, and runtime hashes before publication.

The aggregate reports `stage4_compiler_files=0` only after every required row
passes and all three link receipts revalidate their journals and zero
compiler-source count.  It reports `unknown` while any required row is
missing, blocked, or invalid; a literal zero is never synthesized from an
incomplete matrix.

## Verification status

Implementation is present in the scoped working tree.  Per the Phase-4 freeze,
no shell integration test or bootstrap/tool build was run while this edit was
prepared.  Static review and the single focused fake-authority integration run
remain required before the runner can be used for admission.

## Acceptance audit blockers (2026-08-16)

The earlier 13-row support fixture is revoked as acceptance evidence.  Before
this runner can participate in a Stage 4 admission, a new scoped change must:

- resolve the reviewed shell source/syntax mismatch and re-freeze exact hashes;
- include explicit `check` rows for compiler, lib, MCP, and LSP plus compiler
  bootstrap and full compiler tests;
- give CLI, MCP, and LSP separate help/version receipts, and give MCP and LSP
  their correct executable dependencies and independent stdio protocol smokes;
- bind the admitted manifest, every compile journal, compiler/runtime ABI,
  source and test content, and a task-specific PASS marker into reusable rows;
- report `stage4_compiler_files=0` only after every required link receipt is
  validated; otherwise the aggregate is `unknown`;
- add required Linux check, examples, fmt, fix, verify, SPipe doc generation,
  native-build, security, build, and run rows; and
- terminalize VS Code and Electron explicitly as optional PASS or UNSUPPORTED,
  never by omission.

No old green support check may be rerun unchanged.

## Narrow recovery freeze (2026-08-16)

The current static snapshot has 49 terminally modeled rows.  It adds disjoint
compiler bootstrap, compiler-core, non-bootstrap compiler, and exact
`format_fixed` regression shards; explicit lint and duplicate help/focused
rows; independent MCP protocol/focused and LSP protocol/log-mode rows; and
per-row pre/post frozen source identities.  Tool link receipts distinguish the
canonical manifest framing hash from the manifest file hash and prove that the
approved entry source occurs in the journal unit closure.

Two required rows remain deliberately fail-closed:

- `mcp_stdio_integration` is `BLOCKED_UPSTREAM` with status
  `protocol-root-contract-not-accepted`.
- `lsp_stdio_integration` is `BLOCKED_UPSTREAM` with the same status.

Those rows must not PASS until static review accepts the staged protocol-root
wrapper/config/hash contract.  Consequently a full matrix remains `BLOCKED`,
and `stage4_compiler_files` remains `unknown`, even if the three tool links are
valid.  The integration fixture now models zero/missing/failing test summaries,
target-verdict omission, wrong focused count, essential-runner dependency, and
disjoint no-rerun manifests, but it has not been executed in this freeze.

Remaining verification is intentionally external to this edit: shell syntax
review, one focused fake-authority integration run, and review/acceptance of
the two stdio protocol-root rows.  No build, tool command, or test was executed
while preparing this recovery snapshot.

## Deferred after narrow fail-closed review

This snapshot is support infrastructure, not a Stage 4 producer or admission
receipt.  Static review requires its modeled first-run distribution to remain
exactly 44 required PASS rows, the two named required stdio rows BLOCKED, and
three optional rows UNSUPPORTED.  Summary generation revalidates each receipt
against current inputs and retained command/log/marker evidence; any malformed
or drifted evidence is invalid, cannot admit, and cannot establish a zero
compiler-file claim.

The frozen identity includes the complete `src/app` tree as well as every
source/object row in each tool journal, so a non-entry helper outside the three
entry directories cannot retain a stale aggregate.  A resume identity mismatch
first replaces any prior summary with `overall=FAIL`, `admission_eligible=false`,
and `stage4_compiler_files=unknown`, then exits 2.  Task and link receipts require
their exact V1 key sets, and the admitted receipt plus every manifest artifact
is rehashed before a row is counted.

Link publication no longer repeats compiler identity, tool help, or tool version
green probes.  Compiler identity is bound by the admitted manifest/receipt and
artifact hashes; the six explicit help/version rows own the executable probes.
Their link receipts therefore truthfully record both embedded smoke fields as
`false`.  The essential-tools shell gate also no longer fabricates a Simple
test count; only rows whose retained output has a nonzero parsed `Results:` and
per-target verdicts set `test_executed=true`.

The following functional work remains deferred and keeps real matrix execution
forbidden:

- accept and implement the MCP and LSP stdio protocol-root artifact contract;
- decide whether the broader essential-tools behavioral matrix should later be
  split into additional disjoint receipts; its assertions are distinct from
  the explicit help/focused rows, but it remains one canonical shell receipt;
- review exact LSP protocol framing and raw-response evidence independently;
- add link-time required-symbol, archive-provider, native-stub, and complete
  closure/object provenance gates beyond the current journal-byte checks;
- strengthen weak command rows, including complete SPipe doc output manifests,
  optional external capability identity, and runtime-specific help/verdict
  markers; and
- reconcile the production `stage4_tools_only_manifest_spec` with the final
  staging/output-name and receipt schema.

The fake-authority fixture contains expected-exit, exact row-distribution,
source-drift, and receipt/log/command/marker tamper cases.  They remain
unexecuted until the final reviewer returns `PASS_FOR_TEST`; passing that
fixture would still authorize only the next scoped review, not a real Stage 4
matrix run.
