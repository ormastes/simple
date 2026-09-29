<!-- codex-design -->
# Trusted Stage 4 deployment and phase verification matrix

Status: design support for `full_pure_simple_simd_bootstrap`

Requirements: REQ-SIMD-008 through REQ-SIMD-012 and REQ-SIMD-014..015; NFR-SIMD-006 through NFR-SIMD-008 and NFR-SIMD-011.

This plan supplements the main detail design. It defines the bootstrap, cached-tool deployment, rollback, and per-phase verification contract. It does not admit the current host state or authorize a phase transition by itself.

## Trust boundary and current blocker

The only release authority is an immutable, receipt-admitted Stage 4 candidate. A Rust seed, a phase-1 temporary deployment, a raw `.spl` entrypoint, a binary selected by `PATH`, or a mutable compatibility directory is diagnostic evidence only.

The Windows publication transaction was repaired in the preceding lane; its
existence alone still does not admit an artifact. The next reported failure was
`could not resolve canonical Rust toolchain`. The 2026-09-08 Astra repair
normalizes native sysroot/CRLF output and records actual Windows `.exe` identities.
Its focused fixture test and live exact-tool launch pass; the historical causal
link remains inferred because the unchanged resolver also passed after normal
bootstrap PATH normalization in this shell. See
`doc/08_tracking/bug/bootstrap_rust_toolchain_sysroot_resolution_2026-09-08.md`.
The bootstrap owner must validate the changed candidate through the canonical
recovery path before any admission claim; no Stage 4 admission follows from the
focused toolchain result.

## Phase authority

| Phase | Admitted input | Permitted evidence | Promotion condition |
|---|---|---|---|
| 1, seed | Immutable Rust-authority generation and input stamp | Seed-specific bootstrap sanity and receipt-admitted focused tests | Published generation, compatibility-pointer transaction complete, hashes match |
| 2, receiver | Phase-1 manifest plus frozen source/runtime/tool snapshots | Receiver sanity and only commands declared supported by its manifest | Candidate and sanity receipts agree on SHA-256 and provenance |
| 3, admitted compiler | Stage-2 admission receipt consumed by `resume-stage3-from-admitted.sh` | Compiler/interpreter focused suites declared supported; unsupported tool rows retained | Stage-3 manifest and sanity evidence validate without source or runtime drift |
| 4, release candidate | Stage-3 manifest plus planner receipt consumed by `resume-stage4-from-admitted.sh` | Full compiler, interpreter, MCP, LSP MCP, SPipe, DevHub, Caret, and release-bound suites | Every required row passes against one frozen candidate identity |

Promotion is monotonic. A failed or unsupported required row cannot be replaced by a later-phase binary, a seed, or a source-mode wrapper. Stage 2 and Stage 3 results remain non-release evidence even when green.

## Frozen candidate identity

Before any Stage 4 verification, freeze these values in one immutable manifest:

- canonical candidate path and SHA-256;
- candidate provenance receipt path and SHA-256;
- parent Stage-3 manifest and planner receipt paths and SHA-256 values;
- source revision and tracked-dirty fingerprint;
- target triple, backend, compiler ABI, runtime ABI, and capability set;
- compiler, library, application, MCP, LSP MCP, SPipe, DevHub, Caret, test, and check-script tree hashes;
- isolated cache, output, home, and temporary roots;
- verification matrix schema/version and matrix hash.

Every row receipt repeats the candidate hash and matrix hash. Resume is allowed only when the configuration, matrix, row input fingerprint, and candidate identity are unchanged. Otherwise create a new matrix identifier; never reuse green evidence from the old candidate.

## Stage 4 tool construction

Use `scripts/bootstrap/stage4-tooling-matrix.shs` with an admitted compiler manifest and the CLI/MCP/LSP link journals. The existing matrix builds cached native outputs under:

- `build/stage4-tools/<matrix-id>_cli/simple`;
- `build/stage4-tools/<matrix-id>_mcp/simple_mcp_server`;
- `build/stage4-tools/<matrix-id>_lsp/simple_lsp_mcp_server`.

The tools-only linker must record each entry closure, parent compiler, runtime bundle, output hash, and link journal. Production wrappers may execute only these cached native artifacts after their hashes match the deployment receipt. They may not compile or run `src/app/mcp/main.spl` or `src/app/simple_lsp_mcp/main.spl` on demand.

The existing Stage 4 matrix already owns CLI/MCP/LSP linking, help/version checks, compiler/lib/MCP/LSP checks, essential tools, lint/duplicate checks, compiler tests, MCP/LSP unit and stdio tests, runtime smoke, native build, run, verify, and SPipe doc generation. Extend it with explicit `spipe_suite`, `devhub_suite`, and `caret_suite` rows before claiming REQ-SIMD-011. Each row must execute through the frozen Stage 4 CLI or its cached tool artifact and hash the selected test inventory in its input fingerprint.

## Phase-supported suite matrix

The implementation must generate a row for each cell below. `UNSUPPORTED` is valid only when the phase manifest lacks the command or required cached tool; its receipt must name the missing capability, owner, prerequisite, and exact resume command. A skipped or absent row is a failure.

| Suite family | Phase 1 | Phase 2 | Phase 3 | Phase 4 |
|---|---|---|---|---|
| Compiler check and focused bootstrap tests | receipt-admitted focused only | manifest-supported focused only | full supported compiler checks | full compiler checks and complete applicable compiler suites |
| Interpreter behavior and doctests | focused scalar/bootstrap fixtures | manifest-supported fixtures | complete supported interpreter suites | complete applicable interpreter and doctest suites |
| Simple MCP | launch admitted pure-Simple companion or explicit `UNSUPPORTED`; no raw-source substitute | same-phase cached companion protocol launch plus supported suite | same-phase cached companion protocol launch plus supported suite | cached native MCP check, unit, protocol, focused, and stdio integration |
| Simple LSP MCP | normally `UNSUPPORTED` | manifest capability decides | manifest capability decides | cached native LSP check, unit, log-mode, protocol, and stdio integration |
| SPipe plugin/SSpec | pinned plugin launch and focused parser/runner checks only if declared | phase-bound plugin launch plus supported runner/docgen | phase-bound plugin launch plus supported runner/docgen | actual pinned plugin launch, full applicable SPipe suite, feature SSpec, docgen, and zero-stub manual gate |
| DevHub | cached companion launch and supported suite or explicit blocker | cached same-phase launch and supported suite | cached same-phase launch and supported suite | actual cached launch plus full applicable DevHub suite through Stage 4 CLI |
| GitHub access through DevHub | real authenticated fixture read or blocker | real authenticated fixture read or blocker | real authenticated fixture read or blocker | independent live authenticated identity/capability and repository read |
| Jira access through DevHub | real authenticated fixture read or blocker | real authenticated fixture read or blocker | real authenticated fixture read or blocker | independent live authenticated identity/capability and known issue read |
| Confluence access through DevHub | real authenticated fixture read or blocker | real authenticated fixture read or blocker | real authenticated fixture read or blocker | independent live authenticated identity/capability and known page read |
| LLM Caret | cached companion launch and supported suite or explicit blocker | actual same-phase cached launch plus supported suite | actual same-phase cached launch plus supported suite | actual cached launch plus full applicable Caret unit/integration/system suite through Stage 4 CLI |
| Repository unit/integration/system/release test sets | phase-owned focused inventory | receipt-admitted inventory | all manifest-supported sets | all applicable sets, including release-bound `test test --whole --mode=interpreter` |

The inventory must be materialized before execution as a sorted manifest of exact test paths and hashes. Broad directory arguments are acceptable only when the receipt also records the resolved inventory, so later file additions cannot silently escape evidence.

For Phase 1 and Phase 2, the concrete fixed-row controller is
`scripts/check/check-bootstrap-phase-feature-matrix.py`; its operator contract
is `doc/07_guide/tooling/bootstrap_phase_feature_matrix.md`. It materializes
interpreter and native rows for `compiler`, `language_runtime`, `simple_mcp`,
`simple_lsp_mcp`, `t32_mcp`, `spipe_sspec`, `caret`, `slang`, and
`simd_db_web`, then separate live launches for Simple MCP, Simple LSP MCP, T32
MCP, the installed SPipe plugin, Caret, and Slang. An absent row is a failure.
An unavailable declared row binds the phase compiler and retains owner,
prerequisite, and exact resume argv without launching.

Every supported row repeats the selected artifact SHA-256, immutable generation,
provenance-receipt SHA-256, and admission-envelope SHA-256. The controller
rejects relative/PATH-resolved launchers, scripts, symlinks, an older Phase 1
tool, or a Phase 2 companion produced by another compiler generation before
launch. Each receipt also records the selected bootstrap job count and detected
CPU count. Neither phase is marked as release evidence.
Phase 1 additionally rechecks the current authority marker, absence of its
publication transaction, selected immutable generation stamp, and admitted
seed hash before and after each row; an internally consistent retained older
manifest cannot substitute for the current generation.

## Row receipt schema

Each command produces `PhaseVerificationRowV1` with exactly these fields:

`phase`, `suite`, `row_id`, `support_status`, `unsupported_reason`, `owner`, `resume_command`, `candidate_path`, `candidate_sha256`, `candidate_provenance_path`, `candidate_provenance_sha256`, `matrix_path`, `matrix_sha256`, `capability_set`, `command_argv_sha256`, `test_inventory_path`, `test_inventory_sha256`, `isolated_cache`, `isolated_output`, `isolated_home`, `isolated_tmp`, `started_at`, `duration_ms`, `exit_status`, `result`, `pass_marker`, `log_path`, and `log_sha256`.

`PASS` requires `support_status=supported`, an executed command, exit status zero, a suite-specific pass marker, and unchanged before/after identity snapshots. `UNSUPPORTED` requires no command execution and a nonempty reason/resume command. Upstream failure is `BLOCKED_UPSTREAM`, never `PASS` or `UNSUPPORTED`.

The phase summary is `PhaseVerificationMatrixV1`. It binds every row receipt and
counts required/pass/fail/unsupported/blocked rows. A phase's live coverage is
`PASS` only when its required live rows execute successfully. Complete
unsupported receipts preserve the compiler handoff audit; they do not make the
phase's live coverage, full feature matrix, or release verification green.

## Actual launch and authenticated access gate

The additional live controller is
`scripts/check/check-bootstrap-phase-live.py`. It is a bounded host test harness;
it does not become a Simple product runtime dependency, build/admit a compiler,
or authorize raw-source fallback. Run it after each producer phase has frozen
its compiler and permitted cached tool artifacts. Repeat for phase 5 against
the deployed artifact identities. Compiler/interpreter semantic checks and
complete component suites remain separately required; these eight live rows
supplement them:

`mcp`, `lsp_mcp`, `spipe_plugin`, `caret`, `devhub`, `jira`, `confluence`, `github`.

Each row must launch the exact artifact. Protocol checks require initialize,
initialized notification, tools/capability discovery, and a real read-only
operation against a known fixture. Caret uses local status/discovery; no message
delivery is part of sanity. SPipe binds the actual plugin executable and
manifest/tree digest; static plugin checks cannot replace execution.

DevHub provider reads are independent. GitHub must identify a known repository;
Jira must return a known issue key/id; Confluence must return a known page id and
valid content metadata. Authentication/configuration messages and empty search
results are insufficient. Successful fixture reads prove their resource scope;
current-user/capability claims additionally require real corresponding provider
responses. The current DevHub GitHub facade has no `api user` command, so that
identity subcheck remains explicitly unsupported until implemented; never
substitute a made-up command or generalize a repository read to full auth scope.

The controller accepts `BootstrapPhaseLiveManifestV1`: integer `phase`, compiler
path/SHA-256, and an `artifacts` map containing the exact cached artifact
path/SHA-256 and admission receipt path/SHA-256. Provider rows use the `devhub`
artifact. `resources` supplies the nonsecret Jira issue key, Confluence page id,
and GitHub owner/repository. The phase owner supplies
`BootstrapPhaseArtifactAdmissionV1` with phase, `status=ADMITTED`, artifact and
compiler SHA-256 values, and an existing evidence file path/hash. The live
controller consumes this authority; it must never fabricate it from mere file
existence or self-reporting output.

`BootstrapPhaseLiveReceiptV1` retains row/phase, compiler/artifact/admission/input
hashes, argv, actual process id, `launched`, status/reason, duration/exit/timeout,
bounded sanitized response assertions, and `resume_argv`. The enclosing phase
matrix adds owner, reviewer, prerequisite, capability/suite inventory and
isolated cache/output/home/tmp roots. Pre/post identity drift invalidates a row.
Missing credentials, fixtures, capabilities or admission cannot be PASS; retain
their exact prerequisites. Never store a token or issue/page body in a receipt.

For a frozen phase manifest and a fresh evidence directory, the command is:

```text
python scripts/check/check-bootstrap-phase-live.py --manifest <absolute-phase-manifest.json> --output <new-absolute-receipt-directory> --timeout 30
```

To resume one previously blocked row after its prerequisite is supplied, use
the receipt's exact `resume_argv`; the explicit command form is:

```text
python scripts/check/check-bootstrap-phase-live.py --manifest <absolute-phase-manifest.json> --output <new-absolute-receipt-directory> --row jira --timeout 30
```

Repeat only changed/failed row inputs. A different phase requires its own
manifest and evidence directory. Controller fixture tests prove fail-closed
classification only; they cannot admit live servers, plugin execution, external
provider access, phase promotion, or deployment.

## Deployment transaction

After Stage 4 verification freezes green evidence:

1. Acquire the existing deployment lock and verify the candidate, MCP, and LSP MCP hashes again.
2. Copy each artifact to a sibling temporary file under `bin/release/<triple>/`, set executable permissions, hash it, and atomically rename it into place.
3. Publish one deployment receipt binding all three source and deployed hashes, provenance, matrix summary, prior deployed hashes, and wrapper targets.
4. Probe the canonical wrappers with version/help and JSON-RPC initialize/tools-list requests. Record startup time, representative request latency, selected candidate hash, and maximum RSS.
5. Reject wrappers that reach a raw source entrypoint, a seed, a different triple, or an unhashed fallback.

The deployment receipt is incomplete unless all three artifacts are committed as one transaction. A partial deployment triggers rollback before any verification claim.

## Rollback proof

Before deployment, retain the prior files and their hashes in the existing recoverable pre-deploy location. Run `scripts/bootstrap/rollback-bootstrap-deploy.shs --dry-run <triple>` to validate the receipt and restoration target. After the new tools pass canonical-wrapper probes, exercise rollback in an isolated copied deployment root or the repository's rollback self-test; do not replace the verified live deployment merely to prove rollback. The rollback receipt binds the deployment receipt, restored artifact hashes, command, status, and log.

If a live rollback is required, execute the canonical rollback script once, verify all restored hashes against the pre-deploy receipt, and record that the new candidate is no longer deployed. Re-deployment then requires a fresh transaction and probes, while the immutable Stage 4 verification evidence remains valid only if its inputs did not change.

## Canonical command shapes

Commands below are templates; manifest and journal paths must come from admitted receipts, not guessed paths.

```text
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy

sh scripts/bootstrap/stage4-tooling-matrix.shs \
  --matrix-id=<frozen-id> \
  --compiler-manifest=<admitted-stage3-manifest> \
  --cli-journal=<cli-journal> \
  --mcp-journal=<mcp-journal> \
  --lsp-journal=<lsp-journal> \
  --scope=full

sh scripts/check/cert/redeploy_gate/redeploy_gate.shs \
  build/stage4-tools/<frozen-id>_cli/simple

sh scripts/bootstrap/rollback-bootstrap-deploy.shs --dry-run <triple>
```

The all-in-one bootstrap command is permitted only after the Windows publication blocker is resolved and its recovery transaction validates. Verification runs each unchanged acceptance command once. A failed row may enter at most three distinct fix/verify cycles; a green row is not rerun unless its recorded input fingerprint changes.

## Completion gate

This lane is complete only when the Stage 4 summary, deployment receipt, wrapper probes, rollback proof, performance receipt, requirement trace, direct-environment guards, and final verifier all bind the same candidate hashes. The final verifier must report `STATUS: PASS` before linear `jj` rebase and the already-authorized push.
