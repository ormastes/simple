# Core + MCP runtime qualification: execution blockers

Status: PARTIAL FIX, runtime qualification BLOCKED. Follow-up to draft PR #1989.

Inspected source: refreshed `origin/main`, commit `267b99c8c17`, in isolated sparse worktree `/tmp/simple-core-mcp-qualification-20260928`. No compiler build, cache deletion, commit, push, or CI dispatch was performed.

## Why the workflow cannot yet be switched safely

The existing Core + MCP workflow selects `src/compiler_rust/target/bootstrap/simple` for all four required source checks and MCP integration tests. That is bootstrap-seed evidence.

The existing `candidate.yml` is not an executable qualification recipe:

1. Its direct Stage 4 resume supplies neither scheduler lineage nor the Stage 4 binding. `bootstrap-from-scratch.sh:749` requires verified `SIMPLE_BOOTSTRAP_LINEAGE_ADMISSION` and its hash before proceeding. `resume-stage4-from-admitted.sh:74` additionally requires `SIMPLE_BOOTSTRAP_STAGE4_BINDING_SHA256`.
2. The documented supervisor path supplies lineage, but `bootstrap-strategy.sh:814` does not produce/export the Stage 4 binding. The only production writer found is `guard-existing-stage3-deploy.shs:221`; that separate direct-resume path does not supply scheduler lineage. An ordinary fresh runner has neither inherited authority.
3. Candidate provenance and continuation completion form a hash cycle. `stage4-candidate-provenance.shs:171` hashes the prepared continuation into the compiler provenance. `bootstrap-from-scratch.sh:5775` then calls `resume_stage4_finalize`, which changes that continuation to `status=pass` and appends the compiler provenance hash (`resume-stage4-from-admitted.sh:136–144`). The canonical verifier at `stage4-candidate-provenance.shs:229` subsequently rejects the changed continuation. Rehashing the provenance would invalidate the completion receipt in turn.
4. Bootstrap defaults now use centralized storage. `centralized-storage.shs:53` treats relative `build/bootstrap` as the centralized default, while `candidate.yml` searches that relative directory. Consumers must use the producer's actual output path.

Bounded GitHub searches returned no successful `candidate.yml` or `rust-bootstrap-multiplatform.yml` runs. This is not proof that no successful build exists elsewhere. The latest candidate run inspected, 36378704254, failed before bootstrap at release-policy projection parity.

## Required repair and qualification design

The accompanying uncommitted patch repairs blocker 3: immutable admission and
terminal completion now use separate files and schemas. Canonical provenance
requires the admission schema, and the scheduler verifies the completion links.
The real finalizer passed a focused receipt-graph test with sixteen rejection
cases. This is not a compiler admission test or runtime qualification PASS.

Use the implementation skill's existing provenance rules, without a new shell-authored admission envelope.

Next repair the supervisor to derive the binding from its verified Stage 3 artifact, source fingerprint, backend, and Stage 4 planner receipt. Independently review the receipt split and exercise it with a real admitted compiler.

Then CI must produce receipt-free Stage 2, canonical Stage 3/4 planner receipts, and invoke the supervisor directly with both receipts and `--full-cli --no-mcp`. Use an explicit absolute output directory consistently. Validate the resulting full CLI with `stage4_verify_candidate_provenance`, recording commit, source digest, configuration, runtime path/hash, and bootstrap lineage.

Run each required check with that exact artifact; record path/hash and exit status per gate. Build both native server entry closures and run core/native MCP smoke. Package changes additionally require isolated npm smoke. Preserve failed logs and receipts. Admit no seed fallback, missing provenance, changed source, or changed artifact. Mark #1989 resolved only after an authentic CI run passes.
