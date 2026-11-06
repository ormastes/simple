> **CYCLE 8 / CANDIDATE UNQUALIFIED:** Cycle 7 publication protections passed independent review and 27 focused controls. Qualification attempt 2 then stopped before candidate sanity because `git archive` omitted tracked controls marked `export-ignore`. The user-authorized cycle 8 source-materialization repair passed 15 focused assertions and independent source review. Actual candidate qualification remains unperformed; no fresh candidate admission exists. Earlier attempts remain counted and preserved.

# Preserved Stage 2 candidate requalification

Use `scripts/bootstrap/requalify-stage2-candidate.shs` when exact preserved
pure-Simple Stage 2 bytes and their immutable historical admission chain remain,
but a historical companion log is unavailable. This route never rebuilds the
compiler and never uses a Rust seed. It does not reconstruct missing logs.

## Admission boundary

The ordinary `bootstrap_stage3_verify_stage2_admission_receipt` remains strict:
missing execution evidence rejects product use. Its internal historical-chain
check verifies the original envelope and pinned bytes only. Successful
`--validate-history-only` prints `product_admission=false`, creates no output,
and executes no candidate. It is not a producer-tool or runtime admission.

Actual qualification copies the preserved candidate and runtime authority to a
new output directory. It reruns the complete canonical bootstrap sanity family
in both bootstrap configurations, then the struct-receiver/runtime check. The
canonical admission writer and strict preparation replay verify new evidence.
The receipt remains uncommitted while the runtime binding is prepared. Normal
admission and direct consumers reject it until the parent atomically publishes
`requalification-commit.env` after the publication watchdog reports successful
completion. The marker binds the exact admission and completed watchdog receipt
hashes; missing, incomplete or altered commit evidence rejects consumption.
The publication phase uses the remaining time from the same attempt deadline,
publishes the canonical Phase 2 runtime binding, and seals the admitted tree.
The runtime-binding publisher is a preparation operation; `resolve`, parent
receipt publication, phase verification, product producer/resume and the native
worker's transferred authority all enforce the same commit guard.

Original source snapshot, tool snapshot and dirty producer state remain under
`producer/`; they describe the compiler's original build. Fresh source, script,
runtime-source, tool and Git snapshots live under `control/`; they describe the
qualification checks. `requalification.sdn` binds both identities and the fresh
admission. Fresh controls do not claim that the preserved compiler was rebuilt
from their revision. Original archives and receipts are read-only inputs.
The canonical sanity-composition receipt binds those provenance files into the
ordinary admission graph; ordinary replay rejects missing or altered control
files or producer state. The SDN record is a readable companion to that binding.

Actual mode requires a clean committed control worktree. It materializes that
exact HEAD with `git archive` into `control/source-root`, using private Git
metadata whose highest-priority attributes disable `export-ignore` and
`export-subst`. This preserves committed bytes, executable modes and symlinks
without reading dirty files or changing shared Git attributes. It removes write access,
and executes the canonical fixtures there. Uncommitted qualification repairs
must be committed before launch; they are never silently excluded or relabeled.

## Required inputs

Pass absolute canonical paths using `--candidate=`, `--historical-receipt=`,
`--history-root=`, `--runtime-root=` and `--output=`. The output must not exist.
The history directory must retain `source-inputs-before.txt`,
`runtime-admitted.txt`, `tool-authority-before.txt`, `git-state-before.env`,
`stage2-sanity.env`, `stage2-receiver.env` and `stage2-receiver.log`.

Independently obtain and pin `--expected-candidate-sha256=`,
`--expected-admission-sha256=` and `--expected-producer-state-sha256=`. Supply
positive finite `--timeout-seconds=` and `--max-rss-kib=` bounds. Actual mode
also requires `--backend=llvm` or `--backend=cranelift` and `--target=` matching
the historical target. The canonical target toolchain must be on PATH. The
usual canonical sanity controls remain applicable; they cannot skip checks.

Do not run actual qualification before reviewing the candidate's historical
identity, the new control snapshot and resource capacity. The historical-only
mode is suitable for that preflight. Each actual invocation is a separate
finite attempt with a fresh output; failures retain logs and caches and do not
trigger another attempt automatically.

Successful output contains `stage3/<target>/stage2-admitted/simple` and adjacent
`admission.env`. This is a qualified Stage 2 compiler, not a full CLI/test runner
or deployment. Managed continuation and product verification retain their own
admission requirements.

## Verification contract

`sh scripts/check/check-stage2-candidate-requalification.shs` uses synthetic
fixtures only. It proves strict replay accepts a complete fixture and rejects
a missing historical companion log, while historical preflight does not execute
the fixture or create admission. It rejects altered candidate/receipt/source/
runtime/tool/sanity/receiver state, malformed arguments, symlinks and occupied
outputs. These controls are not evidence that a real candidate qualifies.
