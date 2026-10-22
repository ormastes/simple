# Coverage-aware retained parser ownership

Authored manual for
[`coverage_retained_parse_owner_spec.spl`](../../../../test/03_system/compiler/coverage_retained_parse_owner_spec.spl).
Execution and SPipe doc generation: **UNRUN**. This manual does not claim
native evidence or zero-stub generator admission.

## Prepare the native fixture

Admit the canonical source-matched pure-Simple CLI through the existing
Stage4 provenance verifier. Compile the actual ownership fixture once with
stub fallback disabled. Preserve compiler output, source and binary hashes,
and exit status in the private test-artifact directory. A missing producer,
receipt or native executable fails the scenario.

## Coverage source reclamation

1. Run the native fixture with `--coverage`.
2. Parse four sources and check that each source's flat-AST scratch is empty
   after return. Read the first retained return value and desugared functions
   after later allocations.
3. Check original coverage rows, replay semantics, malformed-source diagnostics
   and successful recovery.
4. Require exit zero and the exact mode-specific PASS receipt.

## MC/DC source reclamation

1. Run the same executable with `--mcdc` in a fresh process.
2. Require retained condition obligations and formal contexts from prior files.
3. Replay the first source: decision/condition rows remain deduplicated and
   existing context-appending semantics remain exact.
4. Require readable parser diagnostics, recovery, exit zero and the MC/DC PASS
   receipt.

## Full-inventory target selection

1. Run the executable with `--full-inventory` in a fresh process.
2. Require the same lifetime and coverage checks plus four valid retained
   frontend target receipts.
3. Reject an unregistered source identity; then retain malformed-source
   diagnostics and recover on a valid source.
4. Require exit zero and the full-inventory PASS receipt.

All scenarios cover REQ-PARSE-OWNER-001, REQ-PARSE-OWNER-002 and
REQ-PARSE-OWNER-003. Compile deadline: 20 minutes; each native execution:
2 minutes. The campaign supervisor retains the existing process-tree RSS cap.

**Evidence:** `build/test-artifacts/coverage-retained-parse-owner-<pid>-<time>/`
contains compile/run logs, `identity.sdn`, and each policy's exit receipt.
This fixture establishes ownership behavior only; whole-build RSS, object
membership, linking and Hello World require their separate real evidence.
