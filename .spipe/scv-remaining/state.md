<<<<<<<<<< Conflict 1 of 1
%%%%%%%%%% Changes from base to side #1
 # SStack State: scv-remaining
 
 ## User Request
 > remains with agents teams
 
 ## Task Type
 code-quality
 
 ## Refined Goal
 > Close all remaining SCV work items: fix interpreter memory-pressure parse-state corruption affecting PROD-001 child-process tests, split integrity.spl preventively (718/800 lines), calibrate structural_match Dice coefficient thresholds with empirical data, and pass the completion gate audit.
 
 ## Acceptance Criteria
 - [ ] AC-1: Interpreter memory-pressure fix — PROD-001 wasm_executor_spec passes reliably under repeated runs (no sporadic parse-state corruption from child `simple run` with full SIMPLE_LIB)
 - [ ] AC-2: integrity.spl split — file stays under 600 lines after extracting a logical sub-module (e.g. integrity_parser.spl or integrity_ops.spl)
 - [ ] AC-3: Dice coefficient calibration — structural_match.spl TODO resolved with empirically-tested threshold values, documented rationale
 - [ ] AC-4: Completion gate audit — all 6 gate criteria verified and documented in scv.md
 
 ## Cooperative Providers
 - Codex: unavailable
 - Gemini: unavailable
 
 ## Phase Checklist
 - [x] 1-dev (Developer Lead) — 2026-05-15
 - [x] 2-research (Analyst) — 2026-05-15
-- [x] 3-arch (Architect) — 2026-05-15
-- [x] 4-spec (QA Lead) — 2026-05-15
-- [x] 5-implement (Engineer) — 2026-05-15
-- [x] 6-refactor (Tech Lead) — 2026-05-15
-- [x] 7-verify (QA) — 2026-05-15
-- [x] 8-ship (Release Mgr) — 2026-05-15
+- [ ] 3-arch (Architect)
+- [ ] 4-spec (QA Lead)
+- [ ] 5-implement (Engineer)
+- [ ] 6-refactor (Tech Lead)
+- [ ] 7-verify (QA)
+- [ ] 8-ship (Release Mgr)
 
 ## Phase Outputs
 
 ### 1-dev
 Task type: code-quality (4 remaining items closing the SCV product).
 
 Refined goal: Close all remaining SCV work — interpreter memory-pressure fix, integrity.spl split, Dice calibration, completion gate audit.
 
 Acceptance criteria: 4 ACs covering bug fix, refactor, tuning, and verification.
 
 Workstream strategy for parallel Sonnet agents:
 - **WS-A (Runtime):** AC-1 — interpreter memory-pressure investigation and fix in `src/compiler_rust/`
 - **WS-B (Refactor):** AC-2 — split `integrity.spl` into sub-modules
 - **WS-C (Tuning):** AC-3 — Dice coefficient calibration in `structural_match.spl`
 - **WS-D (Audit):** AC-4 — completion gate verification
 
 Each workstream has disjoint file scope.
 
 ### 2-research
 Research complete across 4 parallel Sonnet agents. Detailed findings in:
 - `.spipe/scv-remaining/research_ws_a.md` (Runtime memory pressure)
 - `.spipe/scv-remaining/research_ws_b.md` (integrity.spl split)
 - `.spipe/scv-remaining/research_ws_c.md` (Dice calibration)
 - `.spipe/scv-remaining/research_ws_d.md` (Completion gate audit)
 
 Critical findings:
 - WS-A: NOT cross-process corruption. Per-child RSS bloat from 600+ SIMPLE_LIB files causes OOM kills. Fix is test-script scoping + memory guard, no bootstrap rebuild.
 - WS-B: Clean 5-file star split: main ~195, parser ~200, view ~155, object ~135, commit ~70. No circular deps.
 - WS-C: Thresholds match GumTree paper. Strict > vs >= gap. TODO remains blocked on real tree-sitter. Can fix inequality + add boundary docs.
 - WS-D: 4/6 gate criteria PASS. 2 PARTIAL: need one test each for byte-edit content-ID divergence and binary snapshot-restore round-trip.
 
 ### 3-arch
 <pending>
 
 ### 4-spec
 <pending>
 
 ### 5-implement
 <pending>
 
 ### 6-refactor
 <pending>
 
 ### 7-verify
 <pending>
 
 ### 8-ship
 <pending>
+++++++ Contents of side #2
++++++++++ Contents of side #2
>>>>>>>>>> Conflict 1 of 1 ends
