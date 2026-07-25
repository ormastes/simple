# SPipe LLM Fine-Tune Feature Requests

Tracker for follow-up work discovered while wiring the SPipe fine-tune process
to the existing MedGemma Korean artifacts.

Id scheme: `FR-SPIPE-LLM-####`, monotonic, no reuse.
Lifecycle: `Open` -> `Accepted` -> `Implemented` or `Rejected`.

---

## Open Requests

### FR-SPIPE-LLM-0001 - Run fixed-format/data-quality retry

- **Filed-on:** 2026-06-02
- **Filed-by:** Codex
- **Target:** SPipe LLM fine-tune retry loop / MedGemma Korean
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Execute the retry attempt
  `llm_backed_app_server_dry_run_retry1` using the fixed-format prompt and
  data-quality path identified in the MedGemma Korean project.
- **Acceptance-criteria:**
  - [ ] Retry attempt records real training/data-quality commands and artifact
        paths.
  - [ ] Retry evidence is recorded through `fine-tune-record-training`,
        `fine-tune-record-eval`, and `fine-tune-record-decision`.
  - [ ] Failed retries create the next explicit retry attempt instead of
        replacing prior evidence.

### FR-SPIPE-LLM-0002 - Require target-reaching eval before acceptance

- **Filed-on:** 2026-06-02
- **Filed-by:** Codex
- **Target:** SPipe fine-tune readiness gate
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Do not accept the MedGemma artifact until recorded
  evaluation reaches `target_accuracy>=90.0` on the 604-sample target set.
- **Acceptance-criteria:**
  - [ ] `fine-tune-ready llm_backed_app_server_dry_run_retry1` reports PASS only
        after an accepted decision with target-reaching eval evidence.
  - [ ] The original `llm_backed_app_server_dry_run` remains preserved as a
        failed evidence record with retune routing.
  - [ ] Handoff docs state the accepted model id/path and exact eval command.

### FR-SPIPE-LLM-0003 - Add medical safety and deployment evidence

- **Filed-on:** 2026-06-02
- **Filed-by:** Codex
- **Target:** LLM-backed medical QA app/server handoff
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Require safety, license, and deployment evidence
  before the MedGemma artifact is treated as production-ready.
- **Acceptance-criteria:**
  - [ ] Handoff records license/distribution constraints for `google/medgemma-4b-it`.
  - [ ] Safety eval includes refusal/boundary behavior and clinical-disclaimer
        checks.
  - [ ] Deployment evidence records runtime, memory target, latency target, and
        rollback/fallback model.
- **2026-06-26 gate update:** `fine-tune-record-app`, `fine-tune-verify`, and
  `verify_attempt.shs` now require explicit `license_constraints`,
  `safety_eval`, and `deployment_evidence` fields. The current MedGemma retry
  records intentionally carry non-deployment evidence until the real license,
  safety, and deployment checks above are complete.

### FR-SPIPE-LLM-0004 - Obtain licensed fixed-format data cache

- **Filed-on:** 2026-06-26
- **Filed-by:** Codex
- **Target:** SPipe LLM fine-tune retry5 / MedGemma Korean
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Complete the current retry5 handoff by obtaining
  licensed fixed-format medical QA data access, writing a repo-visible cache
  path/checksum evidence record, and keeping training blocked until license
  approval exists.
- **Acceptance-criteria:**
  - [ ] `llm_backed_app_server_dry_run_retry5` records a real licensed data
        source, approved license state, cache path, and checksum.
  - [ ] `fine-tune-data-plan llm_backed_app_server_dry_run_retry5` reports the
        licensed data cache/checksum as present.
  - [ ] `fine-tune-ready llm_backed_app_server_dry_run_retry5` still fails until
        target-reaching model eval and accepted decision are also recorded.

### FR-SPIPE-LLM-0005 - Run real QLoRA retry after data gate

- **Filed-on:** 2026-06-26
- **Filed-by:** Codex
- **Target:** SPipe LLM fine-tune retry6 / MedGemma Korean
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** After FR-SPIPE-LLM-0004 is satisfied, run the real
  QLoRA rerun and target evaluation instead of accepting dry-run artifact
  evidence.
- **Acceptance-criteria:**
  - [ ] A retry6 or successor attempt records real training command, artifact,
        evaluation command, metrics, and target result.
  - [ ] The eval reaches `target_accuracy>=90.0` before any accepted decision.
  - [ ] If eval remains below target, the decision routes to a new retry or a
        retrieval/tool strategy instead of overwriting prior evidence.

### FR-SPIPE-LLM-0006 - Promote retry7 acceptance only after real evidence

- **Filed-on:** 2026-06-28
- **Filed-by:** Codex
- **Target:** SPipe LLM fine-tune retry7 / MedGemma Korean acceptance gate
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Keep retry7 as the normal-review acceptance gate, but
  do not allow it to pass until the licensed data, real training/eval, safety,
  deployment, and app-handoff evidence are all real and locally verifiable.
- **Acceptance-criteria:**
  - [ ] `fine-tune-ready llm_backed_app_server_dry_run_retry7` reports PASS only
        after retry5 licensed-cache evidence and retry6-or-successor real
        target-reaching eval evidence are present.
  - [ ] `check_retry7_acceptance_gate.shs` reports missing safety, deployment,
        app-handoff, or normal-review evidence as WARN/FAIL blockers instead of
        acceptance.
  - [ ] The accepted retry7 decision records the final model artifact, target
        eval command/result, license constraints, safety eval, deployment
        evidence, and app handoff doc without placeholder or `do not deploy`
        wording.
