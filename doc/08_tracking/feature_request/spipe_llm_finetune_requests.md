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
