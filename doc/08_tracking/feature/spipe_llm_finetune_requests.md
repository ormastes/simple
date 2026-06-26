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
