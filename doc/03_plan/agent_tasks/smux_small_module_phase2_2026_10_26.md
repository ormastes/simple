# Small-module implementation and Phase 2 execution guide

User authorization: complete the remaining implementation with Astra workers and interim Phase 2 execution. Target release/1.0.0; current follow-up is draft PR #4882. This does not relax the full Caret/IDE/Tmux/CoreMux scope or the requirement for executed system tests before landing.

Landing update: PR #4882 subsequently merged, and the user then explicitly requested “just land your fixes”. The remaining reviewed source is submitted in a separate PR on the current release branch. This supersedes the earlier instruction to hold these source fixes for execution; all failed/NOT_RUN qualification records remain unchanged, and no full-provider or release-readiness claim is made.

## Shared rules

- Read the accepted caret_mux_tui requirements, architecture, design and frozen common contracts. Never invent missing contract fields or advertise partial mandatory support.
- One authoritative ServiceState. New pure modules receive immutable inputs and return values; no new session registry, implicit adoption or endpoint fallback.
- Product code remains Simple. Host access uses Sosix or existing approved app facades. Memory-family selection is configuration, never application-directory inference.
- Root owns API/server composition, compiler scheduling, integration, publication and final review. Workers own disjoint files and send exact manifests before editing shared surfaces.
- Module tests call production functions with independent expected results. Modern SSpec uses existing matchers and named steps; no placeholder pass. Manuals remain explicitly authored until docgen runs.
- Configured container allocation may fail without throwing. Where a dropped insertion could turn ambiguity into a unique match, truncate an apparently complete snapshot, or advance an event cursor without payload, check actual insertion/cardinality outcomes and refuse with a typed error. Shape-validating a smaller result alone is insufficient. Record allocation-failure branches as unexecuted unless actually exercised; do not introduce fake passing fault-injection claims.
- Each worker retains source hashes, failures, case counts and artifacts. Authored, compiled, native-control-passed and SSpec-passed are separate statuses. Actual tests are required; source review never substitutes for them.
- One heavy compiler process at a time, finite rows, enforcing 5859375 KiB tree budget, bounded logs/deadlines, no automatic retry. At most six fix/verification cycles per feature; changing names/directories does not reset earlier attempts.
- The cache-generator diagnostic series is already exhausted. Do not rerun it without the separately requested explicit exception.

## Module ownership and seams

1. Exact target resolver: new core_mux_targets.spl. Resolve existing IDs/exact labels within a validated snapshot and supplied context; return existing references, never mint authority. Duplicate labels must refuse ambiguity. Broader tmux target grammar remains a separately visible integration requirement. Shared test steps: target_setup and target_check_resolution.
2. Per-lease event journal: new core_mux_events.spl. Bind one explicit handle, bounded event retention and byte budget; monotonic cursor, overflow reconciliation and pre-effect serial-capacity admission. No hidden service polling or new mutable controller. Shared steps: event_setup and event_check_batch.
3. Metadata query composition: new core_mux_metadata_queries.spl. Compose scoped snapshots, exact-target resolution and current context using frozen DTOs. Authentication belongs to the owner before invocation. Capture, retained request status and event effects retain their proper owners rather than fake default success. Shared steps: metadata_setup and metadata_check_snapshot.
4. Phase 2 SSpec execution owner: inspect the canonical common/test_runner/native_framework_wrapper.spl and existing real-framework positive/negative controls. Reuse the canonical runner; do not create another imitation assertion framework. Define one finite build/execute row per small module after interface freeze, with actual executable/producer/runtime/source identities and case counts.

Authors propose exact exported signatures against current contracts before implementation. Helpers must be small enough for independent review; do not move large unfinished behavior behind a completed-looking wrapper. Optional weaker semantics are not automatically selected.

## Execution order and evidence

Root first qualifies the real SSpec harness with its retained positive and intentional-failure controls. No zero-case pass is admissible. Module source work may proceed in parallel; compiler rows remain serialized.

The immutable interim compiler is C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025/output/stage3/simple.exe, SHA256 13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b. Its native-build interface is usable, but --library-mode is unsupported. A supported legacy-profile functional run must record that actual profile and cannot prove explicit NoGC selection. Explicit profile controls, full system workflows, Phase 3 qualification and both-backend N2 remain separate mandatory gates.

After each module's actual supported cohort passes, integrate real process/terminal cases for split/layout/resize, detached children, multiple clients/windows, literal/key/paste routing, notifications, recovery and cleanup. Preserve and fix failures within the existing budgets. A passing native diagnostic is not a passing SSpec suite. Keep the PR draft until relevant execution, formal-model and repository verification gates actually pass.
