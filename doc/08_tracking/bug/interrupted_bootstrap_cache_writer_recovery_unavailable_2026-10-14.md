# Interrupted bootstrap cache writer cannot be recovered canonically

Status: OPEN. Operational blocker observed while rebuilding the Phase 3 repair producer; no cache authority was changed.

The owned canonical seed-to-Stage-2 prerequisite was interrupted deliberately to include the reviewed full-object direct-argv linker repair. Its outer watchdog reports exit 143, `quiescent=1`, and peak RSS 2,377,396 KiB. The session preserved 1,001 cache object files, logs, source/tool/runtime snapshots, writer marker and process receipts under `.simple/storage/build/phase3-producer-refresh`.

The retained `stage2-native-cache.writer` names PID 2095702. Canonical acquisition refuses an unresolved writer, and the idle-writer repair path has no execution-owner receipt recovery implementation. Wrapper quiescence alone is explicitly insufficient. The supported `--refresh-stage2-source-cache=<predecessor-components>` source transition is therefore blocked before it can verify the unchanged seed/runtime/tool authority and independently validate cached objects.

Relocating the cache to a new output does not preserve its context: the semantic binding includes the output-specific link-compat library path. Do not delete the writer marker, rewrite bindings or relabel old object keys to force reuse.

The safe continuation uses a fresh private native cache at `.simple/storage/build/phase3-producer-refresh-linkfix`, while preserving the interrupted cache for future owner-supported recovery. This retains compatible successes as evidence but does not claim they were reused. The additional full Phase 3 qualification has not started.

Required repair: define an authenticated execution-owner completion/cancellation receipt and canonical recovery that verifies exact writer identity, process lifetime/session containment, descendant quiescence and cache publication boundaries before releasing an abandoned writer. Cover live-writer rejection, PID reuse, incomplete publication and interrupted source-transition recovery. Existing lock ownership and cache identity checks must remain effective.

Evidence: `phase3-producer-refresh/source-refresh-restart-assessment.md`, `retained-predecessor-before-link-fix-20261014` and `root-corrected-link-handoff.json` in the private build storage. Owner: Codex Phase 3 incremental completion session.
