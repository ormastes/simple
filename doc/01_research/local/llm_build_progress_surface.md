# Local Research: LLM Build Progress Surface

The compiler already emits structured append-only `build_progress` events through `log_build_progress`, and bootstrap passes `SIMPLE_BUILD_PROGRESS_EVENTS` to native-build workers. The event stream is useful evidence but forces readers to scan an ever-growing file and reconstruct current state. The native pipeline already knows phase, completed/total units, current item, failures, cache hits, elapsed time, and link inputs at the call sites. Therefore the least-invasive integration point is `driver_log_helpers.spl`: preserve events and additionally publish one current snapshot.

Centralized storage roots provide the required authority. The snapshot belongs at `<worktree-storage-root>/build/progress/current.sdn`; detailed events and receipts remain separate evidence. Compiler code consumes explicit paths and does not discover roots itself.

