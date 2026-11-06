# Caret process ownership boundary

Application code imports canonical opaque owners through `app.io.process_ops`; no new rt externs belong in agent leaves. The manager owns lease/pin cleanup; authenticated source code only verifies the same lease. Keep source-session generation independent of raw PID identity. Process errors with retained owners keep the team degraded/stop-failed, never exited/clean. Runtime qualification and standalone fixture instructions are in `doc/07_guide/tooling/caret_owned_source_agents.md`.
