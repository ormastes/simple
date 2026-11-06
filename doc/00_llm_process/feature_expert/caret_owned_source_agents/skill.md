# Caret owned source agents

Use `agent_runtime.spl` and `owned_agent_process.spl` for the opt-in `owned_source_sessions` path. Preserve existing provider argv and legacy mode. Opaque `OwnedProcessLease` plus owner-generated identity is authority; never derive authorization from PID existence. Retain failed close/collection owners. The supervisor must pump leases independently of HTTP requests. Guide: `doc/07_guide/tooling/caret_owned_source_agents.md`. Runtime admission is pending; authored tests are not PASS.
