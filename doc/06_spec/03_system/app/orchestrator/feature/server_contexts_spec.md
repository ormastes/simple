# Select a server and retain controller intent

Source: `test/03_system/app/orchestrator/feature/server_contexts_spec.spl`.
Manually authored companion. **NOT_RUN**: no admitted self-hosted runtime.

The application selects the same server and credential reference for Simple
and Orchestrator, selects a separate local Caret override, and projects the
agent's explicit container address. The controller scenario initializes a real private state root,
submits the AgentSession fixture through the typed gateway, inspects its UID,
records cancellation using the original source digest, and inspects the retained
cancelled state. It asserts that metadata submission is not execution authority
and requested cancellation is not observed process termination.

No SSH endpoint, container, runtime process or signed successful dispatch is
claimed by this scenario. Native SSH and Linux/Windows container receipts remain
required. The private test root is retained as inspectable evidence.
