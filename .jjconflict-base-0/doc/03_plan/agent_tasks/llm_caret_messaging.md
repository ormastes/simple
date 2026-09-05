# LLM Caret Messaging — Agent Tasks

The exclusive lanes and merge order are defined in `doc/03_plan/app/llm_caret/messaging.md`.

Shared interfaces: `ChatTransportPort`, `AgentControlPort`, `MessageStorePort`, `NotificationPort`, `TransportCapabilities`, `ContextBundle`, `MessagingHooks`.

Shared manual steps: `Enroll a primitive account`, `Create and bind a room`, `Route a message to an agent`, `Inject the bounded context bundle`, `Observe task and receipt transitions`, `Recover messaging state after restart`.

Shared helpers: `setup_messaging_fixture`, `start_primitive_messaging_server`, `check_transport_contract`, `check_agent_control_contract`, `check_messaging_plugin_install`, `check_messaging_traceability`. Any incomplete helper fails explicitly.

Sidecars: bounded domain/application implementation, SSpec/manual generation, and plugin/skill surfaces may proceed in parallel after this contract freeze. Merge owner: primary Codex integration lane. Final reviewer: normal/highest-capability Codex; it owns broad exclusions, manual quality, security acceptance, traceability, and done marks.
