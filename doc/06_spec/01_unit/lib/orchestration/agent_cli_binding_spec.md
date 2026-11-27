# Exact agent CLI and task binding

Source: `test/01_unit/lib/orchestration/agent_cli_binding_spec.spl`.
Status: **AUTHORED_UNRUN**. These production-import checks establish pure
adapter/integrity behavior only; no installed binary, account, image or agent
execution is qualified by constructing a capability value.

1. Admit the three observed exact versions and reject unknown versions/providers.
2. Construct provider-specific resume and output argv while preserving arbitrary
   prompt text as data, without shell execution or borrowed CLI flags.
3. Refuse unsupported interactive Kimi and Codex's lone-dash stdin selector.
4. Reject malformed prompt and option values before an invocation is returned.
5. Resolve the checked policy fixtures and bind exact task/source/catalog,
   executable identity and ordered arguments into a stable digest. Changing
   model, resume identity or executable digest must change that binding.
6. Reject task namespace/reference/content corruption and provider mismatch.

The controller's retained AgentSession resolver must supply task authorization
and actual host/provider image-scoped CLI observations before consuming these
adapters. Image/workspace resolution, grants, common Container API execution,
CLI conformance and the Caret-to-smux positive binding scenario remain separate
integration requirements. Runtime tests and manual generation have not run.
