# Caret correlated execution client

Status: **AUTHORED_UNRUN**. This manual describes seven source-import scenarios
in `test/03_system/app/llm_caret/feature/orchestrator_execution_client_spec.spl`.
It was written from the executable specification; generated doc tooling has
not run. Synthetic wire values exercise production codecs and client logic;
they do not establish process, host, container or completed AgentSession evidence.

| Step | Check |
|---|---|
| Build distinct dispatch resume and execution inspection requests | Exact argv preserves spaces; dispatch/resume use a 120000 ms transport budget and inspection 30000 ms. |
| Reject relative executables extra inspection packets and metadata actions | Invalid requests return before the process owner is called. |
| Validate exact nested prepared fields and preserve the original UID | Matching preparation confirms only admitted state and keeps runtime unobserved. |
| Decode both provider observations and keep exited distinct from completion | Native-boot and service-incarnation scopes pass through the host decoder; `completionObserved` remains false. |
| Correlate controller UID host operation plan and semantic request | Matching hashes cannot excuse a different controller, UID, host operation, plan or request. |
| Require the shared strict codecs instead of trusting a status string | Unknown versions, completion claims, extra fields and malformed nested observations fail. |
| Keep the same request identity and never infer a safe retry from malformed output | Nonzero exit, stderr, empty and saturated capture remain uncertain; no automatic retry occurs. |

Production consumption is `llm_caret/main.spl` →
`run_orchestrator_execution_cli_v2` → `caret_execution_request_v2` → the existing
bounded process facade, with one configured absolute controller invocation.
The CLI uses the existing `orchestrator` prefix and separate `dispatch`,
`resume-execution` and `inspect-execution` actions. Metadata V1 is unchanged.

Verification must integrate the exact reviewed shared controller reply V2,
host observation V2 and Container scope V2 dependencies, then execute a real
compiled Caret/controller roundtrip. Preserve argv, stdout, stderr, exit code,
durable operation correlation and binary identities. A client transport timeout
is uncertainty; it never renews a signed host deadline or authorizes a retry.
Generic resolved dispatch is not retained AgentSession resolution, terminal
adoption, input/geometry capability or workload completion.
