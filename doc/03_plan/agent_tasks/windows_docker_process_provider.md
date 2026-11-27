# Windows Docker process-provider ownership

| Lane | Owner | Scope |
|---|---|---|
| Provider implementation | Sol sidecar `/root/astra_windows/docker_impl` | Windows-only source modules |
| Contract/spec/manual and review | Astra `/root/astra_windows` | Negative/recovery assertions, source review and docs |
| Integration and landing | Root orchestrator owner | Cross-provider review and source-only PR landing |

Windows dispatch remains a separate versioned integration task. The source is
AWAITING_VERIFICATION; neither worker nor reviewer may promote it to qualified
from static checks. Root owns final cross-lane review and merged-PR disposition.

Follow-up ownership agreed: Astra orchestrator owns proposed shared
`ResolvedHostLaunchPlanV2`, `HostExecuteRequestV2`, `ControllerDispatchRequestV2`
names; Astra host owns Windows observed-host continuity and the Windows host
executor. They must use an explicit Windows discriminator and this leaf's typed
codec, preserve Linux V1 behavior and never reinterpret Linux launch bytes. Root
requested this source follow-up as part of the full feature objective; live
Windows qualification remains separate.
