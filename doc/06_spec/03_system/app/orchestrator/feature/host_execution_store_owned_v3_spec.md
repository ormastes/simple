# Owned Host execution storage with explicitly scripted provider

Source: `test/03_system/app/orchestrator/feature/host_execution_store_owned_v3_spec.spl`.
Requirements: HOST-EXECUTION-STORE-01, HOST-EXECUTION-STORE-02.
**AUTHORED_NOT_RUN**. This manual is not generated/docgen-verified.

| Scenario | Steps and asserted observations |
|---|---|
| retains exact packets creation intent and observation through the shared executor | Prepare a real signed reservation and invoke the common executor with a scripted provider. Check executing state, original packet, exact identity and canonical observation. |
| refuses a conflicting retained execution packet before journal begin or provider effects | Publish conflicting original bytes under the operation archive name. Verify refusal, zero scripted calls, admitted state and unchanged bytes. |
| preserves an uncertain post-create observation and refuses execution replay | Run the signed executor with a scripted start failure after journal begin. Verify retained creation identity/observation and no further provider calls on replay. |
| refuses arbitrary archive namespaces and keeps execute on the explicit effect action | Use production path and command admission guards. Reject namespace misuse; admit explicit execute and parent-budget command shapes. |

Filesystem, journal and signature operations are real when executed; provider
effects are scripted. These scenarios do not establish Windows native execution,
protected deployment startup, authority refresh during effects, persistent
daemon consumption, or post-effect cleanup qualification.
