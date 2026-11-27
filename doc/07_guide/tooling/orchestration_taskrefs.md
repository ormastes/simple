# Retaining and using an exact TaskRef version

Status: source implementation, **NOT_RUN / NOT_APPLIED**. These commands do not
start an agent. They require a qualified Simple executable, an administrator-owned
Controller root and independently signed issuer/human-approver packets.

The command forms are:

```text
simple orchestrator task-retain <root> <controller> <config-digest> <absolute-packet-file>
simple orchestrator task-use <root> <controller> <config-digest> <absolute-packet-file>
```

The root and configuration pin are local administrator inputs. A future remote
service must obtain them from its installed policy, never from a peer's frame.
Linux uses the existing protected Controller root and trusted ancestor precondition;
its pin is SHA256 of canonical V1 dispatch configuration. Windows uses the actual
retained V3 private root and exact installed V3 configuration-byte pin. Windows
root composition is a separate dependency; source availability is not qualification.

1. Retain a canonical `agent-task-object` containing namespace, logical reference,
   original UTF-8 content and its SHA256. The maximum body is 4096 bytes. The
   `retain` command packet carries a separate signed retention grant and approval.
   The object becomes an immutable version under the existing Controller journal.
2. Submit/pin the AgentSession desired state and policy through the existing
   Controller flow. Its TaskRef names the logical reference; it does not select a
   mutable latest body.
3. Create a canonical `agent-task-use` binding with the exact raw digest, namespace,
   session UID, attempt, committed source/catalog, selected Host scope, model and
   fixed `codex-root-start-0.169.0-v1` adapter. Obtain separate signed task-access
   grant and approval for that exact binding, then call `task-use`.

The canonical outer SDN packet has version 1, kind
`controller-agent-task-command`, action `retain` or `use`, canonical body string,
`signedGrant` and `signedApproval`. Its maximum size is 262144 bytes. Authority
operation construction is exposed by
`controller_agent_task_authorization_operation_v1` for the independent signing
integration. No private role signer or key is created by these commands, and SSH
client keys are not role-signing credentials.

Both signatures cover the exact task operation and currently installed config,
Controller epoch, policy, revocation and session generation. A `use` commits the
exact attempt binding before reading content. Each read checks fresh access again;
a committed binding is not continuing authorization. Reusing that UID/attempt for
a different version or intent fails. A separate authorized attempt may reuse the
same immutable task version.

Replies report reference/digest and metadata status. Raw content is not printed.
Provider CR/CRLF normalization is a later derived invocation value; stored task
bytes are never silently rewritten. A task-access result is not permission to
execute, disclose arbitrary task contents or reuse an expired grant. The complete
AgentSession path still needs the real Host selection, workspace/credential owners,
full invocation grant and terminal handoff. Unconfirmed cleanup retains the actual
root/journal owner in-process and reports reconciliation required.
