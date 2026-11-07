# Caret local controller client

The Caret `orchestrator` command submits or inspects retained controller intent
through an explicitly selected compiled controller. Both applications must be
built through the admitted product toolchain. The source client alone does not
provide the controller binary or a running host execution service.

Use the same request UID for later inspection:

```text
simple_caret orchestrator /absolute/path/simple_orchestrator submit /absolute/controller/state controller-a request-a /absolute/agent.sdn agents reviewer
simple_caret orchestrator /absolute/path/simple_orchestrator inspect /absolute/controller/state controller-a request-a
```

The controller state root must already belong to the selected controller.
Submission selectors are the source document's namespace and resource name.
Paths with spaces must be quoted as one argument by the invoking shell.
The client never resolves an implicit executable from PATH.

Results are SDN. `confirmed: true` means the matching controller metadata
receipt passed validation; `executionAuthorized: false` remains explicit.
Retained intent or assignment does not mean an agent is running. This client
does not issue execution grants, perform provider startup, or attach smux.

Exit status 0 reports confirmed metadata, 1 reports an unconfirmed controller
attempt requiring reconciliation, and 2 reports invalid input before a child
was invoked. For timeout, process failure, malformed reply, or changed reply
identity, preserve the displayed original UID and inspect it. Do not assume
the failed response proves that no intent was retained, and do not replace the
UID to retry uncertain work.

The current reply schema accepts the local metadata protocol only. Future
runtime/host inspection fields require a coordinated client schema update.
The explicit executable path is not a pinned binary identity. See the design
document for bounds and the distinction between source checks and runtime
qualification: `doc/05_design/caret_orchestrator_client.md`.
