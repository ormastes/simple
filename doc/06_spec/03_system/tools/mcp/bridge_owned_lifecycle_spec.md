# MCP bridge owned-process lifecycle

Status: host Node suite GREEN4/4 after RED2/4; Simple SSpec wrapper AUTHORED_UNRUN.
Authored manual, not generated docgen output. Historical native orphan attribution
remains unresolved; this checks the actual Node bridge with synthetic children.

Spec: `test/03_system/tools/mcp/bridge_owned_lifecycle_spec.spl`

Spec SHA-256: `29a3c9de53272dcc19920ec02cb2a101e370c72c6810d9defa61d56323d72176`

Artifact: `test/fixtures/mcp/bridge_lifecycle_evidence.sdn`

Artifact SHA-256: `3941719c2e5ae9e1bc023172d7a31029f49106ad7b8ecc033bc2cf3e0fb53a8c`

## Flow

1. Run the production bridge and exchange an initialize-shaped fixture message.
2. Close stdin; require normal bridge exit and the owned fixture PID gone (REQ-001).
3. Launch a nonexistent child command while stdin stays open; require nonzero exit (REQ-002).
4. Close stdin on an EOF-ignoring child; require bounded owned-child shutdown (REQ-003).
5. Repeat normal sessions three times; require no owned fixture left alive (REQ-004).

Full identities are REQ-MCP-BRIDGE-LIFECYCLE-001 through -004. Every case's finally
cleanup uses a private stop-file and its bridge ChildProcess handle; no unrelated
process is killed. The SSpec calls the real Node test suite via the existing bounded
process facade and asserts four passes, zero failures, skips and cancellations.

No live MCP account, native Simple server, self-hosted runner or timing/security
qualification is implied. Run spipe-docgen and the wrapper with an admitted runtime
before replacing this authored manual with generated evidence.
