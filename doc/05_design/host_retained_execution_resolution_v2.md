# Retained execution resolution

`host_local_retained_execution_v2` reads an immutable execution packet from the configured host journal root and correlates its original envelope, normalized Container request, scope, resource projection and original observation. It returns historical facts only. Terminal journal rows remain readable so an independently retained qualified wait can be checked after cleanup.

`host_local_resolve_execution_v2` uses that record to recover the exact retained creation intent and perform a fresh shared Container inspection. Its explicit `HostExecutionResolveTurnV2` carries the updated `HostLocalRootV1` on every path, including recovery failure, failed inspection and failed observation publication. Persistent callers must retain the complete turn; discarding it would lose provider recovery state. The finite inspect command retains its compatibility observation projection and closes its writer afterward.

Only the operation ID is caller-selected. Roots, provider policy, execution bytes, scope and runtime identity come from the configured retained owner. Neither read function creates, starts, destroys, releases a reservation or turns a signed packet into fresh authorization. Native inspection remains behind Simple Container API, with Linux Podman and Windows Docker backend checks owned by that facade and its configured leaf.

The original create/start observation stays immutable. A guarded inspection cache may advance phase/time while preserving exact native identity and authority correlation. The terminal-wait collector consumes the pure record for replay after destruction and the full owner-returning resolver before a fresh native wait.

Three authored SSpec cases cover repeated success, recovery/read failures and corrupt retained data. Their scripted adapter is explicit; runtime qualification remains NOT_RUN. No performance or platform completion claim is made.
