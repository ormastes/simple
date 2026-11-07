# Authenticated runtime binding adapter

Status: **AUTHORED_UNRUN**. Production-import, in-process dispatch and pure codec assertions. No socket, compiled CLI, configured host admission, stream, or provider acceptance is established.

Source: `test/01_unit/os/apps/smux/runtime_binding_adapter_v3_spec.spl`.

1. Reject unauthenticated planning, binding, inspection, target, and capability queries before owner lookup. Configuration revision remains unchanged.
2. Classify the real authenticated absence reply without claiming a configured owner. The actual client classifier accepts discovery and rejects unconfigured binding, generic success text, and the unauthenticated remote route.
3. Require the exact configured capability shape without inferring runtime support. Synthetic codec input permits planning only and rejects binding, framed CoreMux, input, geometry, interactivity, readiness fields, and unknown versions.
4. Refuse replayed or substituted binding identities before reporting planning success. Syntactically valid planned metadata with the wrong UID, service incarnation, binding digest, workload operation, or helper operation is rejected. These negative codec inputs never enter an owner and are never asserted as positive planning evidence.

The configured foreground mode is `--serve-runtime-owner-file OWNER HOSTROOT`. It opens the trusted host root and fixed protected policy before listening. Requests carry only canonical bounded base64url SDN references and exact target fences. A planned reply requires actual common plan capability; adopted-opening is adoption, never readiness. Timeouts remain uncertain: inspect the same binding UID without generating a new operation.

Real configured positive coverage requires retained signed parent-budget and helper-admission packets, an admitted broker/profile, an actual provider runtime, fresh output through the sole pane reader, and retained cleanup/host settlement. No synthetic positive binding is substituted here.
