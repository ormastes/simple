# SimpleOS server capability manifest agent tasks

- Sidecar lanes: N/A — bounded parent-assigned implementation lane.
- Merge owner: parent `/root`.
- Final reviewer: parent `/root` at normal/high capability.
- Shared interface: `ProtocolCapabilityManifestV1` and
  `simpleos_server_protocol_capabilities`.
- Manual flow helpers: inline `step("Start...")`, `step("Offer...")`, and
  `step("Bind...")`; no placeholder helpers.
