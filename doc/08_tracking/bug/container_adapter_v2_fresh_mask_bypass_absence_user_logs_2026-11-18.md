# LinuxSimpleContainerAdapterV2: seven V2 calls skip the `_fresh` routing on a fresh-epoch (lent) owner (2026-11-18)

Status: OPEN. Owner: container lane. Found by the milestone_0030 design review r2 (opus). Re-cited and widened by the
milestone_0030 auth-PR review at 42c82fa5d62.

`src/lib/nogc_async_mut/container/providers/linux/simple_container_adapter_v2.spl`:
- `read` (:487) and the typed V3 paths start with `if val fresh = self._fresh: return fresh...`.
- These skip that guard and go to `self.provider` directly on an `open_fresh_v2` (:115) adapter:
  - `logs_capture_begin_v1` (:475). Its preliminary `inspect` does go through `read`.
  - `absence` (:554)
  - `execution_user` (:573)
  - `output_plan` (:667)
  - `_output_capability_observe_v2` (:689)
  - `open_output_session` (:725 -> :745)
  - `user_mapping` (:747 -> :754)

Impact: they fail closed, but they report the wrong reason. `open_fresh_v2` builds the raw provider with
`live_enabled=false` and `engine_policy: nil`, so each call refuses inside `oci_runtime_v1.spl`:
- `observe_absence_v2` (:399) returns `absence-managed-podman-required`.
- `observe_execution_user_v2` (:430) refuses the same way.
- `logs_capture_begin_v1` (:1092) returns `container-logs-native-capture-unavailable`.
- Output engine observation refuses on the nil policy.

Nothing observes through the masked provider. However, the refusals name a podman or engine condition instead of
the fresh-epoch rule. They also depend on those provider defaults staying refusing.

Fix: give each of the seven methods the same `_fresh` guard as `read`. Each should refuse with
`linux-workspace-fresh-typed-action-required`, or route to a fresh-owner equivalent if one exists. Add a spec that
calls each method on an `open_fresh_v2` adapter and expects that refusal.
