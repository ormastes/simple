# Native macOS Simple Container implementation plan

Merge owner: Codex. Final reviewer: Astra or equivalent. Sidecars: N/A until
the macOS helper interface is fixed. The Windows process-container lane owns
its separate platform files.

1. Keep the shared `native-sandbox` admission and SDN codec; run their focused
   specs on a source-matched self-hosted Simple runtime.
   The Mac `.spl` format and request admission gates now exist with focused
   unit specs. Run them in a fresh verification session; this session exhausted
   its prescribed verify/fix cap. Admission does not enable native launch.
2. Build and sign a small Mac App Sandbox helper and an inheriting workload
   with the required child entitlements. Confirm the actual workload is sandboxed and denies the host
   sentinel while accepting the explicitly provisioned workspace. Run this
   fixture in a Mac session that can launch an independently sandboxed app;
   the restricted Codex host probe of 2026-09-28 aborted before `main` for
   both an ad-hoc signed CLI and `.app` bundle.
   A bounded authenticated command protocol now exists in Simple. Add a
   Simple-native XPC/app service and an OS-authenticated key/peer channel;
   protocol authentication alone does not establish sandbox authority.
   A Simple bundle generator and CLI now stage supplied native app/service
   executables and sign the embedded XPC service before the app. Supply actual
   Simple app and `xpc_main` service entrypoints, connect them, then qualify
   independent launch and sandbox state on an unrestricted Mac login.
3. Implement `MacOsNativeSandboxProviderV1` in Simple around the existing
   pinned executable and a new macOS process-observation owner: current V3/V4
   owners are unavailable on macOS. Bind one operation to its
   native start identity. Reject stale IDs, incompatible binaries, missing
   entitlements, unsupported policy, and uncertain cleanup.
4. Exercise create/start/wait/stop/destroy or document the exact honest
   lifecycle supported by the helper. Require nonzero exit, bounded output,
   cancellation, an attempted detaching child, and fresh absence on this Mac.
   If the no-child policy cannot be enforced, keep untrusted launch unavailable.
   Hosted Process Observation V4 currently does not advertise exact-tree
   containment. Select a real descendant authority or explicitly limit the
   first provider to trusted same-owner workloads; leader/process-group
   observation must not be reported as a no-child proof.
   Apple documents same-process-group launchd cleanup only. A child that calls
   `setsid`/`setpgid` is an explicit negative fixture for any proposed owner.
5. Repair SimpleOS authenticated loader bug 355, then qualify a SimpleOS
   managed task and kernel exit on SimpleOS. Compare common receipts across
   both providers without transporting platform handles.

The old QEMU/HVF Mac preflight and guest dispatcher are outside this plan.
