# Local Windows Controller and retained Host route

Status: source candidate, NOT_RUN. These commands have not been qualified on a Windows deployment. The route requires protected local filesystem access to both the installed Controller root and the Host setup/journal. It is not a cross-host route. A tunnel alone is insufficient. HMAC authenticates the local exchange and protects integrity; it does not encrypt traffic or provide a remote confidential transport.

The Controller journal stays separate from the Host capacity journal. Use the existing installed Host enrollment, machine policy and sole physical-budget owner. Do not start an independent legacy V5 Host instance over the same physical budget.

## Administrative setup

Use the existing administrator-installed protected parent and a fresh setup leaf:

```text
simple orchestrator host-auth-setup SETUP_PATH
```

The lower owner checks the protected parent before OS entropy, publishes one immutable V6 setup record without replacement, and reports public `publicationUid`, `setupDigest`, publication state and cleanup state. It never prints the secret. Save the exact returned setup digest in installed Controller configuration. A conflict or uncertain publication needs explicit reconciliation; do not overwrite the file or repeatedly rerun setup. This MAC credential is distinct from shared SSH `authRef`/`trustRef` identities and from SCV bearer tokens.

## Host service

```text
simple orchestrator host-authenticated-service windows-docker ANCHOR POLICY_PIN BINDING 127.0.0.1:0 SETUP_PATH SETUP_DIGEST
```

`ANCHOR`, `POLICY_PIN` and `BINDING` use the existing installed Host factory contract. The service retains the actual Host domain and publishes a secret-free ready record through that domain's existing journal. The current lease selects the immutable record. This explicit mode rejects legacy bearer commands and terminal operations. Default V5 behavior is unchanged. Authenticated interactive terminal binding through the same owner remains future required work.

## Controller commands

Install a canonical V3 Controller config and its pinned authority policy under a separately protected Controller root:

```text
simple orchestrator controller-service-install CONTROLLER_ROOT CONFIG_FILE POLICY_FILE
simple orchestrator controller-service-status CONTROLLER_ROOT CONFIG_DIGEST
simple orchestrator controller-service-dispatch CONTROLLER_ROOT CONFIG_DIGEST WORKLOAD_UID SIGNED_PACKET_FILE
simple orchestrator controller-service-resume CONTROLLER_ROOT CONFIG_DIGEST WORKLOAD_UID SIGNED_PACKET_FILE
simple orchestrator controller-service-inspect CONTROLLER_ROOT CONFIG_DIGEST WORKLOAD_UID
simple orchestrator controller-service-progress CONTROLLER_ROOT CONFIG_DIGEST WORKLOAD_UID
simple orchestrator controller-service-cancel CONTROLLER_ROOT CONFIG_DIGEST WORKLOAD_UID
simple orchestrator controller-service-stop CONTROLLER_ROOT CONFIG_DIGEST
```

V3 configuration uses `target: retained-host-service-v1`, controller identity/epoch, the authority-policy digest, exact Host enrollment, stable setup path/digest and Host deployment root. It never accepts a selected ready filename as authority. Status verifies actual authenticated Host scope against installed binding. Dispatch uses existing signed authorization and assignment transitions. Resume and operation controls use the exact archived execute bytes; they never reconstruct a fresh permission to resend. A finite local wait or CLI cleanup does not implicitly cancel the persistent Host.

Service stop first authenticates status and binds the current incarnation/scope. The service quiesces before Host cleanup; unresolved owners remain cleanup-only. A successful Host-close reply does not prove later socket/listener cleanup. Lost responses or selector drift are Unknown, not permission to retry an effect.

## Restart and recovery limits

Restart preserves setup K and publishes a new lease-selected immutable ready record. A new lease without a ready record is unavailable; the client never falls back to an older record. Temporary protected selector reads can block Windows lease replacement and cause startup failure. Stop-drain selector drift makes delivery Unknown even if internal Host cleanup succeeded. No transparent restart or power-loss continuity is claimed.

All cleanup capabilities are process-local. Returned carriers are retained through command rendering and canonical finalization, but cannot survive process exit as live native authority. Unresolved cleanup/publication must remain a reported failure and reconciliation obligation. This candidate does not claim complete deployment, native acceptance, or cross-host orchestration.
