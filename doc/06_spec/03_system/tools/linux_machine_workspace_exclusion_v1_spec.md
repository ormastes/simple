# Borrowed actual Linux workspace exclusion v1

**AUTHORED_NOT_RUN — authored manual, not generated SPipe evidence.**

Source: `test/03_system/tools/linux_machine_workspace_exclusion_v1_spec.spl`.
Requirements: REQ-LINUX-WORKSPACE-EXCLUSION-001 through 003.

Use a disposable administrator-prepared Linux fixture with fixed machine and
workspace profiles, its delegated nonroot service UID, the private machine
state/WAL tree and a genuinely enforced XFS project-quota workspace. Run on
the actual process leader thread. This spec does not install anything, elevate,
launch Podman, delete a workspace or release quota.

1. **Read fixed administrator profiles and retain the actual XFS quota lease.**
   Open the actual machine policy reader and its fixed workspace profile.
   Require the profile's machine digest to equal the actual protected policy.
   A mismatch closes the retained reader, reports failure and returns before
   any native quota admission. Obtain a real native quota lease and preserve it before another fallible
   operation, then transfer the policy reader into actual machine storage.
2. **Acquire the actual state-relative exclusion and reject a competing
   alias.** Open the typed exclusion with the actual borrowed storage and quota
   lease. Require its machine and full lease digests to match those owners.
   A competing actual lock acquisition must reject or return cleanup; retire
   its exact returned owner, then verify the first exclusion is still current.
3. **Close only this exclusion and keep both borrowed native owners current.**
   Require closed state without an owner or error and refuse later current
   checks. Re-read the machine policy through the still-live storage owner and
   observe the actual quota lease still retained with the same native binding.
4. **A closed alias cannot release a later canonical exclusion generation.**
   Acquire a new exclusion over the same actual root. Close the old alias
   again and require idempotent closed state; the new exclusion must remain
   current and a second real competitor must still be refused. Retire the new
   exclusion and the caller's machine storage. Leave the actual quota lease
   retained for reconciliation, without fabricated absence or release.

No native or runtime execution has occurred. Alias mount, fork, context-change,
unknown close and forced descriptor-reuse fault cases remain unqualified.
