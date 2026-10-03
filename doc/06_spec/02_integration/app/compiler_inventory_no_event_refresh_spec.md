# Warm SCV refresh with no events

Executable specification: `test/02_integration/app/compiler_inventory_no_event_refresh_spec.spl`.
Requirement: REQ-SCV-WARM-NO-EVENT-REFRESH. Runtime status: **UNRUN**.

Each scenario creates its own small Git checkout under `build/test-artifacts`.
No live checkout, source inventory, or compiler cache is reused.

| Scenario | Steps and observable result |
| --- | --- |
| Unchanged refresh, then edit | Commit one source, cold-admit it, and refresh without events. Compare complete encoded inventory, digest, generation, and cursor. Edit the tracked file and require a new generation with its actual content digest. |
| Publication race | Capture the old cursor, publish the edit, and submit the old cursor to the production publication-lock operation. Require `publish-cursor-superseded`, unchanged new cursor, and a successful subsequent lock acquisition. This deterministically tests stale expected-pointer handling; it does not claim a concurrent scheduler test. |
| Complete pointer bytes | Append an embedded NUL and suffix to CURRENT after capturing it. Require digest-bound revalidation to reject the changed bytes, preserve them without repair, and release the lock for successful admission after restoration. |
| Blob corruption | Alter the referenced inventory file without changing CURRENT. Both locked revalidation and full refresh must reject it; neither repairs or publishes over the corruption. Restore it and require successful admission. |
| Journal changes | Append a source-free checkpoint. Require cursor advancement despite zero source events. An unchanged retry preserves it; rewriting the consumed prefix with the same row count must fail. |
| Cursor normalization and Git changes | Give the row count a leading zero and require canonical publication. Then create an empty commit and require the Git cursor to advance while the inventory digest and generation remain unchanged. |

These are behavioral admission controls. They do not measure elapsed time or RSS.
The avoided decode/encode count is established by source call-chain inspection;
native execution and measured warm-startup performance remain separate gates.
