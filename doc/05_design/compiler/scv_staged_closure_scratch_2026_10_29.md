# Staged coordinator closure scratch ownership

The coordinator formerly held one transient scope across source-authority reopening, the closure walker, selection construction and final physical admission. The inventory reader cannot acquire a nested scope, so each complete decode/hash graph remained live until the entire transaction ended. Removing canonical re-encoding reduces one graph, but does not fix that lifetime.

The parent now uses four sequential transient scopes:

1. Reopen and authenticate the inherited authority; adopt the small authority record into the transaction's session and retire its scratch.
2. Walk the closure and check its exact snapshot/root mapping; adopt only the selected path/root carrier and retire scan/admission scratch.
3. Prepare the selected records using the authenticated inventory; adopt the binding/selection carrier and retire its first inventory read.
4. Independently reauthenticate the original generation and manifest, then publish the selection/request records. No cached proof replaces this final read.

`compiler_entry_closure_prepare_v1` exposes the first half of selection. The existing `compiler_entry_closure_select_v1` remains prepare followed by physical admission, so other callers preserve their behavior. The coordinator invokes those same operations across a reclamation boundary.

The session contains only intermediate handoffs. An active compiler epoch, active/paused caller scope, or borrowed session refuses parent publication before cache mutation. The lower scratch helper can represent a borrowed session and never retires it; the coordinator requires an independent session because its global cache reset containers must not outlive another caller's owner.

Before every scope retirement, pause allocation, detach driver scan, snapshot-memo and host-path globals, adopt the handoff, and end the scope once. Failed adoption still attempts scope retirement. A failed retirement is never retried as though it were a new scope. Failure does not launch descendants or preserve publication authority.

Session semantics matter: allocation while paused belongs to the live session, and runtime promotion under a session is adoption rather than permanent escape. Therefore final publication fields are consumed while alive: `env_set` copies path/digest/consumer marker into the OS environment, and errors are printed before retirement. Then the final scope and session are retired. Cache globals are assigned fresh empty containers again after successful session retirement, without traversing their old contents. Only a scalar selected count survives; the success log reads the independently copied digest back from the environment. Cleanup failure clears publication markers and returns failure.

## Evidence and limits

The native helper fixture uses actual production session helpers and current core-C allocation. It measures monolithic versus staged scope peaks, exercises nested struct/array adoption, refusal and failed-adoption cleanup, and verifies environment-copy/cache-reset lifetime.

The assembled native coordinator probe copies production owner/helper functions verbatim, removing only imports. Deterministic domain fixtures replace filesystem authority, walking and publication services, while actual C scopes, sessions and OS environment copies execute. The original owner fails the 2,000-object ceiling at 4,095; the staged owner passes at 1,077. It also checks four-stage order, handoff contents, borrowed-session refusal and failed final admission cleanup. This is source-owner lifetime evidence, not a real full-inventory compiler run.

Three interpreter examples exercise real inventory publication and real selection/admission: valid parity with the existing wrapper, generation corruption between preparation and admission, and manifest corruption in that interval.

The pinned P1 native diagnostic needs an explicit initialization shim and a fail-closed Darwin thread marker. The current-C session selfcheck passes, but full capsule admission fails later on an unrelated pool-closure linker dependency; this archive is diagnostic only. Phase2 remains unchanged. The original 16 MiB coordinator workload and a source-matched full compiler still require qualification; no Phase2 or whole-process RSS acceptance is asserted.
