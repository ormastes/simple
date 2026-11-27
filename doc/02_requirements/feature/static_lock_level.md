# Static lock-level selected scope

REQ-MC-006 / ASYNC-LOCK-ORDER is selected by the user through the owning task.
The requirement is increasing lock levels with no source-only exception bypass.
This document refines the existing selected requirement; it does not select an
unrequested alternative requirement.

1. Existing `@lock_level(n)` grammar accepts one nonnegative decimal i64 on a
   named synchronous function or immutable module Mutex resource.
2. Synchronous function invocation holds its rank until return. Calls through
   direct local wrappers preserve effects. Lower-after-higher rejects; distinct
   equal ranks remain allowed, and ranked recursion rejects.
3. Resource rank requires a unique immutable module binding constructed through
   an explicit canonical `mutex_new` import. Canonical with_lock method/free
   wrappers acquire only for the inline callback lifetime; sibling calls release
   before the next acquisition. Same-resource nested acquisition rejects.
4. Initial protected values and every callback return must preserve a proven
   scalar invariant. The keeping helper must separately prove its keep argument.
5. Unsupported manual operations, indirect/imported effects, aliases, mutable
   bindings, callbacks, nominal operators, suspension and source exemptions fail
   closed within the checked boundary. Resource-ranked modules opt all functions
   and initializers into a closed-world proof.
6. Fresh/shared/native/cached parsing uses the same checker. Cache metadata is
   versioned, validated by declaration identity, reset and promoted with its owner.
7. Proof collection/graph work is finite; exhausting a budget rejects with E003.

Actual compiled SSpec execution and qualified compiler/native smoke evidence
remain mandatory before acceptance. General manual guard/RAII inference,
arbitrary alias analysis and reviewed exception manifests are unsupported and
must not be reported as implemented.
