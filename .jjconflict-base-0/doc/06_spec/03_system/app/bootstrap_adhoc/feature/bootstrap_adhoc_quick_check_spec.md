# Worktree-local bootstrap ad-hoc quick check

The developer submits changed compiler paths. A local policy routes a safe
change to frontend, HIR, MIR, or backend evidence. Loader, interpreter, common
ABI, MDSOC, and weaving changes are rejected and require exact Stage4.

A passing check requires both a native positive capsule with an exact lane
marker and a negative capsule with its expected diagnostic. The resulting
receipt is explicitly developer-only and cannot authorize deployment.
