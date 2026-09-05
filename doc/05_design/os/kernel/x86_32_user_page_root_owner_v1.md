# x86-32 Explicit User Page-Root Owner V1

One bounded, mutex-serialized capsule owns all create-issued page directories,
private page tables, and leaf-provenance registrations. A lease carries only
root/generation/nonce coordinates. Leaf frames are allocated inside the owner;
`RegisteredQuarantined` means it retained the frame but deliberately stopped
admitting operations. `CreatedQuarantined` still returns the root coordinates,
so an indeterminate unlock never loses the only ownership evidence.

Every mapped physical frame may occur in exactly one live leaf across all
roots. Exact virtual/physical identity is required to unregister it. Root
destruction is allowed only while unpublished and leaf-empty, frees private
tables before the root, and returns terminal `Destroyed` after physical release.

Classic two-level non-PAE i386 has no NX bit. The mapper enforces user/present,
rejects writable-plus-executable requests, exposes
`ExecuteDisableUnavailable`, and never claims read-only data is non-executable.
Every map receipt explicitly records `hardware_wx_enforced: false` and
`scheduler_adoption_permitted: false`; writable leaves permanently bar this v1
root from scheduler adoption.

This owner does not reserve scheduler adoption, install CR3, transfer to CPL3,
or perform terminal task teardown. Therefore its scheduler readiness stays
false and the global x86-32 filesystem-execution gate must not change.
