# Missing explicit-address-space VMM helper cluster

Status: genuine historical implementation restored; runtime verification UNRUN.
Bug database reconciliation is pending a qualified full CLI.

The UI dependency closure reports missing `vmm_read_pte_in` and
`vmm_unmap_page_in`. The companion `vmm_replace_pte_in` is also required by
the existing device-mapping rollback owner. Transplant `bb3f6ab8ab2` removed
the coupled implementation from `vmm_address_space.spl`.

Restore the three exact bodies from parent
`1b24cb2a143a9dc683ada872ac68bd24f0f38839` into that same owner. The read walks
the supplied physical root and recognizes huge leaves. Replacement rejects
huge mappings, compares the expected old PTE, writes only a matching 4K leaf,
and invalidates the TLB. Unmapping requires PRESENT and performs expected-PTE
replacement with zero. No allocation, global-root forwarding, or CR3 switch
is introduced, and no new low-level FFI is needed.

The existing `memory_swap_address_space_isolation_spec.spl` checks two address
spaces at the same virtual address and preservation of the sibling mapping.
Those integration checks remain UNRUN; source equality is not runtime proof.
Exact normalized body hashes are retained in the external UI repair evidence.
