<!-- codex-design -->
# x86_32 privilege-transition ABI implementation tasks

Shared interface names are frozen by
`os.kernel.arch.x86_32.privilege_abi`: `X86_32PrivilegeTokenV1`,
`X86_32TrapDispositionV1`, and the `X86_32_TF_*` offsets.

1. Single assembly owner: install GDT/TSS, build the exact trap frame, and
   implement first entry plus the three disposition branches.
2. Single Simple owner: arm/validate/consume the token and dispatch syscall 60
   and exit 0 without effects before authentication.
3. Scheduler integrator: bind generation and address-space identity, then prove
   exit, collection, and cleanup ordering.
4. Test owner: add deliberate-red C layout checks and QEMU sabotage scenarios.

Sidecar lanes: N/A for the ABI and assembly choke points. Merge owner: x86_32
architecture maintainer. Final reviewer: highest-capability reviewer with i386
privilege-transition and Simple native-ABI knowledge. No agent may independently
renumber selectors, offsets, token states, or disposition actions.
