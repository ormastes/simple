<!-- codex-design -->
# x86_32 privilege-transition ABI verification plan

The source-only phase runs `x86_32_privilege_abi_spec.spl` to freeze selectors,
TSS offsets, trap-frame offsets, token size, and disposition size. Its deliberate
short-frame sabotage proves a same-CPL `int80` layout cannot satisfy the CPL3
contract.

The later live phase must add emulator scenarios for valid nonce output/exit
37 and each rejection listed in the detail design. The release gate remains
fail-closed until those scenarios observe target-origin output, exact child
identity, scheduler collection, and post-reap page-directory destruction.
