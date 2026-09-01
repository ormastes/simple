# x86 AP Trampoline Scalar Policy Contract

Source: `test/01_unit/os/kernel/arch/x86_ap_trampoline_policy_contract_spec.spl`

Evidence class: `source-contract`.

The spec pins exact physical-address and SIPI-vector agreement between Pure
Simple, the C AP startup owner, and the assembly trampoline. It also preserves
the fail-closed preparation branches and proves removal of both redundant C
scalar getters and active inventory debt. It is not runtime or MC/DC evidence.
