# OS variation plan index

OS axis: Windows, Linux, BSD/FreeBSD and SimpleOS service adapters. Its sibling
[filesystem axis](../filesystem/README.md) owns independent provider choices.
Native transport, handles, waiting and resource lifecycle belong to the OS
adapter; filesystem algorithms remain reusable across compatible OS adapters.

Work, status and exit evidence stay in the [existing Item 5 plan](../../runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md#2026-10-11-os-and-filesystem-variation-refinement),
with the [selected design](../../../../../05_design/compiler/perf/item5_shared_provider_interfaces_2026-10-09.md#2026-10-11-selected-os-and-filesystem-separation)
and [acceptance rows I5-V09/V10](../../../../sys_test/item5_provider_size_acceptance_2026-10-02.md#independent-osfilesystem-acceptance--2026-10-11).
This index adds no implementation or platform-support claim.
