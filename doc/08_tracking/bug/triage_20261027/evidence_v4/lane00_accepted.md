# V4 lane 00 accepted evidence

Accepted classifications in V4: 161. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

- 160 accepted records are inherited field-for-field from V3; their detailed evidence is preserved in [V3 lane 00 evidence](../evidence_v3/lane00_accepted.md).

- 1 additional accepted records are detailed below.

## board_vulkan_lanes_fabricated_counterpart_output_despite_available_exec_api_2026-08-11 — Board-Vulkan lanes compared against fabricated counterpart output

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/board_vulkan_lanes_fabricated_counterpart_output_despite_available_exec_api_2026-08-11.md:227-278; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/gpu/board_vulkan/boundary_enumeration_provider.spl:285-299; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/gpu/board_vulkan/boundary_readback_lavapipe_provider.spl:57-90; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/gpu/board_vulkan/boundary_spirv_khronos_provider.spl:163-181; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/gpu/board_vulkan/provider_nvidia.spl:200-225; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/gpu/board_vulkan/provider_inventory.spl:203-227; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/09_report/board_vulkan_lane_redteam_audit_2026-08-11.md:84-115,203-245
```
- Review rationale: The historical enumeration/readback evidence defect remains valid even though the later report narrows it. The original red-team audit itself says L1 executes glslang, so the report opening never established that literally every lane fabricated output. Target Khronos assembly/validation executes bounded tools and fails unavailable/crashed; enumeration and readback repairs already established in the prior review remain applicable. The executed-source independence gate now keys on nonempty independence_group; inventory counting separately trusts declared manifest groups. August partial repair and September campaign-wide qualification are different scopes, not proof of one universal current fabrication mechanism. Keep the historical campaign record open with unknown aggregate remedy; no complete eight-lane execution/independence qualification was inspected.
- Review corrections: Accepted the conservative historical-valid/current-untested classification after separating campaign scope from repaired providers. No all-lane fixed or invalid claim; the original blanket statement is overbroad.
