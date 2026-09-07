# TODO: [gpu][P2] Qualify Vulkan resident-2D device evidence with real timestamps and uploaded rows

Date: 2026-09-06
Lane: GPU scheduler hardening (plan doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md)
Rule: this may not be closed by a source scan, a routing receipt, or an interpreter run.

The resident slice really runs on this Mac: 16 frames through one never-grown arena on
Apple M4 via MoltenVK, 0 semantic rebuilds, 0 readbacks. It honestly reports
`qualifies=false` because the tree exposes no VkQueryPool timestamp externs and the packed
rows are not uploaded yet, so `transfer_bytes` is 0.

Closing evidence: a run whose receipt reaches `gpu_finished` with
`device_timestamp_available=true`, a begin/end tick pair written by `vkCmdWriteTimestamp`
around the resident dispatch, `transfer_bytes > 0` from a real per-frame upload, and the
negative control still refusing a stale generation.
