# SimpleOS nvme checker: multi-device preflight mis-flagged as duplicate field

**Status:** FIXED
**Found:** 2026-06-29 (noise sweep — simpleos_nvme_serial_check_spec)
**Area:** app / SimpleOS nvme serial checker (`src/app/simpleos_nvme_serial_check/main.spl`)

## Symptom

A preflight report describing **multiple NVMe devices** (two `device:` blocks)
was rejected with `physical-nvme-preflight-duplicate-field:model` instead of the
correct `physical-nvme-preflight-multiple-devices`.

## Root cause

`_preflight_identity_match_reason` ran the global duplicate-field check
(`_preflight_duplicate_field_reason`, which counts how many lines start with
`<field>: `) **before** the `_preflight_device_count() > 1` →
`multiple-devices` check. In a multi-device report each per-device field
(`model:`, `serial:`, `controller:`, …) legitimately appears once per device, so
the global count was ≥ 2 and the duplicate-field check fired first.

Confirmed via instrumentation: for the 2-device fixture the checker saw
`model=2 serial=2` and returned `duplicate-field:model`.

## Fix

Detect multiple devices before the duplicate-field check: right after the
`physical_nvme_preflight:` presence check, return `multiple-devices` when
`_preflight_device_count(preflight_report_text) > 1`. Single-device duplicate
detection is unaffected (count 1 → device check passes → duplicate check runs).

## Verification

The checker now writes the correct report to disk for the 2-device fixture:
`reason: physical-nvme-preflight-multiple-devices` / `preflight_identity_match:
false` (confirmed by reading the on-disk report). The spec's
`reason: …multiple-devices` assertion passes.

A separate, still-open issue blocks the spec from going fully green — see
`runtime_file_read_cache_stale_after_subprocess_write_2026-06-29.md`: the test
process reads back a *prior* report's content for this step even though the
on-disk file is correct. That is a runtime read-correctness bug, not a checker
bug.
