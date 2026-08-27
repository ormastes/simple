# nvme_cosmos_openssd_boot_spec pre-existing RED (2026-08-27)

test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl is RED at
HEAD and after the SSDOC-TRC-003 repair (score 49 -> 82, comment-only edits:
single per-scenario `# @req REQ-012 REQ-SSPEC-SYSTEM NFR-012` binding at
8-space indent, and de-mangling the `REQ-SSPEC-SYSTEM..NNN` range tokens in
inter-scenario comments that parsed as phantom unbindable ids).

Identical verdicts before and after (proven via in-place `git show HEAD:`
restore): `Results: 14 total, 7 passed, 7 failed`. Failing scenarios: NVMe IO
callback service, FTL metadata runner, NFC media binding, PCIe-to-NVMe bridge,
NVMe dispatcher, QEMU boot verdict, silicon profile build. Left RED per testing
rules. Mutation dual-check skipped as weak (spec already RED); edits touched
only comments so behavior is unchanged by construction.
