# Windows Phase2 Object Collector Resume and Evidence Safety

**Status:** Proposed; canonical bug database registration pending
**Scope:** Host-side diagnostic collector in `scripts/bootstrap/collect-windows-phase2-objects.py`
**Source baseline:** Frozen at `25c`; no source or Phase2 producer changes are included.

## Changes in the Repair Copy

- The two workers now reserve rows by reading and incrementing one shared cursor while holding the same lock. This prevents duplicate dispatch under parallel workers.
- Campaign preamble events are written only for PENDING rows. A resumed PASS keeps its original object path, byte count, hash, and attempt count as the latest complete receipt. Rows whose inputs changed or whose previous object no longer validates remain eligible for a new PENDING/RUNNING attempt.
- AMD64 COFF and BigObj validation now checks section raw-data ranges against file bounds. Valid uninitialized `.bss` sections with a zero raw-data pointer remain accepted.
- Exit 89 is classified as a BLOCKED watchdog setup failure only when the supervisor log and RSS receipt show the specific compiler-identity installation refusal, `root_pid=0`, `samples=0`, and no bounded collector receipt. Other exit-89 results remain failures. Existing journal records are retained; no automatic retry policy was added.
- Cause excerpts include a bounded head, terminal diagnostic lines, and tail context, avoiding progress-only excerpts from the start of a long log.
- A `STOP_REQUEST` file in the work root stops dispatch before the cursor advances. Active jobs finish normally, undispatched rows remain PENDING, and the marker is retained.
- Optional `--priority-manifest` validates the inventory digest and all 165 logical row ID/path/physical-path/source-hash bindings, then schedules those six reviewed tooling roots first and preserves the complete 14,978-row inventory. The 14,813-row remainder stays in original order.

## Host Harness Evidence

The focused compiler-free harness passed **8 tests**. It covered concurrent unique dispatch, stop-before-dispatch, watchdog refusal controls, terminal log excerpts, COFF raw bounds and `.bss`, the real priority cohort plus invalid-hash/duplicate/missing-row controls, and retention of an existing real PASS receipt across two resume-state selections.

The real fixture paths were supplied through:

- `SIMPLE_PHASE2_REAL_INVENTORY`
- `SIMPLE_PHASE2_REAL_PRIORITY_MANIFEST`
- `SIMPLE_PHASE2_REAL_ATTEMPTS`

These point to the frozen campaign inventory, its reviewed ignored priority cohort, and the live campaign attempt ledger. The retained PASS check used an existing object and verified its COFF structure, recorded byte count, and recorded SHA-256. The harness invoked no compiler and does not claim source correctness, compiler qualification, or bootstrap admission.

## Read-Only PASS Object Audit

At `2026-10-27T07:29:16Z`, the latest terminal receipts in the campaign journal contained **52 PASS rows**. All **52 of 52** object files passed the final strict COFF/BigObj validator, and each object byte count and SHA-256 matched its receipt. There were **zero rejected objects**.

- Campaign: `c718ec0c9fbc4f25bdfe45181b7c4bc9`
- Inventory rows: `14,978`
- Inventory SHA-256: `ef538069e242e54e5ea95841cccc0e3e539720269e8f5dd0d36a867cfbfd2070`
- Attempt journal snapshot SHA-256: `a05424e904810534bdb5e7d0154f68cbc7a22675900675c05c4eab22a11afc65`

The audit read existing files and receipts only. It did not recompile objects or modify the journal. Structurally valid object files are diagnostic evidence, not proof that their source modules are correct.
