# RV32 NVMe NAND Recovery and Prevention Domain Research

**Date:** 2026-07-28

## Primary-source findings

1. Cai et al., *Threshold Voltage Distribution in MLC NAND Flash Memory*,
   characterizes read retry on FPGA-attached commercial NAND. Adjusting read
   reference voltage changes sensed values and can reduce errors after voltage
   distributions shift.
   <https://users.ece.cmu.edu/~omutlu/pub/flash-memory-voltage-characterization_date13.pdf>
2. Cai et al., *Data Retention in MLC NAND Flash Memory*, shows retention shifts
   optimal read reference voltages and proposes a block-granular starting level
   plus lower/higher searches selected by corrected-error count.
   <https://users.ece.cmu.edu/~omutlu/pub/flash-memory-data-retention_hpca15.pdf>
3. Cai et al., *Read Disturb Errors in MLC NAND Flash Memory*, shows disturb
   grows with read count and wear, motivates preventive voltage tuning/refresh,
   and demonstrates recovery by identifying cells near shifted thresholds.
   <https://users.ece.cmu.edu/~omutlu/pub/flash-read-disturb-errors_dsn15.pdf>
4. Cai et al., *Flash Correct-and-Refresh*, periodically reads, ECC-corrects,
   and remaps/reprograms data before retention errors exceed ECC capability.
   <https://users.ece.cmu.edu/~omutlu/pub/flash-correct-and-refresh_iccd12.pdf>
5. Micron's NAND guidance requires READ STATUS after PROGRAM and ERASE, block
   retirement/remap on failure, and refresh to mitigate repeated-read disturb.
   <https://www.micron.com/sales-support/sales/faqs>
6. NVM Express Base Specification 2.3 requires bounded memory-queue head/tail
   movement, full/empty handling, Completion Queue creation before an associated
   Submission Queue, and Submission Queue deletion before Completion Queue
   deletion. The RV32 scalar queue pair preserves those ordering and bounds
   invariants without reproducing PCIe transport registers.
   <https://nvmexpress.org/wp-content/uploads/NVM-Express-Base-Specification-Revision-2.3-2025.08.01-Ratified.pdf>

## Algorithm selected for RV32

The implementation carries the following controller invariants from the cited
work rather than copying a device-specific voltage table:

1. Read once at the nominal reference, then search bounded controller-owned
   ladders in both directions: retention `128,120,112,104` and disturb
   `128,136,144,152`. Search order never depends on the injected hidden level.
2. Convert threshold distance into a deterministic raw-error count. A retry is
   usable only when that count is within the configured ECC budget; exhausting
   the ladder is an uncorrectable read, not a guessed recovery.
3. Treat ECC correction and data validation as separate gates. Refresh is
   forbidden unless the read is correctable and the corrected payload equals
   the protected payload.
4. Follow FCR ordering: read, correct, erase, program at the nominal level, then
   read-verify. A primary verification failure retires that slot, programs and
   verifies the alternate slot, and switches the active mapping only on success.
5. Count reads at block scope because read disturb affects neighboring cells.
   At the prevention threshold, validate and refresh the modeled neighbor before
   its errors exceed the ECC budget.
6. Require device startup, live admin/I/O queues, bounded SQ/CQ movement, and
   explicit erase/program status before media commands can complete.

These are fail-closed safety rules. The retry references and ECC budget are
test constants, not values claimed for a particular NAND part; a production
target must calibrate them from its data sheet and characterization results.

## Model ceiling

The RV32 model is deliberately discrete and deterministic. It verifies firmware
control flow, state ordering, telemetry, retry, refresh, and fail-closed behavior.
The existing `hardware.nand_emu` Vt model remains the authority for distribution,
wear, retention-time, and cell-level characterization. The one-page RV32 image
contains one real alternate slot for fail-closed remap evidence; allocation and
copying across a production free-block pool remain owned by the full FTL, not
this bounded controller-policy test image.
