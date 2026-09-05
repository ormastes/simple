# NAND SSD Cell-Recovery and Failure-Prevention Algorithms — Taxonomy

**Status:** research (2026-07-19). Companion docs:
`nand_recovery_gap_analysis_local.md` (mapping onto this repo's fw + nand_emu),
`doc/04_architecture/hardware/nand_recovery/reliability_engine_architecture.md`
(the flexible FTL/FIL-placeable design derived from this taxonomy).

Below is a near-exhaustive taxonomy of the publicly documented techniques used
or proposed for NAND SSDs. A literally complete list is not possible because
NAND vendors keep many voltage tables, retry sequences, ECC policies, and
failure thresholds proprietary. Academic literature also contains many minor
variations of the same underlying methods.

A useful distinction is:

**Recovery algorithms** try to recover data after the initial NAND read is
unreliable or has failed.

**Prevention algorithms** reduce the creation of errors, delay wear-out, or
move data before errors exceed ECC capability.

Most "cell recovery" restores readability of the data, not the original
physical condition of the oxide or charge-trap cell. Erase/reprogram,
dwell-based self-recovery, controlled heating, and experimental reprogramming
schemes are the main exceptions.

---

## 1. The normal NAND recovery ladder

A modern SSD typically escalates through approximately this sequence:

1. Perform a normal hard-decision read.
2. Decode with BCH or hard-decision LDPC.
3. Change one or more read-reference voltages, or Vref, and retry.
4. Gather several reads to construct soft information or log-likelihood ratios.
5. Run soft-decision LDPC decoding.
6. Apply failure-specific recovery, such as retention-, disturb-, neighbor-,
   layer-, or page-type-aware correction.
7. Reconstruct the page using RAID/RAIN, parity, or an erasure code.
8. Rewrite the corrected data to a fresh location.
9. Retire or quarantine the weak page, wordline, block, die, or chip.
10. Return an uncorrectable error only after the available recovery paths are
    exhausted.

Public recovery studies such as ROR/RFR, RDR, ReMAR/ReNAC, and the 3D-NAND
variation-aware methods cover several stages of this ladder.

---

## 2. Recovery algorithms

### 2.1 Read-reference-voltage recovery

NAND states are separated by read-reference voltages. Retention, cycling,
temperature, process variation, interference, and read disturb shift or
broaden the threshold-voltage distributions. The controller therefore searches
for better decision boundaries.

| Algorithm family | Variants |
|---|---|
| Fixed read retry | Try a manufacturer-defined sequence of positive and negative Vref offsets. |
| Linear Vref sweep | Move each reference voltage in fixed steps until ECC succeeds. |
| Bidirectional search | Search above and below the nominal reference. |
| Binary or interval search | Narrow the likely voltage interval rather than examining every offset. |
| Gradient or hill-climbing search | Use corrected-bit counts or syndrome information to decide the next direction. |
| Valley search | Estimate the low-density valley between adjacent threshold-voltage distributions. |
| Table-based retry | Select a retry table according to NAND model, page type, layer, P/E count, temperature, or data age. |
| Adaptive retry ordering | Try the voltage offsets most likely to succeed first. |
| ECC-margin-guided retry | Use the previous decoder margin, syndrome weight, or corrected-bit count to determine the next read. |
| Distribution-estimation retry | Estimate threshold-voltage distributions and derive the likely optimal boundaries. |
| Model-predictive retry | Predict Vref from retention age, wear, layer, temperature, and prior observations. |
| Machine-learning Vref prediction | Regression, neural-network, or meta-learning models predict the next read thresholds. |

**Named read-retry schemes**

- PR² — Pipelined Read-Retry: overlaps retry operations through NAND
  cache-read behavior.
- AR² — Adaptive Read-Retry: shortens individual retry steps when ECC
  information indicates that a full retry operation is unnecessary.
- Near-Zero Read Retry: creates a tailored retry table for a NAND model,
  dynamically selects promising entries, and performs a local proximity search.
- Novel Valley Search: estimates a suitable read boundary with fewer reads
  than a conventional valley search.
- Sentinel-cell methods: reserve or identify representative cells whose shifts
  predict the movement of the wider threshold-voltage distribution.
- ORVD-WRRO/OER-ECC methods: infer optimal read voltages from error or ECC
  observations, attempting to avoid a separate exhaustive retry sweep.

PR², AR², near-zero retry, and valley-search work are representative public
designs in this category.

### 2.2 Retention-aware read recovery

Retention errors arise as stored charge changes while data remains idle.
Different cells, blocks, layers, temperatures, and wear levels exhibit
different retention behavior.

**Named schemes**

- ROR — Retention Optimized Reading: learns the optimal read-reference voltage
  for each block and uses it for subsequent reads.
- ReMAR — Retention Model Aware Reading: models threshold-voltage movement as
  a function of retention age and adjusts read references accordingly.
- HeatWatch: combines retention age, dwell time, temperature history, and wear
  information to select better read thresholds.
- Age-aware read retry: organizes retry tables by estimated time since
  programming.
- Temperature-compensated reading: corrects references according to
  programming and reading temperatures.
- P/E-aware reading: maintains different references for blocks at different
  wear levels.
- Per-page or per-wordline calibration: maintains finer-grained reference data
  than a single per-die or per-block value.

ROR, ReMAR, and HeatWatch demonstrate progressively richer retention models,
from per-block calibration to age-, temperature-, dwell-, and wear-aware
prediction.

### 2.3 Layer-, wordline-, and process-variation-aware recovery

Three-dimensional NAND exhibits systematic differences across vertical layers,
wordlines, strings, and manufacturing locations.

- LaVAR — Layer Variation Aware Reading: uses layer-specific read-reference
  voltages.
- Per-layer retry tables: different voltage offsets are stored for weak,
  nominal, and strong layers.
- Per-wordline calibration: tracks the error behavior of individual wordlines.
- Page-type-aware reading: applies different policies to lower, middle, upper,
  or extra pages within TLC/QLC cells.
- String-position-aware reading: compensates for top, middle, and bottom
  string variation.
- Die/chip-specific calibration: learns separate models for different dies or
  packages.
- Process-corner classification: groups blocks by measured threshold-voltage
  or RBER characteristics.
- Online Vref learning: updates calibration from successful retries and ECC
  correction statistics.

LaVAR is a canonical public example of exploiting systematic 3D-NAND layer
variation.

### 2.4 Soft sensing and threshold optimization

A hard read produces one bit decision for each sensing boundary. Soft decoding
performs multiple reads around the expected boundary and converts the sequence
into reliability information.

**Soft-read algorithms**

- Uniformly spaced multiple reads.
- Nonuniformly spaced multiple reads.
- Adaptive number of sensing levels.
- Decoder-feedback-directed sensing.
- Syndrome-weight-directed sensing.
- Error-count-directed sensing.
- Page-type-specific sensing.
- Layer-specific sensing.
- Retention-age-specific sensing.
- Temperature-aware sensing.
- RBER-aware multi-sensing.
- Mutual-information-maximizing, or MMI, threshold selection.
- Entropy-maximizing threshold selection.
- Threshold-voltage-distribution estimation.
- Gaussian-mixture or parametric distribution fitting.
- Maximum-likelihood boundary estimation.
- Expectation-maximization distribution estimation.
- Neural-network or learned threshold estimation.

**Named schemes**

- EBDN — Entropy-Based Double Nonuniform sensing: uses nonuniform sensing
  points chosen to improve soft information for LDPC decoding.
- VaLLR: calibrates log-likelihood ratios using the observed or estimated
  threshold-voltage distribution.
- DNN-aided threshold optimization: predicts useful read thresholds using a
  neural model.
- Cross-iterative search: alternates between distribution or decoder estimates
  and threshold selection.
- RBER-aware multi-sensing: changes the number and positions of reads
  according to estimated raw error rate.

MMI-based quantization, entropy-based nonuniform sensing, and learned
threshold optimization all seek more useful soft information with fewer NAND
reads.

### 2.5 Error-correcting-code recovery

**Classical ECC families**

- Parity and CRC: primarily error detection rather than strong correction.
- Hamming codes: correction of small error counts; historically useful for SLC
  and small metadata.
- BCH codes: common in earlier SLC/MLC NAND generations and still useful for
  metadata or low-error modes.
- Reed–Solomon codes: symbol-level correction and erasure recovery.
- Product codes: combine row and column codes.
- Interleaved codes: distribute clustered errors across multiple codewords.
- Convolutional and turbo codes: researched less commonly than BCH or LDPC for
  SSD data paths.
- Polar codes: researched for flash channels but not the dominant commercial
  SSD code.
- LDPC codes: dominant public research direction for high-density TLC and QLC.

**Hard-decision LDPC decoding**

- Gallager-A and Gallager-B decoding.
- Basic bit-flipping.
- Weighted bit-flipping.
- Modified weighted bit-flipping.
- Reliability-ratio-based bit-flipping.
- Gradient-descent bit-flipping.
- Probabilistic bit-flipping.
- Syndrome-weight-guided bit-flipping.
- Multi-bit flipping.
- Adaptive threshold bit-flipping.
- Early-termination hard decoding.
- Double-hard-decision decoding.

**Soft-decision LDPC decoding**

- Sum-product or belief-propagation decoding.
- Log-domain belief propagation.
- Min-sum decoding.
- Normalized min-sum.
- Offset min-sum.
- Layered min-sum.
- Quantized min-sum.
- Finite-alphabet iterative decoding.
- Scheduled or residual belief propagation.
- Early termination.
- Adaptive iteration limits.
- Decoder-state reuse between retry reads.
- LLR rescaling and calibration.
- Error-floor mitigation.
- Erasure-assisted LDPC.
- Chase-like candidate decoding.
- Joint sensing and decoding.
- Hybrid hard/soft decoding.

**Adaptive code management**

- Variable code rate.
- Variable parity length.
- Shortened or punctured LDPC.
- Adaptive codeword size.
- Adaptive iteration count.
- Layer-specific ECC strength.
- Page-type-specific ECC strength.
- Retention-aware ECC allocation.
- Wear-aware ECC allocation.
- Error-mode-aware parity allocation.
- Dynamic transition from hard to soft decoding.

**Named NAND-oriented ECC schemes**

- ALCod: adapts LDPC coding to inter-layer RBER variation.
- CooECC: cooperatively uses information across related pages to reduce
  decoding latency.
- DHD: double-hard-decision decoding.
- LLD: reduces hard-decision LDPC read/decoding latency.
- EMAL: error-mode-aware LDPC configuration.
- REAL: retention-error-aware LDPC.
- BeLDPC: bit-error-aware adaptive-rate LDPC.
- DyLDPC: dynamically changes correction behavior using temporal and spatial
  RBER information.
- SSALDPC: uses syndrome-sum information to adapt decoding.
- Variable-dimensional LDPC: changes LDPC dimensions or coding granularity
  according to reliability.
- Pair-bit-error-aware LDPC: models correlated errors between bits stored in
  one multilevel cell.
- Asymmetric-error-aware LDPC: accounts for unequal transition probabilities
  among programmed states.
- Inter-page LDPC: exploits relationships among lower, middle, and upper
  pages.
- Adaptive-rate LDPC: strengthens or weakens the code according to measured
  wear or error rate.

These are representative named NAND-specific designs; the number of decoder
scheduling, quantization, code-construction, and bit-flipping variants is
effectively unbounded.

### 2.6 Neighbor-cell and interference-aware recovery

Adjacent cells influence each other through capacitive coupling, program
interference, lateral charge migration, and other mechanisms.

- NAC — Neighbor-cell-Assisted Correction: reads neighboring-cell states and
  modifies the target cell's read references.
- ReNAC — Retention-interference-aware NAC: combines neighbor-state
  information with retention behavior.
- Previous-wordline-assisted correction: uses the state of the earlier
  programmed wordline.
- Next-wordline-assisted correction: compensates for interference caused by
  later programming.
- Adjacent-string-assisted correction.
- Paired-page-assisted correction.
- Program-order-aware correction.
- State-dependent interference tables.
- Linear interference cancellation.
- Nonlinear interference modeling.
- Predistortion-aware readback.
- Post-compensation: estimates interference after programming and adjusts
  sensing thresholds.
- Joint detection: jointly estimates target and neighboring cell states.

ReNAC is the principal 3D-NAND public example that combines retention and
neighbor-cell interference information.

### 2.7 Failure-mode-specific probabilistic recovery

These methods identify cells whose behavior matches a particular failure
mechanism and selectively invert or reinterpret the most likely erroneous
bits.

- RFR — Retention Failure Recovery: distinguishes cells with relatively fast
  and slow charge leakage, identifies likely retention errors, and
  probabilistically changes the most suspicious decisions until ECC can decode
  the page.
- RDR — Read Disturb Recovery: identifies cells especially susceptible to read
  disturb and probabilistically corrects likely disturb-induced errors.
- Program-interference recovery: identifies transitions likely caused by later
  neighboring programming.
- Asymmetric-transition correction: prioritizes error directions known to be
  more likely for a particular NAND state.
- State-transition-probability decoding: incorporates a channel transition
  matrix into ECC likelihoods.
- Error-location ranking: ranks cells by voltage margin, state, layer,
  neighbor state, or prior history.
- Candidate-pattern search: tests likely bit-flip combinations and validates
  them with ECC or CRC.
- Erasure marking: marks uncertain cells as erasures rather than forcing hard
  zero/one decisions.
- Failure-signature classification: classifies a page as retention-, disturb-,
  interference-, or wear-dominated before selecting a recovery procedure.

RFR and RDR are canonical examples of failure-mechanism-aware probabilistic
recovery.

### 2.8 Cross-page, cross-die, and parity recovery

When the physical page cannot be decoded by itself, the SSD can recover it
from higher-level redundancy.

- RAID-4/5-style parity.
- RAID-6-style dual parity.
- RAIN — Redundant Array of Independent NAND.
- Stripe parity across channels.
- Parity across dies or packages.
- XOR parity.
- Reed–Solomon erasure coding.
- Local reconstruction codes.
- Hierarchical parity.
- Metadata mirroring.
- Page replication.
- Superpage parity.
- Inter-plane parity.
- Cross-layer parity.
- Dynamic parity placement.
- Failure-domain-aware stripe placement.
- Parity scrubbing.
- Degraded-read reconstruction.
- Erasure decoding after identifying a failed page, block, die, or chip.
- LI-RAID — Layer-Interleaved RAID: distributes pages from different 3D layers
  across a parity group so that weak layers are not concentrated in one
  stripe.
- Cooperative page decoding such as CooECC.

LI-RAID directly addresses layer-dependent reliability variation rather than
treating every physical page as equally reliable.

### 2.9 Read repair, remapping, and retirement

After data has been corrected, the controller normally prevents the next read
from depending on the same weak physical location.

- Read repair: rewrite corrected data after a high-correction read.
- Read reclaim: migrate valid pages from a read-disturbed block.
- Refresh rewrite: copy data to a newly erased block.
- In-place reprogramming: add charge without erase where the device permits it.
- Block remapping: redirect the logical address to another block.
- Page remapping: use page-level mapping where supported by the FTL.
- Wordline remapping or salvage.
- Sub-block remapping.
- Partial-block salvage: preserve usable portions of a block.
- Weak-page quarantine.
- Weak-wordline quarantine.
- Runtime bad-block retirement.
- Spare-block substitution.
- Die or chip retirement.
- Progressive retirement: first lower the usable cell mode or capacity, then
  retire.
- RAID rebuild: reconstruct and relocate all data from a weak die or package.

Commercial controllers normally combine ECC, bad-block management, wear
leveling, remapping, and spare capacity rather than treating them as
independent features.

### 2.10 Physical or quasi-physical cell recovery

These techniques alter the stored charge or exploit partial physical recovery
rather than only changing the read interpretation.

- Erase and reprogram.
- Copy-erase-rewrite.
- In-place charge top-up or reprogramming.
- Incremental reprogramming of marginal states.
- Dwell-based self-recovery.
- Recovery-aware idle scheduling.
- Thermal annealing or controlled heating.
- Targeted heating of highly worn blocks.
- Relaxation before reuse.
- Reuse scheduling based on measured self-recovery.
- Cell-mode downgrade followed by reprogramming.
- Experimental dense-to-sparse or sparse-to-dense reprogramming.

**Named schemes**

- CellRejuvo: experimentally reprograms the most error-prone state using
  dense/sparse cell-state manipulation to recover retention-aged cells.
- Opportunistic Self-Healing: schedules block reuse so that idle periods allow
  partial recovery from trapped-charge effects.
- SREA — Self-Recovery Effect-Aware wear leveling: accounts for dwell and
  recovery when choosing blocks.
- SmartHeating: proposed targeted heating to accelerate self-recovery.
- HeatWatch: models temperature and dwell effects while managing retention
  reliability.

These do not restore a NAND cell to factory-new condition; they seek partial
recovery, better state separation, or a longer usable lifetime.

---

## 3. Prevention algorithms

### 3.1 Program-operation prevention

These mechanisms prevent programming from creating unnecessarily broad
distributions or disturbing unselected cells.

**Pulse and verify algorithms**

- ISPP — Incremental Step Pulse Programming.
- Program-and-verify.
- Adaptive ISPP step size.
- Variable program-pulse amplitude.
- Variable pulse duration.
- Early program termination.
- Fine-grained verify thresholds.
- State-specific verify thresholds.
- Layer-specific verify thresholds.
- Wear-aware verify thresholds.
- Temperature-aware program compensation.
- Closed-loop program control.
- Fail-bit-count-guided programming.
- Slow-program mode for weak blocks.
- Reduced-voltage program mode.
- Dynamic program latency.
- Coarse/fine programming.
- One-shot programming.
- Two-step programming.
- Foggy-fine programming.
- Multi-pass programming.
- Lower-page-first programming.
- Page-order optimization.
- Wordline-order optimization.
- Shadow programming sequences.
- Program-suspend scheduling.
- Interference-aware program scheduling.

**Program-inhibit and self-boosting**

These are typically NAND-die internal rather than SSD-FTL algorithms:

- Global self-boosting.
- Local self-boosting.
- Natural local self-boosting.
- Erased-area self-boosting.
- Revised erased-area self-boosting.
- Drain-side self-boosting.
- Channel precharge.
- Asymmetric pass-voltage boosting.
- Positive bitline inhibit.
- Dummy-wordline bias optimization.
- Select-gate timing optimization.
- String-position-aware inhibit.

Self-boosting raises the unselected string channel potential so that
unselected cells see less effective programming voltage, although poor bias
selection can itself create program-disturb mechanisms.

**Program-voltage scaling**

- DVA — Dynamic Voltage Allocation: starts with lower target threshold
  voltages and increases them as the device ages.
- DPES — Dynamic Program and Erase Scaling: adjusts program and erase
  conditions rather than always using worst-case pulses.
- Adaptive target-state spacing.
- Reduced target voltage for short-lived data.
- Retention-relaxed programming.
- Hot-data fast programming.
- Cold-data high-retention programming.
- Per-layer program-voltage compensation.
- Per-state program-voltage compensation.
- Workload-aware program modes.

DPES jointly controls program and erase stress, while DVA reallocates
threshold-voltage margins over the device lifetime.

### 3.2 Erase-operation prevention

Erase operations significantly contribute to oxide and charge-trap wear.

- Incremental step-pulse erase.
- Erase-and-verify.
- Adaptive erase pulse count.
- Adaptive erase voltage.
- Adaptive erase duration.
- Fail-bit-count-guided erase.
- Early erase termination.
- State-aware erase verification.
- Layer-aware erase control.
- Weak-wordline-aware erase.
- Partial or sub-block erase where hardware supports it.
- Deferred erase.
- Batch erase scheduling.
- Erase suspension and resumption.
- Recovery-aware erase scheduling.
- Lower-stress erase for lightly worn blocks.

**Named schemes**

- DeVTS — Dynamic Erase Voltage and Time Scaling: scales both erase voltage
  and erase duration.
- AERO — Adaptive ERase Operation: predicts a suitable erase duration from
  fail-bit observations.
- GuardedErase: selectively lowers erase voltage for weak wordlines to reduce
  wear.
- DPES: jointly scales program and erase stress.

These methods reduce over-erasing: applying stronger or longer erase pulses
than a particular block actually requires.

### 3.3 Retention-error prevention and refresh

**General refresh algorithms**

- Fixed-period refresh.
- Per-block refresh.
- Per-page refresh.
- Per-wordline refresh.
- Background scrubbing.
- Read-correct-rewrite.
- Read-correct-remap.
- In-place reprogramming refresh.
- Adaptive refresh interval.
- Retention-age-triggered refresh.
- Temperature-triggered refresh.
- P/E-count-triggered refresh.
- ECC-correction-count-triggered refresh.
- RBER-triggered refresh.
- Weak-block-triggered refresh.
- Workload-aware refresh.
- Idle-time refresh.
- Priority-based refresh.
- Deadline-based refresh.
- Energy-aware refresh.
- QoS-aware refresh.
- Hot/cold-data-specific refresh.
- Different refresh policies for lower, middle, upper, and extra pages.
- Refresh suppression for data expected to be overwritten soon.

**FCR family**

FCR — Flash Correct-and-Refresh periodically reads data, corrects errors, and
restores the data before the accumulated errors exceed ECC capability.

Its principal variants are:

- Remapping-based FCR: migrate the corrected data to another block.
- Reprogramming-based FCR: reprogram corrected data in place where safe.
- Hybrid reprogramming/remapping FCR: reprogram while safe, then remap when
  necessary.
- Adaptive-rate FCR: change the refresh interval according to wear and
  expected retention behavior.

**Additional named schemes**

- DEAR — Dynamic Error-Aware Refresh: monitors runtime error behavior and
  selectively refreshes data rather than relying only on a fixed offline
  read-count threshold.
- WARM: separates write-hot and write-cold data; frequently rewritten data can
  use relaxed retention requirements and avoid unnecessary refresh.
- HeatWatch: uses temperature, dwell, age, and wear when estimating retention
  risk.
- ReMAR: prevents repeated retry failures through retention-model-based
  reading.
- ROR: reduces retention-induced errors at read time using calibrated
  reference voltages.

### 3.4 Read-disturb prevention

Repeatedly applying pass voltage to unselected cells can gradually shift their
threshold voltages.

**Basic techniques**

- Per-block read counters.
- Per-wordline read counters.
- Per-page read counters.
- Read-hotness detection.
- Disturb accumulation models.
- Read-count thresholds.
- Wear-dependent read thresholds.
- Temperature-dependent thresholds.
- Page-type-dependent thresholds.
- Read leveling or scattering.
- Replication of extremely read-hot data.
- Migration of read-hot data.
- Read reclaim.
- Selective page refresh.
- Selective wordline refresh.
- Block refresh.
- Read throttling.
- Read scheduling.
- Read caching in DRAM or SLC.
- Buffering repeatedly read data.
- Co-location with write-hot data so that normal garbage collection resets
  disturb accumulation.

**Pass-voltage control**

- Static Vpass reduction.
- Selective Vpass reduction.
- Dynamic per-block Vpass tuning.
- Per-wordline Vpass tuning.
- Page-type-aware Vpass.
- Wear-aware Vpass.
- Read-count-aware Vpass.
- Adaptive pass-voltage margining.
- Minimum-safe-Vpass search.
- Closed-loop Vpass calibration.

Dynamic pass-voltage tuning seeks the lowest pass voltage that still turns on
unselected cells without causing excessive read errors.

**Named read-disturb prevention schemes**

- STRAW: tracks accumulated read-disturb stress by wordline and reclaims the
  most heavily disturbed wordlines rather than indiscriminately refreshing an
  entire block.
- SWEEP: places read-hot and write-hot data together so that garbage
  collection caused by writes also resets read-disturb accumulation.
- Cocktail: combines data with different access characteristics to reduce the
  number of explicit read-reclaim operations.
- Minato: uses read-disturb-aware dynamic buffer management to retain heavily
  read data outside NAND longer.
- FineRR-ZNS: provides fine-grained read refresh for zoned SSDs using
  block-level remapping and zone reconstruction.
- Shuffler: manages read reclaim at superblock granularity.
- Read Refresh Scheduling and Data Reallocation: coordinates refresh timing
  and data placement to reduce the performance and endurance costs of read
  reclaim.
- Read leveling: scatters heavily read data so that disturb stress is not
  concentrated on a small number of blocks.

### 3.5 Program-interference and lateral-charge prevention

- Program-order scheduling.
- Shadow program sequence.
- Two-step or foggy-fine programming.
- Neighbor-state-aware programming.
- Program-voltage predistortion.
- Post-program compensation.
- Verify-threshold adjustment.
- Inter-wordline delay.
- Data-pattern-aware programming.
- Restricted state transitions.
- Weak-state avoidance.
- Alternate Gray mappings.
- State balancing.
- Lower-voltage programming for vulnerable layers.
- Neighbor-aware page placement.
- Z-interference-aware bias control.
- Dummy-wordline optimization.
- String-end compensation.
- Lateral-charge-spreading-aware randomization.

### 3.6 Data encoding and state-mapping prevention

The binary representation determines how often each physical threshold state
is used and which state transitions correspond to particular bit errors.

**General methods**

- Data scrambling.
- Data whitening.
- Conventional randomization.
- Gray coding.
- Alternative Gray mappings.
- Dynamic Gray mapping.
- State-aware mapping.
- Page-aware mapping.
- Layer-aware mapping.
- Wear-aware mapping.
- Asymmetric-error-aware coding.
- State balancing.
- Charge-balancing codes.
- Constant-weight codes.
- Constrained codes.
- Run-length-limited codes.
- Write-once-memory, or WOM, codes.
- Error-avoiding codes.
- Crosstalk-avoiding codes.
- Low-energy programming codes.
- Retention-aware codes.
- Read-disturb-aware codes.
- Unequal-error-protection codes.
- Cold-data encoding.
- Hot-data encoding.
- Compression before programming.
- Dynamic entropy coding.
- Huffman-based reliable state assignment.
- Bit inversion to avoid unfavorable patterns.

**Named schemes**

- MGC — Multiple Gray Code: chooses among multiple Gray mappings according to
  current NAND behavior.
- STAR — State-Aware Randomizer: avoids data patterns associated with
  vulnerable state distributions and lateral charge spreading.
- ColdCode: encodes long-lived cold data into patterns with lower measured raw
  error rates rather than using purely random state distributions.
- Dynamic Huffman reliable coding: assigns more common data symbols to more
  reliable physical-state combinations.
- PEAR-type inter-page-aware mapping/read schemes: account for unequal
  reliability among pages represented by the same multilevel cells.

### 3.7 Wear-leveling algorithms

**Basic wear leveling**

- Dynamic wear leveling: select among erased/free blocks for incoming writes
  according to wear.
- Static wear leveling: periodically move cold data from lightly worn blocks
  so those blocks can participate in future writes.
- Global wear leveling.
- Local wear leveling.
- Plane-aware wear leveling.
- Die-aware wear leveling.
- Channel-aware wear leveling.
- Chip-aware wear leveling.
- Layer-aware wear leveling.
- Wordline-aware wear leveling.
- Page-type-aware wear leveling.
- Superblock wear leveling.

**Workload- and reliability-aware variants**

- Hot/cold data separation.
- Multi-temperature data classification.
- Write-frequency-aware placement.
- Lifetime-aware placement.
- Retention-aware placement.
- Read-disturb-aware placement.
- Error-count-aware wear leveling.
- RBER-aware wear leveling.
- Bad-block-risk-aware wear leveling.
- ECC-margin-aware wear leveling.
- Temperature-aware wear leveling.
- Self-recovery-aware wear leveling.
- Differential wearing.
- Adaptive differential wearing.
- Unequal wear allocation according to block quality.
- Weak-layer avoidance.
- Weak-wordline avoidance.
- Capacity-aware wear leveling.
- SLC/TLC/QLC-mode-aware wear leveling.

**Named schemes**

- SREA: includes self-recovery or dwell effects in wear-leveling decisions.
- LaVA — Layer Variation Aware bad-block management: considers systematic
  3D-layer reliability differences.
- WARM: places write-hot and write-cold data in different block pools to
  exploit their different retention requirements.
- DVA: dynamically allocates threshold-voltage margin over device lifetime.
- GuardedErase, DPES, DeVTS, and AERO: reduce the damage associated with each
  P/E cycle.

### 3.8 Write-amplification prevention

Reducing physical writes indirectly prevents cell wear.

**Garbage-collection algorithms**

- Greedy victim selection.
- Cost-benefit garbage collection.
- Age-based garbage collection.
- Hotness-aware garbage collection.
- Wear-aware garbage collection.
- Error-aware garbage collection.
- Retention-aware garbage collection.
- Layer-aware garbage collection.
- Page-type-aware garbage collection.
- Valid-page-count-based selection.
- Expected-reclamation-benefit selection.
- Partial garbage collection.
- Incremental garbage collection.
- Background garbage collection.
- Idle-time garbage collection.
- QoS-aware garbage collection.
- Tail-latency-aware garbage collection.
- Channel-parallel garbage collection.
- Zoned garbage collection.
- Parity-aware garbage collection.
- Read-disturb-reset-aware garbage collection.

**Other write-reduction methods**

- Over-provisioning.
- TRIM/deallocate.
- Write coalescing.
- Write buffering.
- Log-structured mapping.
- Hybrid page/block mapping.
- Hot/cold separation.
- Multi-stream writes.
- NVMe streams.
- Zoned Namespaces, or ZNS.
- Flexible Data Placement, or FDP.
- Host hints.
- Compression.
- Deduplication.
- Delta encoding.
- In-place update buffering.
- pSLC write caches.
- Larger sequential write units.
- Avoidance of small random writes.
- Checkpoint and metadata-write reduction.
- Data-lifetime grouping.
- Placement by expected invalidation time.

Commercial SSD documentation commonly presents wear leveling, garbage
collection, over-provisioning, bad-block management, and host placement as
mutually supporting endurance mechanisms.

### 3.9 Cell-mode and capacity reconfiguration

A controller can trade capacity for wider threshold-voltage margins.

- QLC-to-TLC conversion.
- QLC-to-MLC conversion.
- QLC-to-pSLC conversion.
- TLC-to-MLC conversion.
- TLC-to-pSLC conversion.
- MLC-to-SLC conversion.
- Dynamic pSLC caching.
- Permanent retirement into a lower-density mode.
- Partial-state use, where some threshold states are no longer used.
- Reserved-state encoding.
- Reduced-capacity operation.
- Adaptive over-provisioning.
- Capacity throttling near end of life.
- Stronger ECC with reduced user capacity.
- Larger parity allocation.
- Selective lower-density operation for weak blocks.
- Metadata placement in SLC/pSLC regions.
- Cold-data placement in stronger modes.
- Critical-data replication in stronger modes.

These methods widen effective state separation or increase redundancy, but
sacrifice capacity and sometimes write performance.

### 3.10 Bad-block and fault-containment prevention

- Factory bad-block identification.
- Factory bad-block tables.
- Runtime bad-block detection.
- Program-failure detection.
- Erase-failure detection.
- Read-margin testing.
- Weak-block classification.
- Weak-page classification.
- Weak-wordline classification.
- Early retirement.
- Gradual retirement.
- Spare-block pools.
- Separate metadata spare pools.
- Plane-local replacement.
- Die-local replacement.
- Cross-die remapping.
- Partial-block salvage.
- Sub-block bad-block management.
- Fault-domain-aware allocation.
- RAID/RAIN reconstruction.
- Parity patrol and scrubbing.
- Chip sparing.
- Die sparing.
- End-to-end CRC.
- Metadata replication.
- Journaling and atomic mapping updates.
- Power-loss-protected metadata recovery.
- Latent-sector-error scanning.
- Predictive failure alerts.
- Media-error trend monitoring.

### 3.11 Predictive reliability and machine-learning algorithms

These do not directly correct a cell, but decide when and where recovery or
prevention is needed.

**Features commonly monitored**

- Corrected-bit count.
- Decoder syndrome weight.
- LDPC iteration count.
- Retry count.
- Soft-read count.
- RBER.
- Estimated UBER.
- P/E count.
- Read count.
- Retention age.
- Time since erase.
- Time since programming.
- Dwell time.
- Temperature history.
- Layer and wordline.
- Page type.
- Neighbor-state pattern.
- Program and erase latency.
- Program/erase fail-bit count.
- Prior refresh and reclaim history.

**Model families**

- Fixed thresholds.
- Linear and polynomial regression.
- Exponential retention models.
- Arrhenius temperature models.
- Maximum-likelihood estimation.
- Bayesian updating.
- Kalman filtering.
- Gaussian-mixture threshold-distribution models.
- Survival and hazard models.
- Decision trees and random forests.
- Support-vector machines.
- Neural networks.
- Recurrent or temporal models.
- Reinforcement learning for policy selection.
- Online learning.
- Per-device transfer learning.
- Meta-learning across NAND generations.
- Confidence-based fallback to conservative policies.

They can drive Vref prediction, refresh scheduling, weak-block classification,
ECC-strength selection, read-reclaim thresholds, wear leveling, and
retirement.

---

## 4. Compact index of principal named public schemes

| Scheme | Primary purpose |
|---|---|
| AERO | Adaptive erase duration using erase fail-bit information. |
| ALCod | Layer-error-aware adaptive LDPC coding. |
| AR² | ECC-margin-guided adaptive read retry. |
| BeLDPC | Bit-error-aware adaptive LDPC. |
| CellRejuvo | Experimental state reprogramming for retention-aged cells. |
| Cocktail | Data placement that reduces explicit read reclaim. |
| ColdCode | Low-RBER state-pattern encoding for cold data. |
| CooECC | Cooperative decoding across related NAND pages. |
| DEAR | Runtime error-aware selective refresh. |
| DeVTS | Dynamic erase-voltage and erase-time scaling. |
| DHD | Double-hard-decision LDPC recovery. |
| DPES | Dynamic program and erase scaling. |
| DVA | Dynamic threshold-voltage allocation over lifetime. |
| DyLDPC | LDPC adaptation using temporal and spatial RBER. |
| EBDN | Entropy-based double nonuniform soft sensing. |
| EMAL | Error-mode-aware LDPC. |
| FCR | Correct and refresh before errors exceed ECC. |
| FineRR-ZNS | Fine-grained read refresh for zoned SSDs. |
| GuardedErase | Reduced erase stress on weak wordlines. |
| HeatWatch | Temperature-, dwell-, age-, and wear-aware retention management. |
| LaVA | Layer-variation-aware bad-block management. |
| LaVAR | Layer-specific read-reference calibration. |
| LI-RAID | Layer-interleaved RAID/parity placement. |
| LLD | Reduced-latency hard-decision LDPC processing. |
| MGC | Runtime selection among multiple Gray mappings. |
| Minato | Read-disturb-aware dynamic buffering. |
| NAC | Neighbor-cell-assisted correction. |
| Near-Zero Read Retry | Tailored retry table, dynamic selection, and local search. |
| Novel Valley Search | Fast estimation of read-distribution valleys. |
| ORVD-WRRO/OER-ECC | ECC/error-observation-based optimal read-voltage selection. |
| PEAR-type schemes | Handle unequal reliability among interrelated NAND pages. |
| PR² | Pipelined read-retry execution. |
| RDR | Read-disturb-specific probabilistic error recovery. |
| REAL | Retention-error-aware LDPC. |
| ReMAR | Retention-model-aware reading. |
| ReNAC | Retention- and neighbor-interference-aware correction. |
| RFR | Retention failure recovery using leakage behavior. |
| ROR | Per-block retention-optimized reading. |
| SREA | Self-recovery-effect-aware wear leveling. |
| Shuffler | Superblock-oriented read-reclaim management. |
| SSALDPC | Syndrome-sum-adaptive LDPC. |
| STAR | State-aware randomization against vulnerable patterns. |
| STRAW | Wordline-level accumulated-disturb tracking and reclaim. |
| SWEEP | Co-location of read-hot and write-hot data. |
| VaLLR | Threshold-distribution-aware LLR calibration. |
| WARM | Separate management of write-hot and write-cold data. |
| Variable-dimensional LDPC | Reliability-dependent LDPC dimensions or granularity. |

---

## 5. Which techniques are commonly deployed versus research-oriented?

**Common or strongly established in commercial controllers**

- BCH and/or LDPC ECC.
- Read retry using vendor voltage tables.
- Hard-to-soft LDPC escalation.
- Per-page-type and often per-layer calibration.
- Bad-block management and spare-block remapping.
- Dynamic and static wear leveling.
- Garbage collection and over-provisioning.
- Read reclaim.
- Background data refresh or scrubbing.
- Read counters and disturb thresholds.
- Adaptive program/erase control within the NAND die.
- Data scrambling/randomization.
- pSLC caching.
- Thermal monitoring.
- RAID/RAIN or equivalent parity in many enterprise-class designs.
- Corrected-error and health-statistic monitoring.

**Published research ideas that may be partly deployed under proprietary names**

- ROR/ReMAR-like retention models.
- LaVAR-like per-layer calibration.
- HeatWatch-like temperature/dwell models.
- Dynamic Vpass tuning.
- Neighbor-assisted correction.
- RFR/RDR-like failure-specific candidate correction.
- Adaptive-rate and error-mode-aware LDPC.
- Error-aware refresh.
- Fine-grained wordline read reclaim.
- State-aware coding and data placement.
- Self-recovery-aware wear leveling.

**More experimental or architecture-dependent**

- CellRejuvo-style state reprogramming.
- Active or targeted heating.
- Complex neural recovery on the SSD data path.
- Per-cell persistent characterization.
- WOM or highly constrained codes for ordinary user data.
- Permanent dynamic conversion of arbitrary weak QLC blocks to lower-density
  modes.
- Fine-grained page or wordline remapping when the NAND interface does not
  expose the required operations.

---

## 6. Canonical research backbone

For a literature review, the most important foundational sequence is:

1. FCR for retention refresh.
2. ROR and RFR for retention-aware reading and post-ECC recovery.
3. Dynamic Vpass tuning and RDR for read disturb.
4. LaVAR, LI-RAID, ReMAR, and ReNAC for 3D-NAND variation, retention, and
   interference.
5. HeatWatch for temperature/dwell/age-aware retention.
6. WARM for retention-aware hot/cold placement.
7. PR², AR², valley search, and near-zero read retry for retry latency.
8. MMI/EBDN/VaLLR and adaptive LDPC for soft sensing and decoding.
9. DPES, DeVTS, GuardedErase, and AERO for program/erase endurance.
10. STRAW, DEAR, FineRR-ZNS, SWEEP, and Shuffler for modern fine-grained
    refresh and read reclaim.
11. MGC, STAR, and ColdCode for data-pattern and state-mapping prevention.
12. CellRejuvo and self-healing-aware schemes for physical or quasi-physical
    recovery.

The critical design trade-off across nearly all these algorithms is the same:
lower raw error rate and lower UBER versus additional reads, writes, latency,
metadata, controller computation, and write amplification. Refresh and read
reclaim may prevent data loss but consume endurance; additional soft reads
improve LDPC success but increase latency and potentially read-disturb
exposure; lower program/erase stress improves endurance but may reduce speed
or retention margin.
