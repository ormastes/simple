# Item 5 size and startup measurement acceptance criteria

Status: NOT_IMPLEMENTED. These are acceptance criteria for intentional failing SSpec scaffolds, not implementation or execution evidence.

Canonical requirements: [selected requirements](../../../02_requirements/feature/runtime_optional_provider_binary_size_optimization.md).

Each criterion must eventually use real build, loader or measurement observations. Missing runners, fixtures, admitted baselines or evidence remain incomplete. No test has been run for this scaffold.

## I5-P06-AC01: keep unstripped NoGC hello strictly below two MiB

- Requirements: NFR-001.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare the same allocation-free NoGC hello for every supported native target using a same-host admitted toolchain and preserve the unstripped artifact.
- Action: Measure its exact on-disk byte size and bind the measurement to target, source and binary identities.
- Observable acceptance: Each unstripped executable is strictly below 2 MiB (2,097,152 bytes); a result equal to the threshold fails and no supported target is silently excluded.

## I5-P06-AC02: meet the Linux ELF absolute release-small size limit

- Requirements: NFR-002.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a Linux ELF release-small NoGC hello that prints the required bytes through the Simple print path, using the admitted strip policy.
- Action: Build and measure the stripped artifact with its map, section and identity evidence retained.
- Observable acceptance: The executable is at most 15 KiB (15,360 bytes); the absolute limit is enforced independently of the matched-C ratio.

## I5-P06-AC03: meet the matched C size ratio with identical runtime conditions

- Requirements: NFR-002.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare Simple and C hello on the same host and toolchain, sharing startup wrapper, required core runtime archive, linker options, section GC and strip policy; C uses puts and emits the same bytes.
- Action: Build both artifacts, compare output checksums and measure their byte sizes.
- Observable acceptance: Simple is no larger than 1.05 times matched C, with no rounding that admits an over-limit result; mismatched inputs invalidate comparison, and bare C main is advisory only.

## I5-P06-AC04: bound non-ELF size using an admitted format allowance

- Requirements: NFR-003.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare matched same-host C and Simple release-small NoGC hello for each supported non-ELF target and obtain its admitted fixed format allowance in bytes.
- Action: Measure both artifacts and attribute every byte of the fixed allowance to format overhead.
- Observable acceptance: Simple size is no greater than C size plus that target's admitted allowance; missing or unadmitted allowances reject the gate, and runtime features cannot be hidden inside the allowance.

## I5-P06-AC05: bound warm interpreter startup against same-host Python

- Requirements: NFR-004 NFR-007.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare minimal interpreter hello and an admitted same-host Python hello with equivalent output, declared warm-cache conditions and a fixed measurement protocol.
- Action: Collect the required cohort of warm startup samples and compute p50 and p95 under the admitted comparison statistic.
- Observable acceptance: The protocol's startup statistic is at most 1.10 times its matched Python baseline, with parity or better as the target; p50 and p95 and output checksums are reported, and the statistic is not chosen after observing results.

## I5-P06-AC06: bound interpreter maximum RSS against same-host Python

- Requirements: NFR-004 NFR-007.
- Status: NOT_IMPLEMENTED.
- Setup: Use the same hello fixtures, admitted Python baseline, host and declared process-tree RSS accounting used by the warm-startup cohort.
- Action: Measure maximum RSS for each run and apply the declared baseline comparison while retaining the individual samples.
- Observable acceptance: Maximum RSS under the admitted comparison protocol is at most 1.10 times matched Python; aggregation, units and child-process scope match, with p50 and p95 reported and no omitted high-memory samples.

## I5-P06-AC07: require at least thirty development samples

- Requirements: NFR-007.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a development measurement cohort with fixed host, toolchain, source, binary hashes, output checksums and sampling protocol.
- Action: Collect size/startup/RSS evidence for at least 30 valid runs and submit the cohort to the gate.
- Observable acceptance: Fewer than 30 samples cannot qualify; the gate retains all sample identities and reports p50, p95 and RSS alongside hashes, toolchain identities and checksums.

## I5-P06-AC08: require at least one hundred release samples

- Requirements: NFR-007.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a release measurement cohort for the exact immutable candidate and matched baseline with the declared same-host protocol.
- Action: Collect at least 100 valid samples and submit the release evidence.
- Observable acceptance: Fewer than 100 samples cannot qualify for release; development evidence is not relabeled, and p50, p95, RSS, binary hashes, toolchain identities and checksums remain traceable to the release candidate.

## I5-P06-AC09: retain complete linker and measurement artifacts

- Requirements: REQ-014 NFR-007.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare one native build with a unique candidate identity and an evidence directory intended to survive stripping and packaging.
- Action: Link, strip and collect the candidate's map, removed-section log, section sizes, symbol-size ranking, dynamic dependency list and both binary hashes.
- Observable acceptance: All six required evidence categories are retained, refer to the exact unstripped/stripped pair, and remain connected to the measurement cohort; missing or inconsistent evidence rejects qualification.

## I5-P06-AC10: reject incomparable or altered measurement cohorts

- Requirements: NFR-001 NFR-002 NFR-003 NFR-004 NFR-007.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare otherwise complete size/startup cohorts and separately vary host, toolchain, candidate hash, output checksum, baseline admission or declared strip/runtime conditions.
- Action: Submit each altered cohort through the same measurement gate used for valid evidence.
- Observable acceptance: Each identity or comparability violation is rejected with the offending field; no favorable size, startup or RSS number can override the invalid cohort, and original samples remain available for audit.
