# System Test Plan: Simple Platform Unification

## Traceability basis

Existing requirements retain their source document and namespaced identity:
`PF/REQ-*`, `EODL/REQ-*`, and `SMPB/REQ-SMPB-*`. Additional user-selected
integration decisions use stable `UP-AC-*` acceptance IDs. Planned coverage is
not executed evidence.

| Acceptance | Origin | Production owner | Planned evidence | Status |
|---|---|---|---|---|
| UP-AC-001 | PF/REQ-001..008, PF/NFR-001..007 | parser framework + frontend adapter | exact output, lexical boundary, incremental/full, allocation, dispatch | planned; existing coverage delegated by reference |
| UP-AC-002 | EODL/REQ-001..014, EODL/NFR-001..010 | environment/catalog/binding/loader | admission-before-map, policy, binding, retirement, startup isolation | planned; existing coverage delegated by reference |
| UP-AC-003 | EODL/REQ-015..016, EODL/NFR-011..012 | target registry + process inspector | registry invalidation, atomic completion, cancellation/reap | planned; existing coverage delegated by reference |
| UP-AC-004 | SMPB/REQ-SMPB-001..013 | SimpleOS platform-build catalog | aliases, RV32 ABI, runtime symbols, native backend, shared UART | planned; existing coverage delegated by reference |
| UP-AC-005 | user decision §§35..38, 44, 54..56 | image + machine planners | machine plan happy/boundary/error and digest substitution | source contracts/specs landed; qualified execution and machine-plan owner pending |
| UP-AC-006 | user decision §§49, 60 | bootstrap + release verifier | canonical live guest compiler and persistence | not implemented |

The production system path is
`test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`, mirrored
under `doc/06_spec/03_system/os/`. Supporting tests cannot substitute for its
production-owner receipt.

## Planned executable scenarios

1. Manifest determinism and target/host separation (`UP-AC-005`).
2. Machine-spec validation and KVM/HVF/WHPX/TCG selection receipts.
3. Baseline boot with every optional optimized provider absent or quarantined.
4. `prefer`, `max`, and failing `require` provider policy.
5. Forced legacy/scalar/SIMD exact outputs, lexical boundaries,
   incremental/full equivalence, allocation counts, and semantic hashes; GPU
   remains fail-fast until implementation and device evidence exist.
6. Fresh x86_64 image cold boot, NVFS mount, SOSIX filesystem operations,
   guest compiler version/run/build/execute, persistence write, reboot/read.
7. Reused development VM cannot satisfy the cold-boot release receipt.
8. Tampered image, provider, firmware, or evidence digest fails promotion.
9. `--show-plan` is complete and `--print-command` derives from the same plan.
10. Stale generations, dependency quarantine, bounds exhaustion, malicious
    path/argv/environment, timeout/cancellation/reap, device loss/unfinished GPU
    fences, TOCTOU substitution, and replayed guest evidence fail closed.

Executable SPipe is added with the first implementation slice after helper names
are frozen. Every unimplemented scenario fails fast; placeholder passes are
forbidden. Generated manuals mirror test paths under `doc/06_spec` and expose
operator flow and evidence artifacts.

## Evidence and performance gates

SimpleOS scenarios declare `source-contract`, `host-fixture`, `image-admission`,
or `live-guest`. Missing admitted runner/image/compiler output/transcript is
`MissingEvidence`, never PASS. Native execution is required; interpreter loading
alone is insufficient. Receipts join candidate, boot session, image, firmware,
compiler, source input, and produced artifact identities.

Retain exact selected thresholds: PF scalar time <=110% of its oracle, parser RSS
<=50% of retained baseline, optimized `auto` >=1.5x end-to-end speedup, and small
edit latency <=25% of full reparse. EODL additionally requires warm/cold
selection p95 <=1/25 ms, dispatch overhead <=2%, optimized RSS increase <=5%,
and unselected catalog RSS <=2 MiB. EODL's 1.15x pilot does not replace the PF
1.5x auto-promotion gate. Plans name fixtures, reference machines, repetitions,
warmup, quantiles, and retained raw samples. Boot and guest-roundtrip numeric
budgets remain pending user selection.

## Retained checkpoint evidence

- `test/01_unit/os/simpleos_machine_catalog_projection_spec.spl` covers six
  architectures, aliases, four profiles, lane fallback, and QEMU argv. It has
  source review but no admitted-runtime verdict.
- `test/01_unit/lib/common/contracts/execution/simpleos_image_manifest_v1_spec.spl`
  covers bounded validation, baseline safety, separated carrier/root/volume/
  snapshot/overlay identity, digest/path failures, and near-`u64` rejection. It
  has diagnostic seed execution only.
- Before V1 encoding freezes, add independently pinned canonical bytes and
  SHA-256 plus exact-fit and overflowing maximum-capacity cases. These source
  cases are now present: 2,037 bytes, SHA-256
  `87fbdf46453452b6f9f6f46c028489b4b59914754049dfb3ceee6a1590c5e9bb`, exact
  `u64::MAX` fit, and mathematical `u64::MAX+1` rejection. Missing qualified
  execution or generated manuals remains `MissingEvidence`.
- `test/01_unit/os/installer/image_builder_manifest_adapter_v1_spec.spl`
  covers all adapter rejection/mismatch branches. It proves fail-closed
  projection policy, not that the current builder materializes an NVFS root.

## Corrected executable ordering

1. Prove native retained-root image I/O with symlink, replacement, oversize,
   collision, durability, and exact-reread negatives.
2. Reject filesystem artifacts with generated weak serial/NVMe/FAT32/runtime
   implementations before QEMU.
3. Use `x64-nvme-fat32` only as filesystem evidence.
4. Use a distinct cold-boot compiler scenario for guest version/build/execute,
   persistence write, reboot, and persistence verification.

The three prior boot cycles are closed diagnostics. The Multiboot artifact
reached `_start`, but weak providers invalidate qualification.
