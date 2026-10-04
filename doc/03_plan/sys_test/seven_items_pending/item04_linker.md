# Seven-item 04 pending umbrella acceptance

Status: NOT_IMPLEMENTED applies to these new scenario bodies only. Existing implementation and coverage remain intact. No runtime execution or completion is claimed.

Sources: `doc/03_plan/seven_plans_host_completion_2026-09-29.md` section 4; `doc/01_research/compiler/linker/mold_mdsocpp_linker_2026-09-15.md` sections 6/9/11; existing `doc/03_plan/sys_test/item4_linker_acceptance_2026-10-03.md` ITEM4-REQ-001..010 (read from origin/main because DEV sparse baseline lacks it). Existing item4_linker_* system specifications retain their authored/source-reviewed statuses. The new rows below target missing complete-product, native-matrix and fault/performance proofs; they do not replace existing portable behavioral specs or claim the linker product unimplemented.

## S7-I04-AC01 — Map retained linker ownership through a complete product link

- Requirement source: ITEM4-REQ-001 ITEM4-REQ-002.
- Status: NOT_IMPLEMENTED.
- Setup: Pin the compiler, runtime, provider manifests and retained MDSOC++ layer map.
- Action: Link the complete compiler through the production facade with ownership and engine receipts.
- Observable: Every retained layer resolves to its actual owner; no sibling-private dependency appears; actual engine receipt names the successful route.

## S7-I04-AC02 — Preserve archive fixpoint and root semantics in a runnable application

- Requirement source: ITEM4-REQ-003.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a real multi-archive application with second-pass dependencies, entry, exports, initialization, TLS and KEEP roots plus unrelated members.
- Action: Link with ordered archive groups and dead stripping, then execute the application.
- Observable: Required roots and dependent members survive, unrelated members are absent, startup/output match baseline and archive extraction order remains deterministic.

## S7-I04-AC03 — Reject relocation and malformed input without publishing a new artifact

- Requirement source: ITEM4-REQ-004 ITEM4-REQ-007.
- Status: NOT_IMPLEMENTED.
- Setup: Retain a prior complete executable and actual machine-specific objects with independently specified relocation values and overflow/boundary controls.
- Action: Link valid and malformed requests through the transactional production output route.
- Observable: Valid relocation bytes match independent values; failures identify object/symbol/type, retain the prior artifact and publish no partial replacement.

## S7-I04-AC04 — Execute dynamic TLS unwind and stripped application behavior

- Requirement source: ITEM4-REQ-005.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare the real ELF dynamic corpus with SONAME/versioned imports, TLS, unwind and required security metadata; other formats retain their separate AC05 gate.
- Action: Link and execute unstripped and stripped variants on each admitted host.
- Observable: DT_NEEDED/SONAME/version visibility match manifests; TLS and unwind effects and command outputs remain equal after stripping.

## S7-I04-AC05 — Qualify each host and object format independently

- Requirement source: ITEM4-REQ-006.
- Status: NOT_IMPLEMENTED.
- Setup: Provide separate ELF x64/ARM64, PE AMD64/ARM64, Mach-O, FreeBSD and retained SimpleOS firmware/board fixtures with available or explicitly missing runners.
- Action: Request linking and native/guest startup for every claimed matrix row.
- Observable: Each claimed row has its own byte and execution evidence; unsupported capabilities produce deterministic diagnostics and missing runners remain pending rather than being inferred from ELF.

## S7-I04-AC06 — Build and execute the complete compiler and application corpus

- Requirement source: ITEM4-REQ-008.
- Status: NOT_IMPLEMENTED.
- Setup: Pin the full self-hosted compiler release sources and representative CLI, provider and full-debug application inputs.
- Action: Link and run each complete artifact through its selected production route.
- Observable: Actual bootstrap/compiler commands and representative application outputs/status match baselines with complete artifact/input identities; tiny fixture success is insufficient.

## S7-I04-AC07 — Qualify full-product fast and bounded performance

- Requirement source: ITEM4-REQ-009.
- Status: NOT_IMPLEMENTED.
- Setup: Pin mold/lld baselines and full compiler, provider, debug, ThinLTO and giant-object corpora with whole-job memory accounting.
- Action: Measure separate cold/warm fast and bounded links under QualifiedJobScope.
- Observable: Behavior is equivalent across tools and modes; record each output digest and size; repeated identical tool/config/input cohorts are byte-deterministic; bounded peak stays below 6000000000 bytes including helpers; every 2 percent regression is investigated.

## S7-I04-AC08 — Recover a replaced linker aspect without losing live generations

- Requirement source: ITEM4-REQ-010.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a working generation with live sessions and an admitted replacement plus a failed dynamic provider and static recovery path.
- Action: Replace the aspect while old sessions remain pinned, then invoke recovery.
- Observable: Old sessions retain their exact generation, new sessions select the replacement and static recovery completes without depending on the failed provider.

## S7-I04-AC09 — Preserve complete output publication under storage and cancellation faults

- Requirement source: ITEM4-REQ-007 ITEM4-REQ-009.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare real spill/output transactions and required PDB/dSYM/manifest outputs with prior complete artifacts.
- Action: Inject disk-full, spill corruption and cancellation before and during publication.
- Observable: Original errors remain actionable; no mixed output becomes readable, required sidecars are never silently omitted and retained complete artifacts remain usable.
