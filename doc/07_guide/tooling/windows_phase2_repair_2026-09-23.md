# Windows Phase2 repair checkpoint — 2026-09-23

## Admission boundary

The successful Stage2 producer remains frozen in `D:/b-sync`, at source commit
`947324516d08a4e669eb65082b1d0fbf355aa484`. Its admitted executable SHA-256 is
`db170300ac0694d453fecf523f5d688ff7a2ec2187b92d8e8df236c06de40caa`; admission
receipt SHA-256 is `a54e518467b666b16fa0782eb4217bf978badcc530b9da893a877cc98404b627`.
Neither artifact was modified by this repair work.

The original Phase2 full CLI and test runner failed with 29 and 6 source
errors, respectively. There were no real test Results/counts and no Stage3
admission. Preserved evidence is under
`build/mini_builds/phase2-real-db170300ac0694d453fecf523f5d688ff7a2ec2187b92d8e8df236c06de40caa/FAILURE-HANDOFF.md`.

Repairs are in the separate `D:/b-phase2` checkout, based on
`18fedb1ae1aa8612d63afcd7dc149bd195475c61`. Changed canonical source and snapshot
coverage require a **fresh matching Stage2 admission** before another Phase2
verification. The old admission must not be relabeled for this source.

## Source/provenance and link repairs

| Repair | Evidence and current limit |
|---|---|
| Require `src/plugins` in canonical source snapshots | Focused real snapshot test passed file inclusion, modification, addition, deletion, and missing-root refusal. The runtime capsule fixture now creates the required root. Previously accepted resolve-contract tests were not repeated. |
| Restore missing `compiler.backend.common.c_abi_type_mapping` | Thin delegation to the existing canonical C mapper preserves its representation, named-type map, and unsupported-type refusals. Added unit spec; runtime acceptance remains pending a rebuilt debug producer. |
| Correct Wasm adapter import | Full static backend registry now names the existing compiler-owned adapter, without removing a backend. Source compilation acceptance remains pending. |
| Keep global `CL=/TC` out of MSVC archive linking | Child-local sanitizer removes only the standalone force-C token; preserves all other option bytes, quoted values, and the compile environment. Two production-helper tests and an actual clang-cl/archive/executable probe passed. |

The C ABI native probe used the original admitted executable only as a debug
producer, with `SIMPLE_NO_STUB_FALLBACK=1`, two threads, 120-second per-file
limits, and a 600-second outer bound. It failed at linking after 23 seconds:
clang-cl interpreted the hosted `.rlib` archive as C source because of inherited
`CL=/TC`. This is a later shared native-build boundary, not the cause of the
original 29/6 source errors. No C ABI runtime PASS is claimed.

The link fix lives in
`src/compiler_rust/compiler/src/pipeline/native_project/linker_env.rs` and is
called only for the final MSVC link command. It does not mutate the ambient
environment. A production-helper rebuild is needed before the frozen producer
can exercise that integration; no launch-only environment bypass was used.

Independent review accepted the link and snapshot changes. Optional extra
end-to-end capsule cases were not used to rerun already-green acceptance work.

## Retained focused evidence

Under `build/mini_builds/phase2-repair-20260923/`:

- `plugin-snapshot-cycle2.log`: snapshot regression PASS.
- `run-c-abi-probe.sh`, `c_abi_probe.spl`, `c-abi-native-cycle1.log`: exact failed
  debug command, original producer hash, link failure, and terminal exit 1.
- `linker_env_tests.rs`, `linker-env-cycle2.log`: two production-module tests PASS.
  Initial standalone compilation exposed only a test-harness `pub(super)` scope
  error; including the production module corrected the harness.
- `run-link-env-native.sh`, `link_env_native.rs`, `link-env-native-cycle1.log`:
  real source compilation preserving `/TC /DKEEP=1`, `.rlib` archive creation,
  sanitized linking, and resulting executable exit 0.

The original Phase2 caches, runtime capsule, receipts, and failed outputs remain
retained. The C ABI probe used an isolated cache; no shared producer cache was
cleared or substituted.

## Other repair lanes and terminal boundaries

LLVM method lowering has six passing focused tests, including runtime signature
checks and JIT `round` results at positive/negative half ties. Ties-away matches
the interpreter; the existing Cranelift ties-even discrepancy is separate.

The typed-provider analogue initially compiled but exited 1 without output when
the class had no explicit trait implementation. Adding an explicit implementation
produced `direct=7` and `optional=7` with exit 0. This does not establish a general
optional-trait compiler fix. The actual PDB/DWARF sources now explicitly implement
`DebugInfoProvider`; the actual-source probe cleared the previous method errors
but stopped at five unresolved link symbols:

- `char_from_code` (lowering corrected to existing `rt_char_from_code`; the
  final exact-filter regression executed one test and passed);
- `HirLowering.error_fatal`;
- `bytes_to_u16_le` and `bytes_to_u32_le`;
- `rt_process_spawn_inherit`.

That probe used the limited `core-c-bootstrap` runtime lane, so missing runtime
symbols must be distinguished from genuine lowering/import errors. Its log is
`build/mini_builds/phase2-method-debug-source/build-cycle2.log`; it is not a PASS.
GPU nullable budget parsing now follows `try_parse_int(...) ?? 0` and preserves
the positive-budget/default policy; its direct source behavioral check remains
unrun. The zero-test exact-filter attempt is not counted as validation.

Trace32/CMM implementation ownership is restored under `src/app` without copied
duplicate implementation trees. Example CLI/MCP mains and cold/light frontend
entrypoints remain at their original paths. The final permitted focused SMF
cycle completed HIR for 90/90 modules with no unresolved names, then the old
producer crashed with `0xC0000005` before producing an artifact. No fourth retry
was run. See `build/mini_builds/trace32-rehome-check/HANDOFF.md` for the three
cycles and exact command. Source review accepted the relocation; executable
acceptance remains blocked. The official staged environment/process guard
passed; the working-tree guard was inconclusive because Git LFS was unavailable
when it inspected unrelated materialized aliases.
The complete Trace32/CMM source lane was checkpointed locally as
`43a29e35b8bd5dfc300f0c29b88014248e6d64f5`; this is not an admitted source revision.

## Remaining work and scheduling

No new admission is scheduled. Remaining field-type, optional narrowing, global
symbol, enum/API, and per-file timeout failures must not be hidden by narrowing
the full CLI/test-runner entries or disabling backends.

Next: finish bounded source/LLVM repair validation, rebuild a debug producer
including the link fix, rerun only failed focused probes, then obtain fresh
Stage2 admission for the repaired source before full Phase2. Main-agent
scheduling remains authoritative. No push, full bootstrap retry, Phase2 PASS,
or Stage3 advance is authorized by this checkpoint alone.
