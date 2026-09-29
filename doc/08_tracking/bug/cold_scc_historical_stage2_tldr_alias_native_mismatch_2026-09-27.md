# Historical Stage2 native TLDR header mismatch in cold SCC probe

Status: OPEN (2026-09-27). Scope: diagnostic historical pure-Simple Stage2,
not an admitted current-source compiler failure.

`test/fixtures/compiler/cold_package_scc_native_probe.spl` constructs a
32-package chain with reciprocal module import/reverse-dependent fields. Its
`old` mode calls `package_scc_schedule_v1`; `new` mode calls
`cold_package_scc_v1` on the same package edges. The interpreter's `old`
mode prints `CHECKSUM 256`, but the strict Cranelift native binary built by
the historical Stage2 producer prints
`FAIL old:reverse-edge-invalid:module_0:module_1`. The same native binary's
`new` mode prints `CHECKSUM 256` and exits 0.

The interpreter reports a JIT fallback while loading this fixture:
`Cannot infer field type: struct 'PackageModuleIndexEntryV1' field
'schema_version'`. The fixture constructs the distinct
`package_tldr_metadata.PackageTldrHeaderV1`, which has that field; the
index module also exports a `PackageTldrHeaderV1` alias for
`PackageModuleIndexEntryV1`, which does not. A type-name collision in the
historical producer is a plausible cause; the exact native miscompile owner
is not yet proven. The old scheduler's native failure makes its timing and
RSS unusable as a paired baseline, so no normalized performance ratio is
claimed from this probe.

Reproduction artifacts:

- Current fixture SHA-256: `9dfa2833e4d95179386955e95b119eda61c429544a51eb9a6a91f4063c2c2dee`.
- Stage2 producer SHA-256: `319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`.
- Native probe SHA-256: `e7c47c0846aeb86e12676df92fd3f51c8e49a12b54587610d74dfba47b116d25`.
- Build and interpreter logs: `build/mini_builds/target6_cold_package_scc_native_20260927/`.

The current-source pure-Simple compiler must compile and run both modes
correctly before a native p95/RSS comparison can qualify this replacement.
Aliasing the fixture's canonical TLDR import left the native output hash and
failure unchanged. Three bounded build/fix cycles were used for this probe;
no further retries are planned in this session.

An independent lightweight probe imports only the cold SCC projection and
SHA-256. After moving the identity hash into that module, strict native
compilation with the same historical Stage2 producer succeeded, and the
128-package chain printed `PASS cold-package-scc-light` (binary SHA-256
`05c758f35b9f785feb683dbd6b7e7692a0dfa637b1ceafa98e7f51be4db697e1`).
This confirms native execution of the isolated new graph projection. It does
not resolve the mixed old-scheduler TLDR mismatch or qualify the product
performance gate.
