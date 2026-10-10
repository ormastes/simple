# Bootstrap independent object diagnostics

Status: draft, not bootstrap/release qualified.

The selected requirement is to collect independent Phase 3 and Phase 4 source
failures through MIR/object emission, while stopping on invalid authority or
schema and retaining an unsuccessful phase result if any required unit fails.

The provisional scheduler previously attempted fallback objects only in Phase 3.
The managed scheduler produced index-independent SMF evidence but did not try
native objects after an index or group failure. Both now schedule independent
object tasks in both phases through the explicit `native-build --target` route.
Each object gets a private manager job/cache, exact entry source, durable outcome,
and target/container validation. Failed groups remain failed/blocked; emitted
objects cannot create a completion receipt or repair a failed executable build.
Failure summaries are written beside the complete outcome journal. Admission
failures stop new work; already running provisional peer work is drained.

The managed worker now recognizes exact anchored `SCV-E-ADMISSION:` diagnostics
in its bounded, persisted compiler output. The public compiler exit code remains
unchanged; the manager promotes this authority refusal to an owner abort. This
change requires rebuilding the manager image. The new unit spec and executable
classifier fixture have not run with a qualified full CLI/test runner.

## Evidence

- Producer: `/home/yoon/dev/simple-bootstrap-mir-object-20261011/build/native_probe/combined-fixes/simple`
- SHA-256: `67b29c2e79ef945dcea3b07ea1cedfad99892a1e4448108382571b25f1533f4f`
- Real fixture: `scripts/bootstrap/tests/collect-all-native-object-test.shs`
- Retained evidence: `/home/yoon/dev/simple-bootstrap-collect-all-20261011/build/native_probe/collect-all-native.DIoymv/`
- Phase 3: first source produced an explicit parse error; the later independent
  source produced an ELF64 relocatable x86-64 object (1,104 bytes).
- Phase 4: first source failed; the later independent source produced an ELF64
  relocatable AArch64 object. Both phases retained `managed_failed=1`.
- The object validator rejected the AArch64 object when asked for x86-64 and
  rejected an invalid target before compilation.
- Scheduling controls passed: `phase3-go-end-test.shs`,
  `managed-task-schedule-test.shs`, `collect-all-admission-stop-test.shs`.
- Shell syntax, Perl syntax, direct-env runtime working guard passed.
- `doc/06_spec` contained zero executable `_spec.spl` files.

A first real fixture under `build/` was correctly refused by SCV's source-family
admission. Moving it under `test/` exposed an unprimed checkout journal, and a
full checkout cold prime exceeded the 45-second per-unit diagnostic budget.
The final fixture uses a tiny isolated Git checkout, preserving real SCV admission
without repeatedly hashing the full repository. Earlier evidence and caches were
retained; no full bootstrap was claimed.

Pending gates: rebuild/admit the manager classifier; run its unit spec; run the
full Phase 3/4 inventories and required compiler/core/MCP checks with qualified
native tools. The source-root list includes composition, compiler, app, lib, OS,
plugins, and package ownership. Integrate CUDA policy commit `11fdfa806e7` in the
next combined candidate. Do not merge, deploy, or publish based on these fixtures.
