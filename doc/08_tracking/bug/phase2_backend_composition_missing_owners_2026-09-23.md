# Phase2 full CLI imports nonexistent BYL and IrTc plugin owners

## Scope and cause

The admitted Stage2 compiler at source `e6ffda6849e6aa7fe01a7d23ddc71e9773286532`
failed the canonical Phase2 full CLI build with E1034 for
`plugins.backend_byl.byl_backend` in `full_static_backend_ports.spl`.
The same composition also named the nonexistent
`plugins.backend_irtc.irtc_codegen_adapter` owner.

Neither plugin directory exists. The implementations are still owned by
`src/compiler/70.backend/backend/byl_backend.spl` and
`src/compiler/70.backend/backend/irtc_codegen_adapter.spl`. Neither is included
in `scripts/check/kernel-phase5-backend-relocations.tsv`.
The registry already uses the equivalent compiler-owned WASM adapter pattern.

Correct the two imports to `compiler.backend.byl_backend` and
`compiler.backend.irtc_codegen_adapter`. This repairs the authored composition;
it does not move backend implementations or claim dynamic-plugin qualification.
The source resolver already probes `src/` and numbered compiler roots.
Adding `--source src/plugins` cannot supply nonexistent files and is unnecessary.
Build arguments, phase/producer/runtime cache identities, and closure discovery
are unchanged. No new scan, allocation, or request-path operation is introduced.

## Focused acceptance and evidence

Native reproduction directory:
`build/evidence/phase2-plugin-owners` in
`/Users/ormastes/simple-tmp/phase2-plugin-closure-20260923`.

Producer (Stage2, admitted, supported command `native-build`):
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-admitted/simple`.
SHA256 `0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`.
Admission status and exact binary hash checked before build, hash checked after.
The matching frozen runtime capsule verified successfully, identity
`99157e8902d570262f1fc59691862b9c3b9d3cbd45373b3127c30df75eb20a6f`.
Copied producer/capsule receipts and exact launch script are retained there.

The dedicated no-import fixture
`test/fixtures/native/full_static_backend_owner_paths.spl` was compiled once
with strict no-stub fallback, jobs1, private Stage2/producer/fixture cache, and
the existing sampled RSS guard. It reads the authored registry and checks both
owner imports and implementation paths. This is structural source-owner
evidence, not a substitute for compiling the full backend composition.

- Build: PASS, 1 compiled / 0 cached / 0 failed; 2.40s wall time.
- Build peak process-tree RSS: 192192 KiB; cap5859375 KiB, quiescent1,
  observer_errors0. The guard is sampled, not a kernel hard limit.
- Same native artifact before import correction: exit11, BYL owner assertion;
  0.35s wall / 8699904 bytes maxRSS.
- Same artifact after both import corrections: exit0,
  `full-static-backend-owner-paths-pass`; <0.01s wall / 8765440 bytes maxRSS.
- Artifact SHA256:
  `018edfa1a125f1b8881612ce5a648a18a489323001c6786e33a704639667853b`.

These single executions establish the regression, not a performance comparison.
The two import substitutions introduce no runtime data structure or algorithm.

Exit-code provenance is retained in `retained-tool-status.txt`: the original
execution tool results `f2e014` (red) and `a4f760` (green), their exact command
segments, and their separately printed fixture statuses. This file is explicitly
a later transcription of existing tool output, not a generated execution receipt;
neither green nor red was rerun to create it. SHA256:
`148f28bc6ad2db9b4adf90b25e853f2761fe059e1216ae7a40cd49add2916020`.
Retained log SHA256 values:

- `red.log`: `9b7b359fe276c56214c2b58586f39309781230d6ee42f5e1e520847c5641e131`
- `green.log`: `a18362de629a99dc04c01e464014c05fcdfa4db6a17f2ac80b304f1fb1309cc8`
- `build-native.sh`: `13d907b87bce3c3065758aac76473816bd45e3e344f830d84c092c242e42bbe2`

`test/01_unit/compiler/driver/driver_source_loading_spec.spl` now extracts the
actual registry imports and calls the real source resolver for each, requiring
a nonempty result. Exact BYL and IrTc owner paths are asserted separately.
That SSpec is **not executed** here: the general dedicated test runner is still
blocked in Phase2. The native fixture is not reported as an SSpec pass.

Working direct-env guard and diff whitespace checks pass. Full CLI/compiler
tests, MCP checks and Stage3 are intentionally left to the canonical Phase2
owner. No full bootstrap or full CLI retry was run in this lane.
