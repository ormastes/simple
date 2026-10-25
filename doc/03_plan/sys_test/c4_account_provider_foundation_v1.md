# C4 account/provider foundation test plan

Status: TEST_BLOCKED / all executable scenarios UNRUN. This plan consumes the
selected authority and current dependency inventory in
[the integration design](../../05_design/compiler/c4_account_provider_foundation_v1.md).
The scope is a reusable logical-accounting foundation for
FORMAL-PHYSICAL-ACCOUNTING and C4-HIR-CFG; no requirement receives a done mark.

| Production API scope | Executable under `test/01_unit/compiler/mir/` | Authored mirror under `doc/06_spec/01_unit/compiler/mir/` | Cases |
|---|---|---|---|
| Atomic shared account, exact caps, overflow refusal, alias close, independent snapshots | `loop_resource_account_v1_spec.spl` | `loop_resource_account_v1_spec.md` | 7 |
| Construction, checked revisions, sticky failure, phase invalidation, structural/remap cycles, scalar/span payload | `loop_module_shape_owner_v1_spec.spl` | `loop_module_shape_owner_v1_spec.md` | 21 |
| Reserved actual type/operand/instruction/text/declaration projections, ordered payload and spans, one-use permits, exact bounds | `loop_module_shape_projection_v1_spec.spl` | `loop_module_shape_projection_v1_spec.md` | 9 |

First obtain the canonical compiled SSpec producer with a valid general testing
admission receipt. Record its path, hash, stage, source, backend, runtime/provider,
commands, isolated output/cache and actual executed inventory. Reject loading-only
interpreter results, zero registered scenarios, skips, fallback or Stage 2-only
diagnostic evidence as behavioral acceptance. Use the existing canonical runner;
no separate evaluator or new runner is permitted.

Run account, owner, then projection cases once each; keep exact executed counts
and failures. The added current-layout projection oracle independently requires
510 permit slots, 516 through text export, and refusal with 509 retaining 220
already charged slots. Do not derive expected values using the production sizing
helper. Execute the real production constructors/materializers.

Then run canonical docgen and SSpec maintenance for each changed pair, review the
manuals and require zero stubs. Preserve authored/UNRUN labels until execution
and generation actually occur. Run required compiler/library/MCP/LSP and core/MCP
smokes with their admitted runtime. Native physical capacity, class privacy/ABI,
RSS and complete SOURCE→PLAN→EMIT are separate required acceptance lanes.

No UI exists; captures are N/A. Runtime evidence should retain the actual SSpec
inventory/results and producer receipt. Source checks or manually rendered
mirrors never replace those artifacts. Repeat a check only after a relevant fix
or new attributable evidence; stop after convergence or the repo iteration cap.
