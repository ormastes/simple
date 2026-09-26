# Retired bootstrap specs: Stage 4 / bootstrap tooling contracts

- **Filed:** 2026-09-26
- **Status:** open — re-land the feature, then restore the spec from its origin commit
- **Component:** `scripts/bootstrap/`, `src/app/io/cli_ops.spl`, `src/compiler/90.tools/fix/`, `.github/workflows/rust-bootstrap-multiplatform.yml`

## Why these were retired

The share-history squash `e274cd33719` (2026-08-27, single parent) brought these
specs into `test/01_unit/compiler/bootstrap/`, but the source they pin never
landed on the main lineage (`fcbec1c3b62` / `e9da588ee61` restored `src/` to
origin). On Windows bootstrap46 they failed under the delegated seed. The owner
decided (2026-09-26): retarget where main has the feature, retire and track where
it does not. Restore each spec from its origin commit once the feature is back.

## Missing features

| Spec (test/01_unit/compiler/bootstrap/) | Retired | Missing on main | Origin commit |
|---|---|---|---|
| `stage4_cli_ops_stderr_facade_spec.spl` | whole file | `src/app/io/cli_ops.spl` still prints CLI diagnostics through `_cli_eprint -> eprint(msg)`; it never routes through `std.nogc_sync_mut.io.stderr_ops.stderr_write` | `85e9d8c8c09` (2026-08-04, fix(bootstrap): harden Phase 4 LLVM 23.1 migration) |
| `stage2_capability_stage4_guard_spec.spl` | whole file | `bootstrap-from-scratch.sh`'s stage-2 capability probe does not clear an inherited `SIMPLE_BOOTSTRAP_STAGE4=0` and still falls back to the seed for Stage 4 | `f703790073c` (2026-08-08, fix(bootstrap): isolate stage2 capability from stage4 guard) |
| `stage4_fix_tool_sync_entry_spec.spl` | whole file | `src/compiler/90.tools/fix/main.spl` is still `async fn main() -> Int` with `dry_run: Bool` and `.slice(`; the synchronous, native-lowerable fix entry does not exist | `38f27b8c529` (2026-08-04, fix: advance LLVM23 stage4 past formatter and lexer) |
| `stage4_smoke_gate_spec.spl` | example "publishes the Linux LLVM full CLI with its hosted providers"; 12 workflow path-filter assertions in "gates test lint and duplicate-check…"; 2 workflow step-order assertions in "builds and requires the dedicated compiler backfill…" | `rust-bootstrap-multiplatform.yml` no longer has the pure-Simple full-bootstrap job, failure-log upload, hosted full-CLI provider staging/upload, the essential-tools push path filters, or the `cargo build --profile bootstrap -p simple-compiler-backfill` step. **These were removed by `e274cd33719` itself (-443 lines), not by an intentional workflow change** — confirm whether that removal was wanted before re-landing | last present at `ae55a746719` |

## Re-land checklist

1. Land the feature on main.
2. `git show <origin>:test/01_unit/compiler/bootstrap/<spec>` and restore the
   spec (or the retired example), escaping literal `{` in needles as `\{`.
3. Run it under the seed and the self-hosted CLI; it must pass on both.
