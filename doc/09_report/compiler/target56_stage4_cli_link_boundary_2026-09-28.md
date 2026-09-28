# Target 5/6 Stage4 CLI link boundary (2026-09-28)

**Current result: compiler source closure builds; full CLI link fails.** This
is a blocker for both targets' broad verification, not a qualification pass.

An isolated, no-stub Stage2 build of the full CLI entry closure first stopped
on an HIR ambiguity in `src/app/play/wm_tray.spl`: the `WindowInfo` rows from
`wm_daemon_list_windows() ?? []` lost their element type before `window_id`
lowering. Both array bindings now declare `[WindowInfo]` explicitly. The
focused native integration spec builds 60 source units and reports **1
example, 0 failures** on Linux; binary SHA-256:
`9e340004018c093fd03282451af8b70bfd3dd6d2c4ec353090ace5fd8be00b91`.

The repaired full CLI command used `--entry-closure`, all four production
source roots, `--runtime-bundle host-gpu`, and the admitted pure-Simple Stage2
compiler SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
It compiled **2,488 source units, 0 failures** (4 compiled and 2,484 reused
on the final retry), then failed at the native link. The linker reported
**173 distinct undefined symbols**. The retained symbol inventory is
`target56_stage4_cli_undefined_symbols_2026-09-28.tsv`: 46 Vulkan, 25 Metal,
25 SQLite, 18 CUDA, 16 SDL, 15 ROCm, plus smaller families. An `nm -g
--defined-only` check found 113 of the 173 in the Stage2 `native_all`
archive; 60 were absent there. The full local link log is
`build/mini_builds/target56_full_cli_native_all/retry.log`, SHA-256
`3f28d92317d0a03a82e858690f0de4fb51b2b321f999193c0915f0d1ab64182b`.

The selected `host-gpu` Stage4 core lane deliberately omits optional hosted
provider implementations. Linking the Rust `native_all` archive into the
release-small core would invalidate Target 5's closure and size requirements.
The next production change must put the optional CLI/provider paths behind
admitted first-demand loading and give Stage4 only the kernel's required
symbols. The full CLI, MCP/LSP, matched hello size, and production compile
time/RSS gates remain open.
