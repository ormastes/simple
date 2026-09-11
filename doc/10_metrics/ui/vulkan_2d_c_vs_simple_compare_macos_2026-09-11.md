# Vulkan 2D: C reference vs Simple (interpreter) — macOS M4, manual row

`compare_status=skipped mode=manual` — see
`doc/08_tracking/bug/vulkan_2d_c_compare_skips_on_macos_2026-09-11.md` for why
the gate itself cannot produce a `pass`/`fail` row on this host (two
independent skip causes: no admission step in the script, and the deployed
binary is seed-class). This table replicates the script's own build/run
commands manually, same workload both legs, real MoltenVK.

- Host: macOS, Apple M4, MoltenVK ICD (`/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`)
- Workload: 800x600, 64 rects, 300 sample frames, 5 warmups (script defaults)
- `origin/main` measured at: `75b81c1d1f0` (#528 merge)
- Simple binary: `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`
  (Rust seed-class artifact — `--version` = `Simple v1.0.0-rc.1`, no
  self-hosted CLI deployed on this host), size/mtime `stat -f '%z %m'` before
  and after run: `26264696 1788766698` (unchanged)
- Simple leg command: `SIMPLE_RUST_SEED_WARNING=0 SIMPLE_LIB=src
  SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
  VK_ICD_FILENAMES=<icd> VK2D_W=800 VK2D_H=600 VK2D_RECTS=64 VK2D_FRAMES=300
  VK2D_WARMUPS=5 VK2D_READBACK=1 VK2D_DUMP_FB=<path> <bin> run
  test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl`
- No `--batch` / batch env knob exists in `vk2d_bench.spl` at this tip (only
  single-mode); recorded `n/a at 75b81c1d1f0`.

| leg | mode | device | p50 ms/frame | p95 ms/frame | fps (1000/p95) |
|---|---|---|---|---|---|
| C reference | native, single | Apple M4 (vendor=106b id=1a040209) | 0.436 | 1.060 | 943.4 |
| Simple | interpreter, single | Apple M4 (vendor=0000106b id=1a040209) | 34.551 | 35.153 | 28.4 |
| Simple | batch | n/a — no batch knob in `vk2d_bench.spl` at this tip | — | — | — |

Ratio (Simple p95 / C p95): **33.16x** — device identity matches across legs
(`Apple M4` both sides), so this is a genuine same-device comparison, not a
`device-mismatch` blocked state. Budget in the gate script is 2.0x
(`VK2D_BUDGET_X1000` default 2000) — this ratio is far over budget, i.e. would
be `compare_status=fail` if the aggregate admission gap (Cause 1 in the bug
file) were fixed and the row were admitted, not `pass`.

Both legs' checksums matched (`checksum=10460147`), confirming identical
rendered content.

Evidence: gate run (all-skipped) at
`build/vulkan-2d-c-compare/runs/run-20260911T060740Z-64492/` (C leg measured
cleanly there too: `p50_ns=436000 p95_ns=1060000`); manual Simple leg raw
stdout captured to a local scratch log (not committed — regenerate via the
command above).
