# `check-vulkan-2d-c-compare.shs` always reports `compare_status=skipped` — two independent causes

Measured 2026-09-11 on macOS (Apple M4), at `origin/main` = `75b81c1d1f0` (#528 merge; #529/#530 not present at fetch time).

## Cause 1 (structural, not host-specific): aggregate() never sees `c_st=admitted`

`scripts/check/check-vulkan-2d-c-compare.shs:249-254` (`aggregate()`) requires
`c_st = admitted` and `s_st = admitted` to proceed to a ratio comparison
(lines 216, 223). But the main run body only ever assigns
`c_status=measured-unadmitted` (line ~697, `c_reason=receipt-needs-common-admission`)
after a fully successful live C measurement — it never assigns `c_status=admitted`
anywhere. So even a leg that measures perfectly cleanly reports
`compare_status=skipped compare_reason=c-leg-measured-unadmitted:receipt-needs-common-admission`
unconditionally. This reproduced on this host: the C leg built, ran against
real MoltenVK, and reported a clean contract
(`c_line=c-vulkan-2d ... p50_ns=436000 p95_ns=1060000 ... device_vendor=106b device_id=1a040209`),
and the run still emitted `compare_status=skipped` for this reason alone —
run manifest: `build/vulkan-2d-c-compare/runs/run-20260911T060740Z-64492/`.
A separate common-admission step (not present in this script) is required
before `compare_status` can ever be `pass`/`fail` via the default invocation.
This is fail-open by design per the script's own header (line 30: "Exit: 0
when aggregate is pass or **skipped**") — confirmed empirically, `rc=0`.

## Cause 2 (this host): seed-detector rejects the only deployed self-hosted binary

`scripts/check/check-vulkan-2d-c-compare.shs:739-740`:
```
elif [ -L "$SIMPLE_BIN" ] || simple_binary_is_seed "$SIMPLE_BIN"; then
    simple_reason=bootstrap-seed-forbidden
```
`simple_binary_is_seed` (lines 198-204) matches the deployed macho binary
`/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple` via its
`strings`-based check: that binary literally embeds the text
`"WARNING: this Rust-built Simple binary"` (a runtime warning banner) plus
`compiler_rust/target` path strings, matching two of the three alternations
at line 201 (`rust-built Simple binary`, `compiler_rust/target`). The binary
is genuinely a Rust-seed-class artifact (`--version` reports
`Simple v1.0.0-rc.1`, no self-hosted-CLI marker) — this attribution is
correct, not a false positive to bypass. This repo has **no self-hosted
(pure-Simple) `bin/simple` deployed on this macOS host**, only the Rust seed.

In this worktree's default invocation (no `SIMPLE_BIN` override, no deployed
`bin/simple` at all), the Simple leg instead skips one step earlier via
`no-selfhosted-simple-binary` (line 737, `[ ! -x "$SIMPLE_BIN" ]`) — either
way the Simple leg never reaches `admitted`.

## Resume command for a self-hosted host

Once a genuinely self-hosted (pure-Simple, non-seed) `bin/simple` is deployed
(no `WARNING: this Rust-built Simple binary` string, no `compiler_rust/target`
path strings, not a symlink into the seed tree):
```
SIMPLE_BIN=/path/to/self-hosted/bin/simple \
  sh scripts/check/check-vulkan-2d-c-compare.shs
```
This still will not flip `compare_status` past `skipped` until Cause 1 above
is also fixed (the admission step that promotes `measured-unadmitted` to
`admitted` needs to be wired into this script, or `aggregate()` needs to
accept `measured-unadmitted` as sufficient for a same-host comparison).

## No bypass taken

Per instructions, the tracked script was not edited to route around the
seed-detector or the admission requirement. The comparison row for this run
was produced manually (same workload: 800x600, 64 rects, 300 frames, 5
warmups, both legs against the same MoltenVK ICD) — see
`doc/10_metrics/ui/vulkan_2d_c_vs_simple_compare_macos_2026-09-11.md`,
`mode=manual`.
