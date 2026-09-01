# `Code Idiom & Structural Ratchet Gates` is RED on `main` — blocks every PR

- Date: 2026-09-01
- Status: OPEN — pre-existing on `main`, NOT caused by any open PR
- Required check (ruleset `spipe-vcs-v3-main`, id 21573643): `Code Idiom & Structural Ratchet Gates`
- Workflow: `.github/workflows/repo-hygiene.yml`, job `code-idiom-gates`

## Evidence of pre-existence

| where | run / job | verdicts |
|---|---|---|
| `main` tip `1b12bd36b` | run `33486779024`, job `99788604481` | same 3 gates FAIL |
| PR #252 head `477d446129e` | run `33488592730`, job `99794430241` | same 3 gates FAIL, byte-identical offender lines |

PR #252 touches 9 files (7 `src/lib/**`, 1 spec, 1 doc). **None** of the three
offenders is among them, and the offender lines are identical on `main`.
Verdict: PR-caused = NO. Pre-existing on `main` = YES.

## The three failing steps (verbatim)

1. **UI backend-isolation ratchet gate** — `scripts/check/check-ui-backend-isolation.shs`
```
ui_backend_isolation_new_violation=RT:examples/09_embedded/simple_os/arch/riscv64/wm_vulkan_smoke_entry.spl
examples/09_embedded/simple_os/arch/riscv64/wm_vulkan_smoke_entry.spl:34:extern fn rt_mmio_write_u32(addr: u64, value: u32)
examples/09_embedded/simple_os/arch/riscv64/wm_vulkan_smoke_entry.spl:60:            rt_mmio_write_u32(base + off.to_u64(), argb)
ui_backend_isolation_baselined=30
ui_backend_isolation_current=31
ui_backend_isolation_new=1
ui_backend_isolation_ok=false
```

2. **Guard-wiring ratchet gate** — `scripts/check/check-guard-wiring.shs`
```
check-guard-wiring: FAIL — 1526 guard(s) checked, 14 NEW unwired (743 baselined as known debt), 2 stale/bad baseline or opt-out line(s), 0 copied hook(s)
```
14 NEW unwired guards:
`check-freestanding-byte-array-slot-tags.shs`,
`check-freestanding-dict-arms-in-every-definition.shs`,
`check-freestanding-dict-write-path.shs`,
`check-freestanding-rt-value-int-tags.shs`,
`check-prepush-no-recursion.shs`,
`check-simpleos-arm64-wm-vulkan-pixel-evidence.shs`,
`check-simpleos-dbfs-server-roundtrip-ovmf.shs`,
`check-simpleos-nvfs-server-roundtrip-ovmf.shs`,
`check-simpleos-riscv64-components-in-guest-opensbi.shs`,
`check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`,
`check-simpleos-riscv64-wm-render-smoke-opensbi.shs`,
`check-simpleos-x86-64-components-in-guest-ovmf.shs`,
`repro-selective-vs-whole-import.shs`,
`run-riscv64-text-probe-opensbi.shs`.

2 stale baseline entries (now wired — delete their lines in
`scripts/check/` unwired baseline):
`check-dual-run-shadow.shs`, `check-unbacked-extern-ratchet.shs`.

3. **PID/clock-keyed build artifact ratchet**
```
FAIL — 34 candidate(s) checked in /home/runner/work/simple/simple; NEW pid/clock-keyed build artifact(s): src/compiler/70.backend/backend/runtime_compiler.spl
```

## Why this blocks everything

The ruleset requires this check on every merge to `main`. Because it is red on
`main` itself, **no PR can ever go green** until the three offenders above are
fixed on `main`. The debt is owned by whoever landed the offending files, not
by the PR authors it now blocks.

Explicitly NOT done here: no baseline was regenerated. Per
`.claude/rules/vcs.md`, `--generate-baseline` is for reviewed updates only;
using it to clear a red is how a ratchet silently stops ratcheting.

## Cross-platform impact

None. This is a CI-configuration/debt record; no source was changed, so Windows
and Unix behaviour are both unaffected.
