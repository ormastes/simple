# CI gate enforcement surface (task #34)

**Filed:** 2026-07-07
**Severity:** low (infra/tracking; hardens enforcement, no product regression)
**Scope:** `.github/workflows/repo-hygiene.yml` + `scripts/check/*.shs` ratchet gates.

W2 established the first automated gate enforcement lane by wiring
`check-cpu-hotloop-idiom.shs` into `repo-hygiene.yml`. jj bypasses the pre-commit
git hook and `build lint` routes the CLI lane to clippy, so **CI is the only lane
that actually runs these standalone gates.** Task #34 extends that lane to the
other green, cheap, structural ratchet gates.

## Two bugs fixed in the existing wiring

1. **Dead workflow path.** `repo-hygiene.yml` step 1 ran `sh scripts/check-repo-hygiene.shs`,
   but that script moved to `scripts/check/check-repo-hygiene.shs` in `2c8b2e6138`
   (Jun 4). The dead path aborted the whole `repo-hygiene` job at step 1 (`sh`
   exit 127), which also made W2's hot-loop gate (step 2) **unreachable** — the
   "first automated gate enforcement" was not actually running. Path corrected;
   hot-loop gate relocated to a green job so it runs.
2. **Ripgrep `-Eq` flag bug.** `check-tui-standalone-closure.shs:25` ran
   `rg -Eq -- '...'`. ripgrep parses `-E` as `--encoding` and consumed `q` as its
   argument (`error: unknown encoding: q`, exit 2), so the `if` was always false
   and the "standalone runtime lane" invariant was **silently never checked**.
   ripgrep uses a regex engine by default (no `-E` needed); fixed to `rg -q --`.
   The check now genuinely runs and passes.

## Gate inventory (ratchet + structural, current tree)

| Gate | Status | Disposition |
|------|--------|-------------|
| `check-cpu-hotloop-idiom.shs` | GREEN | CI-enforced (relocated to green job) |
| `check-ui-backend-isolation.shs` | GREEN after absorb | **CI-enforced** (new) |
| `check-tui-standalone-closure.shs` | GREEN after rg fix | **CI-enforced** (new) |
| `check-workspace-root-guard.shs` | GREEN | **CI-enforced** (new) |
| `check-repo-hygiene.shs` | RED (content debt) | own job; path fixed; NOT green (see below) |
| `check-core-lib-purity.shs` | RED (11 new + 1 stale) | manual; mixed triage (see below) |
| `check-api-arch-guard.shs` | RED (large API delta) | manual; large-drift, do not mass-baseline |
| `check-*-evidence.shs`, renderdoc/vulkan/metal/electron/qemu/bun/node/chrome, `check-*-bitmap-*` (≈200) | RED / timeout | manual/local only — need GPU / QEMU / browser / network / a built `bin/simple`; not CI-appropriate |

## Isolation-gate triage (6 new violations → all absorbed)

All 6 are legitimate pre-existing peer drift of the **same class already
baselined**, absorbed into `ui_backend_isolation_baseline.txt` with source-commit
comments (gate made `#`-comment-aware for annotation + correct counting):

- **3 baremetal OS entry files** (`examples/09_embedded/simple_os/arch/x86_64/`):
  `fs_elf_exec_smoke_entry`, `fs_exec_general_ring3_entry`, `green_carrier_probe_entry`.
  `rt_*` here is legitimate direct hardware/runtime access at the kernel/baremetal
  layer (`rt_debug_exit_success`, `rt_port_outb`, `rt_user_heap_init`,
  `rt_x86_tss_init`, `rt_bare_build_cc1_stack`, `rt_x86_install_syscall_entry_raw`)
  — same as the 50 `arch/x86_64/*_entry.spl` files already baselined.
  Sources: `90eec13805`, `2d1d1d7692`, `d609316609`, `7c30ce49d0`.
- **3 llm_caret CLI files** (`src/app/llm_caret/`): `chat_tui`, `retry`, `tools`.
  `rt_*` here is general system I/O (`rt_env_get`, `rt_stdin_read_line`,
  `rt_file_read/write_text`, `rt_file_exists`, `rt_dir_exists`, `rt_dir_list`,
  `rt_sleep_ms`) caught by the gate's broad `\brt_[a-z0-9_]+` sweep — **not** a
  Metal/Vulkan/DirectX/Software rendering-backend bypass. Same non-GUI class as
  the 8 `src/app/llm_caret/*.spl` files already baselined.
  Sources: `da0a6c5958`, `d90b9c3f51`, `d609316609`.

None is a real new rendering-facade bypass; absorb is the correct ratchet action.
Verified: injecting a fake app-layer `rt_metal_*`/`rt_vulkan_*` extern under
`src/app/cli/` makes the gate report `new=1 / ok=false` and exit 1 (fails the CI
step); removing it returns `new=0 / ok=true`, exit 0.

## Gates left RED / manual-only, with reasons

- **`check-repo-hygiene.shs`** — hard content gate (no allowlist). RED on 22
  pre-existing tracked `.py`/`.sh` files (`test/perf/bench/*.py`,
  `scripts/tool/renderdoc-*.py`, `tools/claude-plugin/*/build.sh`,
  `scripts/setup/spipe/*.sh`, `test/fixtures/js/compat_test.sh`). Fixing that debt
  (convert/rename to `.spl`/`.shs`) is a separate task. Kept in its own job so its
  redness does not mask the green ratchet job's per-gate signal. Only the dead
  path was fixed here (correctness), not the content.
- **`check-core-lib-purity.shs`** — RED, 11 new violations, MIXED: some are clearly
  legit peer drift (`audio/wav_{decode,encode}` import pure `f32_*_bits` from the
  host tier like the baselined `compress/*`; `compress/lzma2_xz_format` is the
  file-I/O split out of the now-stale baselined `compress/lzma2`). But the
  `js/node/{fs,os,process,child_process}_module` + `js/engine/*` group does real
  `rt_file_*`/`rt_process_run`/`rt_env_get`/host-tier imports **inside the pure
  `src/lib/common/` core tier** — a plausible **real tier violation** (Node-compat
  belongs in a host tier, not `common/`). Not baseline-hidden. Left RED and
  reported for separate architectural triage; consequently NOT wired.
- **`check-api-arch-guard.shs`** — RED: ~4 removed + ~40 added public symbols (cli
  `main_part*`/`query_visibility_part*` → `_CliMain`/`_QueryVisibility` refactor,
  new HTTP method/port constants, tier helpers) plus an intentional
  `00_compiler_architecture.md` hash change. Getting it green means
  `--update-baseline`, which is a *deliberate reviewed API-change* action — not a
  CI-wiring side effect. Also ~66 s. Left alone (do not mass-baseline: would hide
  the real API delta). Manual.
- **≈200 evidence/bitmap/renderdoc/vulkan/metal/qemu/electron/bun/node/chrome
  gates** — need a GPU, QEMU, a browser, network, or a freshly built `bin/simple`.
  Not deterministic on a stock `ubuntu-latest` runner. Manual/local only.

## Now CI-enforced (job `code-idiom-gates`, all green, ratchet fail-closed)

`check-cpu-hotloop-idiom.shs`, `check-ui-backend-isolation.shs`,
`check-tui-standalone-closure.shs`, `check-workspace-root-guard.shs`.
Each installs ripgrep if missing and fails the job on exit ≠ 0.

## Still open on #34 (separate work)

- `build lint` → clippy routing for the CLI lane (so the CLI lane runs the real
  Simple lint, not clippy).
- `cli_run_lint` only runs the gates after a rebuild (stale-binary gap).
- `check-repo-hygiene` content debt (22 files) and `check-core-lib-purity`
  `js/node/*` tier triage.

This substantially closes the CI-enforcement piece of #34: the standalone
structural/idiom ratchet gates are now genuinely, non-bypassably enforced.
