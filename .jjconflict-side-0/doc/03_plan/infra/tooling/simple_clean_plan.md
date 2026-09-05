# `simple clean` — manual + auto temp/cache cleanup

Research: `doc/01_research/infra/tooling/cache_temp_cleanup_survey.md`.
Pure Simple; no config files, no daemon — env vars + hardcoded lists only.

## Manual subcommand

```
simple clean [--build] [--cargo] [--qemu-images] [--temp] [--all] [--dry-run]
```

| Target | Paths |
|---|---|
| `--build` | `build/*` entries except `build/freebsd` (kept for `--qemu-images`) |
| `--cargo` | `src/compiler_rust/target/debug`, `.../target/release`, root `target/` |
| `--qemu-images` | `build/freebsd/*.qcow2*`, `build/freebsd/vm/*` (re-downloadable) |
| `--temp` | `/tmp/simple_*`, `/tmp/spl_*` files older than 24 h (grace period) |
| `--all` | all of the above |

Behaviour:
- Sizes printed per target (via `du -sh`) **before** any deletion.
- `--dry-run` lists every path that would be deleted, deletes nothing.
- No target flag → usage + per-target current sizes, exit 0.

## NEVER-TOUCH (hardcoded, checked before allow-roots)

`.spipe/**`, `bin/release/**`, `doc/**`, `.git/**`, `.jj/**`, jj state, and
`src/**` **except** `src/compiler_rust/target/**`. Rejected even when passed
explicitly. Additionally a positive containment gate: every delete path is
lexically normalized (`.`, `..`, `//` resolved) to an absolute path and must
resolve inside one of the allow-roots (`<repo>/build`,
`<repo>/src/compiler_rust/target`, `<repo>/target`, `/tmp/simple_`,
`/tmp/spl_`). Anything outside both gates is refused with a printed reason.
`git gc` is never invoked (jj-colocated repo — documented in the survey).

## AUTO mode (piggybacked on `simple build` start only)

Not wired into `test`/`run` — hot paths stay untouched.

- Opt-IN: runs only when `SIMPLE_AUTO_CLEAN=1` (unset/""/0 → skip). The
  SAFE class on this repo currently holds ~286G including 70G of bootstrap
  artifacts, so an on-by-default sweep would delete high-rebuild-cost state
  under every parallel session; arm it per machine.
- Cap: `SIMPLE_CACHE_MAX_GB` (default **20**; non-numeric/≤0 → default).
- Probe at `handle_build` start: `du -sb` over the SAFE roots
  (`build`, `src/compiler_rust/target`). Total ≤ cap → no further work.
- When exceeded: enumerate first-level SAFE entries (each `build/*` subdir
  except `build/freebsd`, plus cargo `target/debug` and `target/release`),
  stat size + mtime, delete **oldest-first (LRU by mtime)** until total ≤
  **80 % of cap** (ccache-style, avoids re-trigger every build).
- Prints exactly one summary line:
  `auto-clean: freed <X> GB (<n> entries, oldest-first), cache <Y> -> <Z> GB`.
- **Fail-open**: any stat/du/delete error → skip that entry / abort the sweep
  silently and continue the build. Auto-clean must never block a build.

## Implementation map

- `src/app/clean/main.spl` — CLI + pure helpers (`normalize_path`,
  `is_never_touch`, `is_allowed_target`, `lru_delete_set`,
  `auto_clean_threshold`) + `auto_clean_on_build_start()`.
- `src/app/cli/dispatch/table.spl` — `CommandEntry name: "clean"` (mirrors
  `sound`).
- `src/app/build/cli_entry.spl` — `auto_clean_on_build_start()` call at the
  top of `handle_build`.
- Spec: `test/01_unit/app/clean/clean_spec.spl` — dry-run deletes nothing
  (fixture dir), never-touch rejected, LRU order, threshold math, env opt-out.

## Non-goals

Config files, background daemon, per-file cargo artifact GC, git object gc,
cleaning `bin/release` (manual-only with an explicit flag, not implemented).
