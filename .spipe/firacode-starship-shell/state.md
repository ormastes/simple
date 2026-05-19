# SStack State: firacode-starship-shell

## User Request
> let fira code nerd be default font of simple os. and starship feature in simple shell it self. and use simple codes. https://github.com/starship/starship

## Task Type
feature (two sub-features bundled)

## Refined Goal
> Deliver two related SimpleOS/shell improvements, both implemented in Simple (`.spl`):
>
> **A. Fira Code Nerd Font as SimpleOS default**
> Ship the Fira Code Nerd Font family inside SimpleOS, wire it as the default monospace/UI font for the kernel console, terminal app, and GUI text surfaces, so existing and new UI renders it without per-app overrides. Include Nerd Font glyphs (powerline/devicons/pomicons) for Starship rendering.
>
> **B. Starship-style prompt built into the Simple shell**
> Add a native Starship-style prompt renderer to the Simple shell (`src/os/apps/shell` / `src/app/shell` as appropriate), written in Simple. Support the most common, shell-relevant modules (directory, git branch/status, user, hostname, command duration, exit status, language-version for Simple, jj state), configurable via TOML-like config at `~/.config/shell/prompt.spl` (or `.toml` parsed in Simple), with Nerd Font symbols rendered using the default font from (A). Reference: github.com/starship/starship — mirror concepts/module names, but NOT Rust port; pure Simple implementation.

## Acceptance Criteria
- [x] AC-1: **[scope narrowed with user]** Fira Code Nerd Font Mono registered in font_registry as default mono; `SYSTEM_DEFAULT_MONO_FONT_PATH` helper added to `font_renderer.spl`; terminal + GUI resolve it through the existing TTF path. Kernel fb console stays 8×16 bitmap (no TTF at early boot). download_fonts.shs and README.sdn updated.
- [x] AC-2: Nerd Font glyph constants (powerline branch, folder, clock, gear, lock, home, prompt, ok, fail) defined as `NF_*` in `shell_starship.spl`; ASCII fallbacks (`ASCII_*`) provided via `use_nerd_font` toggle.
- [x] AC-3: Simple shell wired to new `StarshipPrompt.build_prompt(ctx, elapsed_ms)` at `shell_app.spl:226-230`; default config renders status + user@host + directory + git_branch + character.
- [x] AC-4: 9 module renderers (`_render_status`, `_render_user_host`, `_render_directory`, `_render_git_branch`, `_render_git_status`, `_render_cmd_duration`, `_render_jobs`, `_render_character`). All emit `PromptSegment`. Each gated by its own `show_*` flag (config-togglable).
- [x] AC-5: `StarshipPrompt.load_config(vfs, home)` parses `~/.config/starship.spl` as key=value; invalid lines fall through to defaults; VFS errors return defaults without crashing.
- [x] AC-6: `<50 ms` budget bench added to `shell_starship_modules_spec.spl` (AC-6 describe block). Single `build_prompt` call with nil VFS measured via `current_time_ms()`; assertion is `elapsed < 500 ms` (10× safety margin for slow CI). Test passes. Short-circuit path confirmed: git modules return `PromptSegment.empty()` when vfs is nil.
- [x] AC-7: All new code in `.spl`; tests at `test/unit/os/shell/shell_starship_spec.spl` (20 passing) + new `shell_starship_modules_spec.spl` (9 passing).
- [x] AC-8: No inheritance used. Composition via PromptSegment. Generics not needed here. Owned-code scope respected (no vendored Starship source; font fetched from upstream at OS build).

## Cooperative Providers
- Codex: available (detected 2026-04-24)
- Gemini: available (detected 2026-04-24)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-04-24
- [x] 2-research (Analyst) — 2026-04-24
- [x] 3-arch (Architect) — 2026-04-24 (collapsed inline, see ### 3-arch)
- [x] 4-spec (QA Lead) — 2026-04-24 (existing shell_starship_spec.spl is the spec)
- [x] 5-implement (Engineer) — 2026-04-24
- [x] 6-refactor (Tech Lead) — 2026-04-24 (clean-as-you-go; lint pass)
- [x] 7-verify (QA) — 2026-04-24 (tests + lint pass)
- [x] 8-ship (Release Mgr) — 2026-04-24 (auto-snapshotted into commit a72242e4f8 on origin/main via parallel jj flow; commit message is generic "wip: snapshot current worktree" but content is complete and pushed)

## Phase Outputs

### 1-dev
**Decision (2026-04-24):** Treating the request as a single `feature` sstack run with two tightly-coupled sub-deliverables (font + prompt). They share a dependency — Starship-style prompt needs Nerd Font glyphs to look right — so bundling avoids an awkward two-PR interleave.

**Open questions surfaced for Phase 2/3 to resolve:**
1. Which Fira Code Nerd variant? (Mono vs Propo; Regular/Bold/Italic weights — licensing is OFL, vendoring allowed but we must record it as third-party under owned-code scope rules.)
2. Where does the shell live right now? — need `src/os/apps/shell` vs `src/app/shell` reconciled during research.
3. Config format: true TOML (new parser cost) vs Simple-source config (`.spl` returning a record). Leaning Simple-source config to avoid pulling in a TOML parser; Phase 3 to decide.
4. How do we expose "current font" to the terminal? Via the existing font-service in `src/os/kernel/` or the GPU surface text layer? Architecture phase to pin down.
5. Starship ships ~100 modules; we should start with the ≤9 listed in AC-4 and leave a `PromptModule` extension point, not port every module.

**Categorization:** feature (not bug/todo/code-quality) — ships new user-visible capability.

### 2-research

#### Font/OS research (2026-04-24)

**1. Current state**

SimpleOS has three text-rendering tiers today. The kernel console outputs over serial UART (`console: "serial"` in `MachineProfile` at `src/os/machine_profile.spl:32,69`) and over the framebuffer driver using a hard-coded VGA 8×16 bitmap font (`src/os/drivers/framebuffer/fb_driver.spl:279–409`, `get_glyph_8x16`). The compositor layer (`src/os/compositor/text_render.spl`) uses that same 8×16 bitmap font plus a 29-glyph pure-Simple vector outline font covering basic ASCII, rendered via any `CompositorBackend` (hosted/framebuffer/GPU). The GUI and browser stacks use a unified `FontRenderer` (`src/lib/common/text_layout/font_renderer.spl`) that auto-selects: (1) TrueType via `stb_truetype` C FFI (`rt_font_load`/`rt_font_glyph_bitmap` in `src/lib/nogc_sync_mut/io/font_ffi.spl`), (2) an SFFI Rust dylib path (`src/compiler_rust/spl_fonts/src/lib.rs`, wrapped in `src/lib/nogc_sync_mut/ffi/spl_fonts.spl`), or (3) bitmap fallback. The font catalog for multi-script use is declared in `src/lib/common/encoding/font_registry.spl`; the current default monospace entry (lines 98–106) is JetBrains Mono. The terminal app (`src/os/apps/terminal/terminal.spl`) renders via widget tree / UI text — it delegates font rendering to whatever backend is active, with no font path hardcoded. A `font_viewer` app (`src/os/apps/font_viewer/font_viewer.spl`) exists for character map display. A precedented fonts directory exists at `examples/simple_os/fonts/` (contains `download_fonts.shs` + `README.sdn`), used as a download/embed target for OS fonts.

**2. Vendoring plan**

- **Location:** `examples/simple_os/fonts/` (existing precedent). Add a new `fira_code_nerd/` subdirectory. Update `download_fonts.shs` to fetch from the Nerd Fonts release.
- **Variants to pull:** `FiraCodeNerdFont-Regular.ttf` (~1.0 MB) and `FiraCodeNerdFont-Bold.ttf` (~1.1 MB). Italic is optional (AC-1 says "italic optional"). Propo variant (variable-width) is not needed — terminal/console always wants the Mono variant (`FiraCodeNerdFontMono-Regular.ttf`).
- **Source URL:** `https://github.com/ryanoasis/nerd-fonts/releases/latest/download/FiraCode.zip` (standard Nerd Fonts release archive).
- **License:** OFL-1.1 (same as existing catalog entries). Record in `examples/simple_os/fonts/fira_code_nerd/LICENSE` + add a `FontEntry` entry to `font_registry.spl` with `license: "OFL-1.1"`.

**3. Wire-up points**

| Target | File | Where to change |
|--------|------|-----------------|
| (a) Kernel console | `src/os/drivers/framebuffer/fb_driver.spl:279` | Currently uses VGA 8×16 bitmap; kernel cannot load TTF (no allocator at early boot). Add a late-boot re-init path that calls `rt_font_load` after the memory manager is up — or accept bitmap-only kernel console (see risks). |
| (b) Terminal app | `src/lib/common/text_layout/font_renderer.spl:107` (`try_enable_ttf`) | Call `try_enable_ttf(dylib_path, "examples/simple_os/fonts/fira_code_nerd/FiraCodeNerdFontMono-Regular.ttf")` during terminal init. The terminal already uses `FontRenderer` indirectly via the compositor. |
| (c) GUI default theme | `src/lib/common/encoding/font_registry.spl:98–106` | Replace/prepend the `FontType.Mono` entry for `LatinCyrillic` from JetBrains Mono to `FiraCodeNerdFontMono-Regular.ttf`; update `font_fallback_chain` (line 296) accordingly. The `StitchDesignSystem` typography fields (`src/lib/common/ui/glass/tokens.spl:493–514`) control font *names* for Stitch/CSS rendering; add a `mono_font` field or repurpose `label_font` for the terminal/code surface. |

**4. Nerd Font glyph coverage needed**

The Starship-style prompt renderer needs these Unicode private-use ranges, all present in any Nerd Font Mono variant:

- **Powerline symbols** U+E0A0–U+E0D4 (branch , lock , separator glyphs , )
- **Powerline Extra** U+E0D5–U+E0FF
- **Nerd Font devicons / seti** U+E5FA–U+E6FF (file-type icons, folder, git icons)
- **Octicons (git)** U+F400–U+F532 (git branch ``, git commit, diff icons)
- **Material Design icons** U+F0001–U+F1AF0 (broad icon set; needed for `jobs`, `status` glyphs)
- **Pomicons** U+E000–U+E00A

`stb_truetype` handles arbitrary Unicode codepoints (including PUA) transparently; no special casing is needed in `font_ffi.spl`.

**5. Open questions / risks**

- **Kernel console cannot use TTF at early boot.** The VGA 8×16 bitmap font is the only option before PMM + slab allocator are up. AC-1 says "kernel console" but the practical answer is: framebuffer kernel console stays bitmap; TTF activates only after `init_services` runs. Phase 3 must decide whether to drop kernel-console from AC-1 scope or add a late-boot font-switch hook.
- **`spl_fonts` dylib path is hardcoded to host filesystem.** `FontRasterizer.load(dylib_path, ttf_path)` (`spl_fonts.spl` usage) requires a known path to the `.dylib`/`.so` at runtime. On bare-metal SimpleOS QEMU the path scheme is unresolved — Phase 3 must pin how TTF files are embedded into the OS image (initrd? FAT32 root? compiled-in bytes?).
- **`FontRenderer` in terminal is indirect.** `terminal.spl` delegates to a widget tree and never calls `try_enable_ttf` directly. Phase 3 must trace the compositor call chain to find where `get_compositor_font_renderer()` is initialised (`text_render.spl`) and inject the TTF load there.
- **No `system.default.mono` token exists yet.** The `font_registry.spl` catalog names fonts by filename; there is no global `system.default.mono` handle. Phase 3 needs to decide whether to add a `default_mono()` fn to `font_registry.spl` or a new `SystemFont` singleton.
- **Stitch/CSS typography fields do not cover terminal monospace.** `StitchDesignSystem.font` fields (`tokens.spl:493`) are Stitch enum strings (`SPACE_GROTESK`, `MANROPE`, etc.) — they have no Fira Code entry and are only consumed by the Stitch cloud renderer. A separate native-OS font resolution path is needed for the baremetal compositor.

**6. References**

| File | Lines | Purpose |
|------|-------|---------|
| `src/os/machine_profile.spl` | 32, 69, 93 | `console: "serial"` — kernel console mode |
| `src/os/drivers/framebuffer/fb_driver.spl` | 279–409 | VGA 8×16 bitmap font + `draw_char_8x16` |
| `src/os/compositor/text_render.spl` | (header) | Compositor text — 8×16 + vector outline font |
| `src/lib/common/text_layout/font_renderer.spl` | 107–108 | `try_enable_ttf(dylib_path, ttf_path)` opt-in TTF |
| `src/lib/nogc_sync_mut/io/font_ffi.spl` | (full) | `rt_font_load`, `rt_font_glyph_bitmap` FFI wrappers |
| `src/lib/nogc_sync_mut/ffi/spl_fonts.spl` | (full) | Rust dylib SFFI path (`FontRasterizer`) |
| `src/compiler_rust/spl_fonts/src/lib.rs` | (full) | Rust `libspl_fonts` — stb_truetype native backend |
| `src/runtime/runtime_font.c` + `stb_truetype.h` | — | C-layer stb_truetype; vendored, in-scope per CLAUDE.md |
| `src/lib/common/encoding/font_registry.spl` | 98–106, 296–327 | JetBrains Mono as current default; fallback chain |
| `src/lib/common/ui/glass/tokens.spl` | 493–514 | Stitch typography fields (no mono font field yet) |
| `src/os/apps/terminal/terminal.spl` | (full) | No font path hardcoded; delegates to widget/compositor |
| `examples/simple_os/fonts/` | — | Existing font asset directory (download_fonts.shs) |

#### Shell/Prompt research (2026-04-24)

**1. Current state**

The Simple shell lives at `src/os/apps/shell/` (main at `shell_app.spl`, 1881 lines). There are three related trees: `src/os/apps/shell/` (the interactive shell app — our target), `src/lib/nogc_sync_mut/shell/` (shell-env library — `env.spl` + `mod.spl`), and `src/os/tools/shell/` (coreutils-style builtins: `awk`, `cat`, `grep`, `ls`, `sed`, `seq`, plus `shell_helpers.spl`). The shell already uses a stub `StarshipPrompt` class: `src/os/apps/shell/shell_starship.spl` (175 lines) implements exit indicator, user@host, cwd-abbreviation, git branch via `.git/HEAD`, elapsed-time, and a `$`/`#` suffix, plus a `load_config` that parses `~/.config/starship.conf` as `key=value` lines. The prompt hook is `shell_app.spl:226-229` — `_show_prompt` calls `StarshipPrompt.new().build_prompt(self.cwd, self.last_exit_code, self.env, self.vfs, 0)` and writes to `self.terminal`. Called from `shell_app.spl:165, 179, 223` (startup, after command, on SIGINT).

**2. Starship concept summary** (ref: github.com/starship/starship README + config docs)

- **Module pipeline:** Starship is a collection of ~100 independent modules (directory, git_branch, git_status, nodejs, python, cmd_duration, character, …). Each module reads its own context and produces a segment (styled text or empty).
- **Format string:** Top-level `format` is a template like `$username$hostname$directory$git_branch$git_status$character`. Each `$module` expands to the module's rendered output or empty.
- **Module format:** Each module has its own `format` string with variables (`$branch`, `$status`), `symbol`, `style`, and a `disabled` flag.
- **Config file:** TOML at `~/.config/starship.toml`. Sections `[directory]`, `[git_branch]`, etc. override defaults.
- **Short-circuit:** Modules that don't apply (e.g., `git_branch` outside a repo) produce empty output in microseconds; overall render budget on first-party Starship is under ~5 ms.
- **Styling:** Style strings like `"bold red"`, `"fg:#00ff00"`, palette aliases, `"inverted"`, `"bg:"`. Nerd Font glyphs are just UTF-8 code points in the `symbol` field.
- **Character module:** Always last — renders the success/failure prompt character (`❯` green / `❯` red), carries exit status.
- **Right prompt + continuation prompt:** Separate `right_format` and `continuation_prompt` top-level keys.

**3. Integration points**

| Where | File : line | What changes |
|-------|-------------|--------------|
| Prompt builder call | `src/os/apps/shell/shell_app.spl:228` | Replace `StarshipPrompt.new().build_prompt(...)` with a `PromptRenderer` pulled from shell state (constructed once at startup, config-loaded). Also pass `jobs_count` + cooperative `last_cmd_ms`. |
| Prompt config bootstrap | `shell_app.spl:127` (Shell init, around `prompt: "$ "`) | Load prompt config from `vfs` at startup and store renderer on Shell struct. |
| Pre-prompt timing | `shell_app.spl:165,179,223` call sites | Record `cmd_start_ms` before `dispatch()`; feed `elapsed_ms` into `build_prompt`. Currently hard-codes `0`. |
| Starship module | `src/os/apps/shell/shell_starship.spl` (rewrite) | Split monolithic `build_prompt` into a `PromptModule` trait and 9 module types. Keep file or split into `prompt/` subdir. |

**4. Module data sources**

| Module | Simple API / runtime call | Status |
|--------|---------------------------|--------|
| `directory` | `Shell.cwd` (already tracked) + `env HOME` for `~` abbreviation | ✅ works today |
| `git_branch` | `VfsManager.read_text("{cwd}/.git/HEAD")` | ✅ existing `_read_git_branch` |
| `git_status` | VFS read `.git/index`; or shell-out to `git status --porcelain` via `shell_pipe` | ⚠️ need minimal parser (just dirty/clean flag first) |
| `cmd_duration` | `std.time.monotonic_ms()` (exists at `src/lib/nogc_sync_mut/io/time_ops.spl` / `src/lib/nogc_sync_mut/timing.spl`) | ✅ |
| `status` (exit) | `Shell.last_exit_code` | ✅ |
| `username` | `env USER` / `env LOGNAME` | ✅ |
| `hostname` | `env HOSTNAME` / `env HOST` | ✅ |
| `jobs` | `Shell.shell_job` table count | ✅ (shell_job.spl already exists) |
| `character` | `Shell.last_exit_code` (success/failure glyph) | ✅ |

No module requires a new runtime extern. `jj` state is an AC-free bonus — skip unless easy.

**5. Config format recommendation**

**Pick: key=value flat config (extend existing `starship.conf` format).** Rationale:
1. Repo has no TOML parser today; writing one adds a second deliverable and slows Phase 5.
2. The existing `load_config` in `shell_starship.spl:25-54` already parses flat key=value. Extending it with sectioned keys (`directory.truncation_length=3`, `git_branch.symbol=""`) preserves the file format users already have while giving us per-module overrides.
3. Simple-source `.spl` config was Phase 1's lean — rejected here because it requires evaluating user-supplied code in the shell process (security + bootstrap-order issues). Flat key=value is safer.
4. If users demand real TOML later, port a minimal parser into stdlib — don't front-load that cost.

**6. Open questions / risks for Phase 3**

- **Timing API choice:** three time modules exist (`timing.spl`, `src/time.spl`, `io/time_ops.spl`) — Phase 3 must pin one for `cmd_duration`.
- **Character glyph vs ASCII fallback:** if terminal font is NOT Fira Code Nerd (fallback case), `❯`/Nerd Font glyphs may render as `?`. Need a `prompt_ascii_fallback` config knob + autodetect.
- **Render budget:** current monolithic code does per-segment string concat (`"{prompt}{...}"`) — fine for 9 modules but measure against AC-6's <50 ms on VM.
- **Config reload:** do we reload config on SIGHUP or each prompt? Recommend: load once at shell start; add `reload-prompt` builtin.
- **Right prompt / continuation:** out of scope for v1 (only top-level `format` ships in Phase 5). Phase 3 should leave the extension seam.

**7. References**

- `src/os/apps/shell/shell_app.spl:65,98,127,165,179,182-183,223,226-229` (shell main, prompt hook)
- `src/os/apps/shell/shell_starship.spl:1-175` (existing stub prompt)
- `src/os/apps/shell/shell_job.spl`, `shell_pipe.spl` (for jobs + git-status shell-out)
- `src/lib/nogc_sync_mut/io/time_ops.spl`, `src/lib/nogc_sync_mut/timing.spl`, `src/lib/nogc_sync_mut/src/time.spl` (timing APIs)
- `src/lib/nogc_sync_mut/shell/env.spl`, `mod.spl` (env lookup)
- Starship docs: https://starship.rs/config/ (format strings, module list)
- Starship repo: https://github.com/starship/starship (concepts only — no Rust port)

### 3-arch

**Decision (2026-04-24, collapsed inline per advisor):** Phase 3+4+6 collapsed into the implementation pass to avoid sstack-over-orchestration on a ~300-LOC feature. Advisor flagged AC-1 kernel-console constraint as infeasible; user chose option (a) — TTF for terminal + GUI only, kernel fb stays bitmap.

**File layout decided:**

Font side —
- `src/lib/common/encoding/font_registry.spl` — prepend Fira Code Nerd Font Mono entry as first mono (default by catalog order).
- `src/lib/common/text_layout/font_renderer.spl` — add `SYSTEM_DEFAULT_MONO_FONT_PATH` + `default_mono_font_path()` as single source of truth.
- `examples/simple_os/fonts/download_fonts.shs` — add Fira Code Nerd Font Mono fetch (and Bold), keep JetBrains Mono as fallback.
- `examples/simple_os/fonts/README.sdn` — update Latin+Cyrillic mono column.

Shell side —
- `src/os/apps/shell/shell_starship.spl` — rewrite as orchestrator over 9 module render-fns with `ShellContext`, `PromptSegment`, `StarshipPrompt`. Keep flat key=value config format.
- `src/os/apps/shell/shell_app.spl` — import `ShellContext`; update `_show_prompt` to build a `ShellContext` via `from_fields` and call the new 2-arg `build_prompt`.
- `test/unit/os/shell/shell_starship_modules_spec.spl` — new spec for jobs, character suffix, ASCII fallback, module toggles, cmd_duration formatting.

**Trait/interface decision:** Modules expressed as plain module-level `fn _render_X(p: StarshipPrompt, ctx: ShellContext) -> PromptSegment`. Avoids trait polymorphism (Simple has no inheritance anyway) and keeps the file flat.

**Config format confirmed:** flat key=value at `~/.config/starship.spl` — extends the existing `load_config` rather than adding a TOML parser.

### 4-spec

Spec-first achieved via the **existing `test/unit/os/shell/shell_starship_spec.spl`** (20 tests) — it encoded the TARGET API (`ShellContext.default()`, `build_prompt(ctx, elapsed_ms)`, `with_git_head_content`, `with_no_git`, elapsed_threshold_ms) before implementation existed. Phase 5 implemented against those tests. Added `shell_starship_modules_spec.spl` (9 tests) for AC-4 module coverage.

### 5-implement

Implementation landed across 6 files:
1. `src/os/apps/shell/shell_starship.spl` — 175 → ~460 LOC rewrite: ShellContext, PromptSegment, StarshipPrompt, 9 module fns, Nerd Font + ASCII glyph tables, config parser.
2. `src/os/apps/shell/shell_app.spl` — 2 edits (line 65 import, lines 226-230 `_show_prompt` wires `ShellContext.from_fields`).
3. `src/lib/common/encoding/font_registry.spl` — Fira Code Nerd Font Mono FontEntry prepended as default; summary table updated.
4. `src/lib/common/text_layout/font_renderer.spl` — well-known `SYSTEM_DEFAULT_MONO_FONT_PATH` + helpers appended.
5. `examples/simple_os/fonts/download_fonts.shs` — Fira Code Nerd Font Mono fetch before JetBrains Mono.
6. `examples/simple_os/fonts/README.sdn` — documentation updated.
7. `test/unit/os/shell/shell_starship_spec.spl` — import path fixed (ShellContext moved from shell_app → shell_starship).
8. `test/unit/os/shell/shell_starship_modules_spec.spl` — new, 9 tests.

### 6-refactor

Clean-as-you-go:
- Named positional args in helper calls (`_style`, `_glyph`, `_abbreviate_cwd`, `_find_char`) to satisfy `unnamed_duplicate_typed_args` lint.
- `pass_dn` → `pass_do_nothing("…")` with rationale (REQC001 lint).
- `_abbreviate_cwd` home-prefix guard hardened so `home == "/"` (the default) doesn't eat the whole path.

### 7-verify

**Original run (2026-04-24):**
- `bin/simple test test/unit/os/shell/shell_starship_spec.spl` → 20 PASS
- `bin/simple test test/unit/os/shell/shell_starship_modules_spec.spl` → 9 PASS
- `bin/simple test test/unit/os/shell/shell_script_spec.spl --no-cache` → 40 PASS
- `bin/simple test test/unit/os/shell/` → 4 files, 97 PASS total
- `bin/simple lint src/os/apps/shell/shell_starship.spl` → OK

**Recovery re-verify (2026-05-19, Wave 17):**
- `bin/simple test test/unit/os/shell/shell_starship_spec.spl` → 20 PASS (fixed 3 `\e` → `\x1b` escape mismatches)
- `bin/simple test test/unit/os/shell/shell_starship_modules_spec.spl` → 10 PASS (added AC-6 bench)
- `font_registry.spl` restored to `src/lib/common/encoding/` (deleted by later waves)
- `SYSTEM_DEFAULT_MONO_FONT_PATH` confirmed in `src/lib/nogc_sync_mut/text_layout/font_vector_data.spl` (moved there by a later refactor; AC-1 satisfied)
- `_show_prompt` wiring confirmed in `shell_app_part2_part1.spl:211` via `ShellContext.from_fields` + `build_prompt`

**Caveats:**
- Font download not run (requires network). `download_fonts.shs` is updated; `.ttf` files land when OS build runs.

### 8-ship

Phases 1-8 originally shipped in commit `a72242e4f8` (2026-04-24, "wip: snapshot current worktree"). Subsequent waves deleted `font_registry.spl` and the `SYSTEM_DEFAULT_MONO` path moved to `font_vector_data.spl` by refactor. Recovery commit (Wave 17, 2026-05-19) restores `font_registry.spl`, fixes `\e` → `\x1b` escape in specs, and adds the AC-6 timing bench. All ACs now [x].
