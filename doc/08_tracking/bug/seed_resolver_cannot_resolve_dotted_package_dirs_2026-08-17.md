## FIXED 2026-08-17 (seed-side; see Verification status below)

Fix option 1 (the preferred one) is implemented in
`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs` as
"Strategy 5" in `resolve_with_numbered_dirs_recursive`: when the plain
per-segment join and the existing one-level dotted join both miss, join 2+
*pending* segments with a literal `.` against the current directory, longest
window first, bounded by `parts.len() - 1` so at least one segment remains for
the module itself. Because each strategy only returns on success, the walk
backtracks naturally out of prefixes that exist but lead nowhere.

This makes the seed agree with the pure-Simple driver for **all** dotted
directories rather than the four hardcoded in
`driver_source_loading.spl:801` — a rewrite table was explicitly rejected as
fix option 2 because two hand-maintained lists are how this drifted.

Commit: `61502d60632`.

### Repro before the fix (2026-08-17, seed
`bin/release/x86_64-unknown-linux-gnu/simple`)

```
$ bin/simple info
error: semantic: Cannot resolve module: app.package.registry.config
EXIT=1
```

### Verification status — HONEST

The change is Rust, in the seed. It is **not provable from a spec run against
the currently deployed `bin/simple`**, which is the pre-fix seed. It is proven
only after a seed rebuild and redeploy. Do not read a green run of the specs
below on the old binary as evidence; on the old binary they fail to resolve
their own imports and the examples never execute.

Two additional facts found while verifying, both worth knowing:

- `src/app/ui.chromium.acid2/` is a **three-segment** dotted directory
  (two dots). Any fix that joins only two pending segments still misses it, so
  it is the sharper regression case and is covered by the prevention spec.
- The seed tree was independently unbuildable at the time of this fix
  (borrow-check errors in `parser/src/expressions/binary.rs` from a concurrent
  lane, since repaired in the working tree) — worth noting because it blocks
  anyone trying to reproduce this verification.

### Specs

- repro: `test/01_unit/compiler/module_resolution/dotted_package_dir_resolution_spec.spl`
- prevention: `test/01_unit/compiler/module_resolution/dotted_package_dir_convention_prevention_spec.spl`
- both mirrored identically under `test/unit/compiler/module_resolution/`

# Rust seed resolver cannot resolve dotted package directories; `simple info` is dead in seed mode

- **Date:** 2026-08-17
- **Status:** OPEN
- **Severity:** medium (blocks `simple info`, `search`, `yank`, `publish` whenever `bin/simple` is the seed)
- **Component:** `src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`

## Symptom

With `bin/simple` resolving to the Rust seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, 59536728 bytes, 2026-08-16
22:59:37 +0000):

```
$ bin/simple info
WARNING: this Rust-built Simple binary is a bootstrap seed only; ...
error: semantic: Cannot resolve module: app.package.registry.config
```

Exit 1. Reproduced 2026-08-17.

## Root cause

`src/app/info/main.spl:10` does `use app.package.registry.config (default_config)`.
That module is at `src/app/package.registry/config.spl` — a **dotted directory
name**, which is a deliberate repo-wide convention (`src/app/ui.browser/`,
`ui.cli/`, `game.breakout/`, `lsp.handlers/`, `dashboard.render/`, ~20 more).

The two compilers disagree about the convention:

**Pure-Simple compiler handles it** with an explicit rewrite table —
`src/compiler/80.driver/driver_source_loading.spl:801`:

```
mapped = _driver_resolve_rewritten_import(module_path, "app.package.registry", "app/package.registry", entry_dir)
```

with sibling entries for `app.game.breakout`, `app.game.rollball`, `cmm_lsp`.

**The Rust seed cannot.** Its module path is a plain per-segment join —
`interpreter_module/path_resolution.rs:624`:

```rust
let relative: PathBuf = parts.iter().collect();
```

Its only dot-joining is one level deep and anchored on the *current directory's
own name*, never on an accumulated pending prefix —
`path_resolution.rs:292-295`:

```rust
let dotted = format!("{}.{}", current_name, segment);
let dotted_dir = parent.join(&dotted);
if dotted_dir.exists() && dotted_dir.is_dir() {
```

(same shape at `module_resolver/resolution.rs:130-133` `find_dotted_dir`, and
`pipeline/module_loader.rs:41` `dotted_dir_from`.)

So from `current = src/app`, segment `package` only ever probes
`src/app.package/`. It never probes `src/app/package.registry/`, because that
requires joining **two pending segments** (`package` + `registry`) with a literal
dot. Error raised at `error_factory/resolve.rs:14` via `path_resolution.rs:593`
and `:1025`.

`app.ui.browser` resolves only incidentally: `src/app/ui/` also exists as a real
directory, so the walk lands on it and then dot-joins `browser`.
`src/app/package/` does not exist, so `app.package.registry.*` has no such path.

There is no allowlist, manifest, or `simple.sdn` entry gating dotted dirs in the
seed — resolution is pure filesystem probing. `__init__.spl` presence is
irrelevant to candidate generation (it only matters in `try_resolve_last_segment`,
`path_resolution.rs:157-198`).

## Blast radius

Every app importing `app.package.registry.*` is unusable under the seed:
`src/app/info/main.spl`, `src/app/search/main.spl`, `src/app/yank/main.spl`,
`src/app/publish/main.spl`, `src/app/search/render_adapter.spl`.

## Fix options

1. **Preferred — greedy candidate step in the seed resolver.** In
   `path_resolution.rs`, when a plain segment join misses, try joining 2+
   consecutive pending segments with a literal `.` against the current
   directory (`package` + `registry` -> `package.registry`), longest match
   first. This makes the seed agree with the pure-Simple driver for *all*
   dotted dirs, not just the four currently hardcoded there.
2. Mirror the pure-Simple rewrite table into the seed. Cheaper but keeps two
   hand-maintained lists in sync, which is how this drifted.
3. Rejected: renaming `src/app/package.registry/` -> `src/app/package/registry/`.
   It would fix the seed, but silently diverges the tree from the pure-Simple
   driver's hardcoded rewrite and reshapes a convention used by ~20 directories
   to accommodate a binary that is bootstrap-only by policy.

## Note

Moot for normal use once a pure-Simple self-hosted `bin/simple` is deployed
(CLAUDE.md: "Default tooling = pure-Simple self-hosted binary, not the Rust
seed"). It still matters because the seed is the bootstrap path, and a seed that
cannot load `src/app/**` limits what bootstrap can validate.

## Evidence

`scratchpad/agentlogs/tool_info.log`; full session context in
`scratchpad/tools_report.md`.
