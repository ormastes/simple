---
paths:
  - "src/compiler_rust/**"
  - "scripts/bootstrap/**"
  - "build/bootstrap/**"
alwaysApply: false
---
# Bootstrap & Binary Architecture

## KNOWN BLOCKER (2026-08-06, check before redeploying): Stage 3 self-host fails

> **STATUS UPDATE 2026-08-18 — the ByteOrder blocker below is STALE
> (RESOLVED).** Re-probed under the current deployed seed (rebuilt 2026-08-18
> 06:12 with brace-escape + statx + env-cache fixes): the regression spec
> `test/01_unit/compiler/hir/hir_lazy_import_registration_flag_regression_spec.spl`
> is GREEN (`Results: 1 total, 1 passed, 0 failed`), and a minimal
> `use std.binary_io.{ByteOrder}` lazy-import probe resolves and runs clean
> under `bin/simple run` (see `scripts/check/check-bootstrap-preflight.shs`,
> which fences it). The BGS1 fix (`module_lowering.spl:952-955`) and the
> `Effect` facade collision fix are on main; a 2026-08-09 full bootstrap
> compiled all 803 Stage-2 files with 0 failures (125 MB non-vacuous binary).
> Per the bug doc's final update, the live bootstrap concern is no longer this
> error but output *vacuity* — verify the deployed binary by symbol
> count/banner, never exit code (see
> `stage3_vacuous_binary_is_enum_discriminant_garbage_not_a_link_failure_2026-08-08.md`,
> itself RESOLVED with fence
> `scripts/check/check-native-inprocess-positional-nonvacuous.shs`).
> **Run `sh scripts/check/check-bootstrap-preflight.shs` before any bootstrap.**
> The historical text below is kept for context only.

`bin/simple --version` right now prints the Rust-seed WARNING banner, and it
will keep doing so until this is fixed. `scripts/bootstrap/bootstrap-from-scratch.sh
--full-bootstrap --deploy` is the **correct, documented command** — it is not
broken and not missing — but it currently fails at Stage 3 (stage2 compiler
recompiling itself) with `unresolved type: ByteOrder` in `cache_validator.spl`,
then (once that's patched) an `Effect` facade collision in
`compiler.mir.__init__`. The wrapper correctly refuses to fall back to the
seed for the full CLI build, so **no redeploy will succeed until this Stage 3
defect is fixed in `src/compiler`** — this is a real compiler bug, not a
tooling/script gap. Full trace, root cause, and an in-progress fix:
`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
(see also `doc/08_tracking/bug/deployed_bin_simple_still_seed_2026-08-05.md`).

**Stage numbering (this doc undercounts it — see the authoritative 4-stage
definition in `doc/07_guide/compiler/build.md` § "Bootstrap Stages"):** Stage 3
("self-hosted") only proves the Stage-2 binary can recompile the *minimal
bootstrap entry* (`bootstrap_main.spl`) — it is NOT the full-featured CLI.
Stage 4 ("Full CLI") is the separate step where the verified Stage-3 binary
compiles `main.spl`, producing the actual deployable `bin/simple` with every
subcommand (`test`, `lint`, `duplicate-check`, etc.). A binary at
`build/bootstrap/stage3/<triple>/simple` correctly answers only `compile`/
`native-build` — it has no `run`/`test`/`duplicate-check`, and that is
expected, not a defect in that binary. Do not assume "Stage 3 passed" means
tooling is usable; it means only the recompile-itself milestone was hit. The
current KNOWN BLOCKER above is at Stage 3, so Stage 4 is unreachable until
it's fixed.

**Do not paper over this by hand-rolling `cargo build --release` and manually
copying the result to `bin/release/<triple>/simple`.** That produces a fresh
Rust **seed**, not a self-hosted binary — the seed banner is the tell. Worse,
the fresh mtime makes the binary *look* current/deployed to the next lane,
which is exactly how this recurs: multiple sessions in this shared working
tree have each independently done this ad hoc "fix" today alone, and each one
resets the clock on the next lane's binary-provenance check without fixing
anything. Before touching `bin/release/**` yourself: (1) run `bin/simple
--version` and check for the seed banner, (2) if seed, check the bug doc above
for current status before assuming it's a quick fix, (3) if you only need a
*working* binary right now and self-host is still blocked, run the seed
explicitly and consciously (`--seed-ok`/`SIMPLE_RUST_SEED_WARNING=0`) rather
than silently leaving a freshly-copied seed masquerading as `bin/simple`.

## Default tooling runs on pure-Simple, NOT the Rust seed
**Policy:** every tool — `test`, `lint`, `fmt`, `check`, `build`, `run`, `-c`,
the MCP/LSP servers, doc-coverage, etc. — must run on the **pure-Simple
self-hosted binary** (`bin/release/<triple>/simple`, built + deployed via
bootstrap). The Rust seed (`src/compiler_rust/target/bootstrap/simple`) is
**bootstrap-only** and must not be the day-to-day `bin/simple`.
- If the self-hosted binary has a **perf or robustness problem** (slow startup,
  high RSS, a crash, a wrong result), **fix it in pure-Simple** (`src/compiler`,
  `src/lib`, `src/app`) and re-deploy — do **not** fall back to the seed as the
  default. File a bug/feature request for anything that can't be fixed in place.
- Verify bug fixes with the **deployed pure-Simple test runner**, not the seed.
- Reverting `bin/simple` to the seed is an emergency stopgap only, never the
  resting state; record a bug when you do it.

| Binary | Path | Role |
|--------|------|------|
| **Real binary** | `bin/release/simple` (`.exe` on Windows) | Self-hosted production compiler — **default for all tools** |
| **Platform binaries** | `bin/release/<triple>/simple` | Per-platform release (this is what `bin/simple` should point at) |
| **Rust seed** | `src/compiler_rust/target/bootstrap/simple` | Bootstrap-only seed (NOT for day-to-day tooling) |

- **NEVER copy Rust bootstrap binary to `bin/release/simple`** — that's the self-hosted binary
- **Bootstrap entry points**: `src/app/cli/main.spl` (full CLI), `src/app/cli/bootstrap_main.spl` (minimal)
- **`bin/release/simple` is fully self-sufficient** — in-process compilation, no subprocess calls
- External tool calls: `clang`/`clang++`/`cl.exe`, `gcc`, `mold`/`lld`/`link.exe`, `llc`, `uname`/`cmd`, `which`/`where`

## Incremental: Rebuild Only Pure-Simple
Normal bootstrap is pure-Simple-only. It reuses the existing Rust seed/runtime
and does not run cargo, even when Rust source hashes changed:
```bash
scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload
```
- Reuses the existing `src/compiler_rust/target/bootstrap/simple` seed + runtime
  lib; **never runs cargo** unless `--full-bootstrap` is passed. Errors out if
  no seed exists yet.
- "If the Rust seed can build the changed pure-Simple" is enforced by Stage 2: the
  seed recompiles the changed `.spl`. If Stage 2 fails, the new pure-Simple needs
  a Rust feature the seed lacks — rerun with `--full-bootstrap`.
- Combine with `--deploy` to swap `bin/release/<triple>/simple` (same smoke gate).
- Pure-Simple build modes:
  - `dynload` (default): reuse `build/bootstrap/native_cache` unless compiler/AOP/loader
    inputs changed; native-build emits native plus SMF cache where supported.
  - `one-binary`: clear native cache and build the monolithic native executable.
- Dependency tracing intentionally over-invalidates around AOP/MDSOC weaving,
  loader ABI, interpreter adapters, execution mode, library path, and
  native-build environment knobs. Do not narrow this to import edges until the
  AOP and loader contracts expose stable cache keys.
- Direct Rust seed execution prints a `WARNING`; suppress it only for bootstrap
  automation (`SIMPLE_BOOTSTRAP=1`), explicit seed maintenance
  (`SIMPLE_RUST_SEED_WARNING=0`), or an acknowledged seed command
  (`--seed-ok` / `--rust-seed-ok`).
- Every bootstrap route that reaches the full server-producing stage must build
  the fresh MCP/LSP pair with `SIMPLE_NO_STUB_FALLBACK=1` and run the exact
  `initialize` -> `notifications/initialized` -> `tools/list` handshake plus
  `simple_status` and `lsp_symbols` before deploy. Earlier stages run their
  native fixture sanity; the separate Stage 2 MCP system spec covers its single
  cached MCP artifact but does not substitute for the Stage 5 pair gate.
- The bootstrap wrapper itself runs the shared compiler sanity before using
  Stage 2 and before accepting Stage 3: exact bootstrap version, unsupported
  `run` rejection, and strict native build/execute of `p2_add.spl`.
- Multiplatform bootstrap CI exercises both LLVM and Cranelift through that
  wrapper and uploads only the resulting pure-Simple Stage 2/Stage 3 binaries,
  never the Rust seed as a platform artifact. Note (2026-07-18): the LLVM
  stage-2 link currently fails with 62 undefined symbols (Windows CI runs that
  step continue-on-error); Cranelift is the working stage-2/3 path. See
  doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md.
- The Linux Stage 3 artifact owns the strict x86_64/AArch64/RISC-V LLVM
  execution gate through `check-llvm-simd-row-native-arch.shs`; Rust cross-build
  success alone is not pure-Simple architecture evidence.

## Verification tiering — match the gate to the change

The authoritative feature-development policy is
`doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md`. Start
with the smallest named target, provider, and SCI projection. A compiler source
path is not itself a bootstrap reason; escalate only when compatibility evidence
requires a stage rebuild. Full bootstrap requires a typed incompatibility or an
explicit release/trust target. Unknown compatibility rebuilds conservatively
and never authorizes reuse.

### Standalone product targets are not compiler bootstrap

Focused compiler/interpreter/loader work may use an explicitly admitted Stage
2 or Stage 3 Simple binary under the rules in
`doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md`. Record
path/hash/stage/provenance/commands, isolate output/cache, fail closed on an
unsupported command, and label the evidence by stage. Never substitute it for
Stage 4, general SPipe/docgen/test-runner, release, convergence, or cross-host
evidence, and never fall back silently to the Rust seed.

Office and other independently shipped target products must not rebuild the
compiler merely because their source changed. When a target can be compiled by
an existing admitted Phase 3 compiler, use a target-only wrapper with a stable
cache and output under `build/standalone/`, never `build/bootstrap/`. The
wrapper verifies Phase 3 provenance, records its digest, sets
`SIMPLE_NO_STUB_FALLBACK=1` and `SIMPLE_STRICT_FABRICATED_STUB_RATCHET=1`, and
fails closed when no admitted compiler is available. It must not silently
substitute the Rust seed or start Stage 1/2/3.

> **Prove the tier you think you're on — a cold cache is indistinguishable from
> a slow compiler.** Whenever you build incrementally, set
> `SIMPLE_NATIVE_INCREMENTAL=1`, pass a **stable** `--cache-dir`, and READ BACK
> the `[native-incremental] N reused / M rebuilt` receipt. No receipt, or `N=0`,
> means it was a cold full build regardless of intent.
>
> **The worktree trap (2026-07-27: four consecutive full rebuilds, ~4h, no
> binary).** A fresh `git worktree` gets its own EMPTY `build/`. A compiler
> rebuild driven from that worktree recompiles everything every time, while a
> warm cache (2,610 objects) sits unused in the main tree. Symptom: repeated
> `native-build worker timed out ... before producing a binary` at 180s, 7200s,
> and 5400s, across BOTH `llvm-lib` and `cranelift` — the backend swap changing
> nothing is the tell that the cost is upstream of codegen, exactly as that
> error message says ("loads the whole compiler + LLVM import graph BEFORE any
> codegen"). Before the first build in a worktree: symlink `build` to the main
> tree or copy `build/native_cache` in, then verify with
> `find <wt>/build/native_cache -name '*.o' | wc -l`.
>
> Two corollaries learned the same day:
> - **Read the whole error message before choosing a lever.** That timeout text
>   named the load phase AND offered "shrink `--source`"; swapping the codegen
>   backend was ruled out by the first half of the sentence, and cost 90 minutes
>   to disprove.
> - **`--source` is not pruned by `--entry-closure` before the loader walks it.**
>   `--source src/app` scans 2,465 `.spl` files across 206 app dirs; the
>   bootstrap entry needs `src/app/cli` (79 files). Point `--source` at the
>   narrowest directory containing your entry.

- **T0 — hosted seed probe (seconds).** Pure logic changes with no target/ABI
  dependence: run the affected `.spl` through the seed hosted (or `bin/simple`) and
  assert behavior. No kernel build. Cheapest; use it first whenever it can decide.
- **T1 — incremental kernel build (fast path).** Small pure-Simple **lib** change
  (a leaf function body, a string constant) that feeds the freestanding kernel.
  Build with a **stable** `--cache-dir` (do NOT wipe it between runs; a
  fresh/wiped cache dir is a cold build).
  - **Two different `native-build` pipelines exist and print different receipts
    — read the one you actually invoked.** Plain `bin/simple native-build`
    (no special flags) dispatches to the **pure-Simple driver**
    (`src/compiler/80.driver/driver_aot_native_output.spl`); its receipt is
    `[NATIVE] cache hit: <module>` (one line per reused module, silent on a
    miss). It is reached unconditionally — `SIMPLE_NATIVE_INCREMENTAL` is not
    read anywhere in `src/compiler/**` or `src/app/**` and has **no effect**
    on this path. Its cache key hashes the **entire loaded source closure**
    into `cache_scope_root`, so an unchanged rebuild reuses every module but
    editing **any one file** changes the whole scope directory and drops
    reuse to **0** for every module, not just the changed one (confirmed by
    direct fixture measurement 2026-08-08: 3/3 reused unchanged, 0/3 reused
    after a one-line edit to one of three modules — see
    `doc/03_plan/compiler/bootstrap/stage3_native_cache_incrementality_2026-08-07.md`
    "Layer 2"). This is a **deliberate, sound-but-coarse** tradeoff, not a bug:
    the scope directory always changes on any content change, so a stale
    object is never served, but a one-file edit currently buys nothing.
  - The Rust seed's **`native_project` pipeline**
    (`src/compiler_rust/compiler/src/pipeline/native_project`) has real
    per-module hardened-key reuse (folds opt-level, entry-closure flag,
    target, linker-script, and the closure's cross-module struct/enum/
    signature layout into the key — a leaf edit never ships a stale wrong
    binary) and prints `[native-incremental] N reused / M rebuilt`. This
    correctness key is **unconditional** whenever the object cache is live —
    it is NOT gated by `SIMPLE_NATIVE_INCREMENTAL`; that env var (and
    `NativeBuildConfig.incremental_hardening`) now controls only whether the
    receipt line is printed. `incremental` itself defaults to `true`
    (opt-out via `--no-incremental`). **But this pipeline is only reached via
    `SIMPLE_NATIVE_BUILD_RUST=1` or a cross-target executable build**
    (`native_build_wants_cross_target` in `driver/src/main.rs`) — routing
    ordinary `native-build` through it would mean falling back to the Rust
    handler, which conflicts with this repo's pure-Simple-default policy
    above, so it is not a drop-in replacement for the default path.
  - Reuse (either pipeline) requires the **same producer binary**: rebuilding
    the seed/compiler changes the fingerprint and invalidates every cached
    object (by design).
- **T2 — full kernel rebuild.** Any big/structural change: new modules, trait/type
  layout changes, entry-closure set changes, linker-script or flag/target/opt-level
  changes. (Under T1 these auto-trigger a full rebuild anyway; run T2 directly when
  you know the change is structural.)
- **T3 — full bootstrap.** Only for a typed bootstrap incompatibility or an
  explicit self-host convergence, release-trust, or DDC target. A change under
  `src/compiler_rust` or `src/compiler` is insufficient by itself; rebuild the
  smallest provider, consumer set, or compiler stage selected by compatibility
  evidence.

**Follow-up (not yet done):** `SIMPLE_NATIVE_INCREMENTAL` safe per-module reuse is
implemented only in the Rust seed's native-build pipeline
(`src/compiler_rust/compiler/src/pipeline/native_project`). The pure-Simple
self-hosted native-build path (`src/compiler/70.backend`, `src/compiler/80.driver`)
should gain the same hardened-key incremental reuse for parity once the seed path
has soaked. Reaching the <20s kernel-rebuild goal additionally needs incremental
**link** and cached entry-closure **discovery/import-map** — the two phases the
object cache does not touch (they dominate kernel build wall time).

## Bootstrap Commands
```bash
# Normal pure-Simple bootstrap:
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# Full Rust + pure-Simple bootstrap:
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy

# Windows:
scripts/bootstrap/bootstrap-from-scratch.sh windows-entry --deploy
# Manual full-bootstrap seed/runtime rebuild:
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap

# Internal stage replay after a full-bootstrap seed exists:
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry src/app/cli/bootstrap_main.spl -o build/bootstrap/stage2/<triple>/simple
```

## Redeploy #79 Key Findings (2026-07-11)

**Parse-Error Gate False Positives:** The phase-2 parse-error gate (checking
`par_had_error` flag) is structurally correct but currently false-positives on
speculative/fragment re-lex errors. Known open bug; fix in flight. Gate behavior
is sound for deployed binaries but may cause spurious bootstrap failures during
stage2 diagnosis.

**Driver Import Pattern:** `use lazy` dynload for the compiler driver was never
implemented. Bootstrap now imports `compiler.driver.driver` directly in
`bootstrap_main.spl`. If changing driver initialization, verify direct imports
still resolve.

**Native-Build Closure Discovery:** The native-build recursive dependency
tracer follows plain `use` imports but does NOT traverse `export use` shims.
Only direct imports trigger cascading closure collection. Plan closure manually
for re-exports if needed.

**Runtime Path Requirement:** `SIMPLE_RUNTIME_PATH` env var MUST point at the
seed target directory for hosted linking. The `--runtime-path` CLI flag alone
does not set it. Ensure the wrapper sets both when invoking native-build in
hosted mode (e.g., `SIMPLE_RUNTIME_PATH="$seed_target" bin/simple native-build`).

See `.claude/memory/ref_architecture.md` for detailed architecture.

## Seed-sibling refresh (2026-08-18) — distinct from a self-hosted redeploy

The "do not hand-roll `cargo build --release`" warning above is about faking a
SELF-HOSTED redeploy. Refreshing the deployed RUST SEED binary with a seed-side
fix is legitimate and was done twice on 2026-08-18 (brace-escape lexer fix,
cleanup_old_logs statx fix): `cd src/compiler_rust && CARGO_TARGET_DIR=<warm>
cargo build --release --bin simple`, verify the fix on the fresh binary, then
deploy `cp <bin> bin/release/<triple>/simple.new && mv ... simple` (never plain
cp — Text file busy). Always record binary identity (size/mtime) and rerun a
spec proving the fix on the DEPLOYED path. This does not change that default
tooling should ultimately be the pure-Simple self-hosted binary.
