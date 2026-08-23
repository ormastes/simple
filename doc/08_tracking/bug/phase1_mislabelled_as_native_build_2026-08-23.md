# "Phase 1" mislabelled as a native-build — ~26 unusable runs (2026-08-23)

**Status:** recorded, prevention landed (`scripts/check/check-sanctioned-bootstrap-invocation.shs`)
**Class:** process / terminology defect. No compiler bug. No build-behaviour change in this commit.

## What was believed

That "phase 1" of the bootstrap is a native-build of the Simple compiler, and
that it could be exercised by hand with a short command such as:

```sh
# WRONG — this is not any bootstrap stage
simple native-build --source src/app --entry-closure \
  --entry src/app/cli/bootstrap_main.spl
```

labelled "phase 1", and that `--strategy=adhoc` selects a lighter/partial build.

## What is true

**Phase 1 is the Rust seed, and it is built by cargo, not by native-build.**

- `scripts/bootstrap/bootstrap-from-scratch.sh:1393` —
  `seed_bin="src/compiler_rust/target/bootstrap/simple${exe_suffix}"`.
- It is produced by `run_rust_authority_cargo rust-seed-build default build
  --locked --offline --manifest-path src/compiler_rust/Cargo.toml --profile
  bootstrap ...` (`bootstrap-from-scratch.sh:1772-1775`). Note the profile is
  `bootstrap`, **not** `--release`.
- That seed binary is then *preserved* as the phase-1 lineage artifact at
  `bootstrap-from-scratch.sh:2117`:
  `sh "${repo_root}/scripts/bootstrap/preserve-phase-binary.shs" "${seed_bin}" phase1`.
- **The first native-build in the whole bootstrap is Stage 2**, at
  `bootstrap-from-scratch.sh:2254-2275`.

So a native-build command can never be "phase 1". Phase 1 succeeds routinely
(~4m18s measured on this host) because it is a cargo build.

### The sanctioned Stage-2 invocation, verbatim

From `scripts/bootstrap/bootstrap-from-scratch.sh:2254-2275`:

```sh
    RUST_LOG="${stage_build_rust_log}" \
    LIBRARY_PATH="${bootstrap_link_library_path}" \
    SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256="${bootstrap_link_compat_sha256}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_NATIVE_BUILD_RUST=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    SIMPLE_BINARY="${stage2_seed_absolute}" -- \
    "${stage2_seed_absolute}" native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle core-c-bootstrap \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
    --threads "${jobs}" \
    ${native_verbose_arg} \
    --cache-dir "${stage2_cache_absolute}" \
    --mode "${bootstrap_mode}" \
    --entry src/app/cli/bootstrap_main.spl \
    --runtime-path "${stage_runtime_absolute}" \
    -o "${stage2_bin}"
```

The hand-typed command carried **one** of those `--source` roots, and none of
`--backend`, `--target`, `--runtime-bundle`, `--runtime-path`, `--mode`,
`--cache-dir`, `--threads`, nor any of the four `SIMPLE_*` env vars.

## The wasted effort

~26 runs over 2026-08-22/23 were driven by the hand-typed line and labelled
"phase 1". Two distinct consequences, both of which cost hours:

### A. The cache was inert

`SIMPLE_CACHE_SCOPE=runNN` was exported, but with **no `--cache-dir` on the
command line** there is nothing for the scope to partition, so a hit is
impossible. A 23,718-line run log contains **zero** cache-hit lines. Hours were
spent "warming" a cache that could never hit. (Scope partitioning is a
subdirectory of the cache dir — see `.claude/rules/commands.md`, per-lane private
caches; no cache dir, no scope, no hit.)

### B. A livelock was misread as slowness

Parse ran healthy at ~0.6 s/module to 389/688 modules in 231s, then **froze**:
the module counter did not advance for 2,700s while
`src/compiler/types/dim_constraints.spl` and
`src/compiler/semantics/narrowing.spl` re-emitted at dt=11-14s each, and
`module_surface_registry_index.spl` was parsed **73 times**.

A frozen counter at high CPU is a **livelock** (repeated re-entry into the same
work), not an O(n²) throughput problem. The two have opposite fixes: a livelock
needs a visited-set / memo / cycle break, while an O(n²) needs algorithmic or
data-structure work. Chasing the wrong one is how the time went.

The likely reason the shape appeared at all: without `--source src/compiler
--source src/lib` the closure walker had to discover those trees through import
edges alone, from a single `--source src/app` root.

### C. `--strategy=adhoc` is not a lighter build

`scripts/bootstrap/bootstrap-cache-policy.shs:22` is the whole of it:

```sh
    adhoc) printf '%s\n' fail-fast ;;
```

`adhoc` selects only a **failure policy** (`fail-fast`, versus `phase-isolated`
for `normal` and `inventory-to-end` for `full`). It changes nothing about what
is compiled. **There is no reduced-closure stage-1 path anywhere in the repo.**
Reading "adhoc bootstrap" as "a quicker partial build" is simply wrong.

## Corrected mental model

| phase | artifact | how it is produced | native-build? |
|---|---|---|---|
| 0 | toolchain / preflight | `scripts/setup/setup.shs` | no |
| **1** | **Rust seed** `src/compiler_rust/target/bootstrap/simple` | **cargo, `--profile bootstrap`** | **no** |
| **2** | `stage2/<platform>/simple` | **seed runs `native-build`** — the FIRST native-build | **yes** |
| 3 | `stage3/simple` (+ per-triple) | stage2 binary runs `native-build` | yes |
| 4 | full CLI / release deploy | stage3 artifacts installed | — |

Full table with gates: `doc/07_guide/tooling/bootstrap_phase_verification.md`.

## Rules that follow

1. **Never hand-type a bootstrap stage's native-build line.** Run
   `sh scripts/bootstrap/bootstrap-from-scratch.sh`. It is the only sanctioned
   path; every flag above is load-bearing and the script keeps them consistent
   with the stage's env, cache scope, runtime authority and provenance snapshots.
2. **Never call a native-build "phase 1".** If a run is doing a native-build it
   is Stage 2 or later, by definition.
3. **A frozen progress counter is a livelock, not slowness.** Before optimising,
   check whether the same module is being re-processed; `module_surface_registry_index.spl`
   × 73 is the diagnostic signature.
4. **`SIMPLE_CACHE_SCOPE` without `--cache-dir` is a no-op.** If a log has zero
   cache-hit lines, stop and check the invocation before warming anything.

## Prevention

`scripts/check/check-sanctioned-bootstrap-invocation.shs` — scans tracked
scripts/docs for bootstrap-stage `native-build` invocations that omit the
mandatory flags (`--runtime-bundle`, `--cache-dir`, `--runtime-path`, `--mode`,
`--backend`, `--target`, and all three `--source` roots), with a fatal
`--selftest` whose must-FAIL fixture replays the exact hand-typed line above.

## Corrections to the original report

Three file:line references in the initiating report were wrong and are corrected
here (verified against `origin/main` @ `f16c2a4736a`):

| claimed | actual |
|---|---|
| seed preserved as phase-1 at `:2035` | `:2117` (seed_bin defined at `:1393`) |
| Stage-2 native-build at `:2181-2196` | `:2254-2275` |
| seed built by `cargo build --release` | `cargo build --locked --offline --profile bootstrap` (`:1772-1775`) |

`bootstrap-cache-policy.shs:22` was correct as stated.

## Addendum — why people hand-roll the command (found 2026-08-23, same day)

Running the script bare fails before Stage 1 with `bootstrap-policy-error:
reason-receipt-required` and **exit 64** (`bootstrap-from-scratch.sh:466-483`):
a staged bootstrap needs a planner-issued receipt. The single trust-root
exception (`:468-475`) requires `--stop-after-stage2` **and** `--full-bootstrap`
together. The working line, verified against a live lane run:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --strategy=adhoc --full-bootstrap --stop-after-stage2 --output=<dir>
```

This matters to this record specifically: "just run the script" plus an
unexplained exit 64 is exactly the pressure that produces a hand-rolled
`native-build` line. `--strategy=adhoc` is a normal sanctioned flag here — still
only a failure policy, still not a lighter build.

Flag-resolution note: the verbatim Stage-2 block above passes `--mode
"${bootstrap_mode}"`, which defaults to **`dynload`** (`:277`, overridable via
`SIMPLE_BOOTSTRAP_MODE`), and `--backend "${backend}"` resolves to `llvm`. An
earlier paraphrase of this incident said `--mode one-binary`; that is wrong — the
script is the authority, not the paraphrase.

**Line-number convention:** all `bootstrap-from-scratch.sh:N` refs in this
document are **as of this commit**, i.e. after the 29-line warning header this
change prepends. Subtract 29 to locate them in `f16c2a4736a`.
