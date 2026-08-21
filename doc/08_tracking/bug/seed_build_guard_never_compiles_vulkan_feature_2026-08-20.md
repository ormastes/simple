# Seed-build guard never compiles `--features vulkan`, so cfg-gated code rots unseen

- **Filed:** 2026-08-20
- **Status:** RESOLVED (2026-08-21)
- **Severity:** P2 — fail-open guard; silently admits non-compiling cfg-gated code
- **Area:** infra / pre-push guards, GPU runtime

## Symptom

`src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs` and
`..._shader.rs` carried stray unconditional trailing `use` lines duplicating
imports that were already cfg-gated. That is **4 pre-existing E0252 errors**
(`the name ... is defined multiple times`), which made *any*
`cargo check -p simple-runtime --features vulkan` fail outright.

The code had therefore never compiled under that feature, and `main` looked
green the whole time.

## Why every existing guard missed it

`scripts/check/check-seed-builds-push.shs` is the guard that exists precisely
to catch "structurally clean tree that does not compile". Its gating legs are:

```
GATING  cargo check --release --bin simple
GATING  cargo check --release --tests
```

Both run with **default features**. Nothing in the push path ever passes
`--features vulkan`, so every `#[cfg(feature = "vulkan")]` body is invisible to
it — cfg-gated code is not type-checked unless the cfg is enabled.

The `--features vulkan` string does appear in
`scripts/check/check-engine2d-vulkan-*.shs` and
`check-simpleos-qemu-host-gpu-2d.shs`, but those are **runtime/device gates**,
not compile gates, and they are device-blocked on hosts with no GPU — i.e. they
never run here, and would not have been reached even if they did.

This is the same fail-open shape already documented for the old path-filter in
`origin_main_unbuildable_missing_half_1e40de916bb_2026-08-18.md`: an absence of
evidence laundered into a green verdict.

## Fixed incidentally, cause not fixed

The 4 E0252s were repaired while implementing non-blocking Vulkan submit (see
`vulkan_submit_and_wait_fence_blocks_unconditionally_no_nonblocking_submit_2026-08-07.md`)
by gating the stray imports `#[cfg(not(feature = "vulkan"))]`. Verified with
`cargo check --release -p simple-runtime --features vulkan` — Finished, no
errors; it did not compile at all before.

**The guard gap itself is untouched.** Nothing prevents the next cfg-gated
regression from landing exactly the same way.

## Proposed fix

Add a gating leg to `check-seed-builds-push.shs`:

```
GATING  cargo check --release -p simple-runtime --features vulkan
```

`cargo check` (not `build`) keeps this cheap and needs no GPU, Vulkan SDK
loader, or device — it is pure type-checking, which is exactly what was
missing. Fold the feature set into the guard's content digest so the existing
marker-based fast path still applies.

Consider the same treatment for any other feature flag guarding a non-trivial
body (audit `Cargo.toml` `[features]` for the full list) — a per-feature
`cargo check` matrix is the general form.

Add a `--selftest` fixture replaying this incident: a crate with a duplicate
`use` inside a `#[cfg(feature = "x")]` body must FAIL the guard, and must pass
a default-features-only check, proving the new leg is load-bearing rather than
decorative.

## Resolution (2026-08-21)

`scripts/check/check-seed-builds-push.shs` gained **GATING LEG 3**:

```
GATING  cargo check --release -p simple-runtime --features vulkan
```

placed after the `--tests` leg and before the advisory `--all-targets` leg,
with the same fail-loud shape (diagnostic block on stderr, `FAIL — cargo check
--features vulkan failed in <sha>: <first error>`, exit 1). Needs no GPU,
Vulkan loader or device — it is pure type-checking, which is exactly the thing
that was missing.

**Marker fast path made honest.** The green-marker digest recipe tag was bumped
`seed/v1` -> `seed/v2+vulkan`. Without this, every tree already recorded green
under the weaker recipe would skip the new leg forever, and the fast path would
launder the exact fail-open the leg exists to close. The tag must be bumped
whenever a leg is added or a selector changes.

**Selftest fixture F** (`SELFTEST_EXPECTED` 5 -> 6) replays the incident: a
crate with `[features] gfx`, a `#[cfg(feature = "gfx")]` module carrying a
stray unconditional duplicate `use`. Both halves are asserted — the
default-features `cargo check` must **PASS** (this is what proves the leg is
load-bearing rather than decorative; a fixture failing both ways would
demonstrate nothing about cfg scope) and `--features gfx` must **FAIL** with
`E0252` / `defined multiple times`. Measured:
`selftest 6/6 fixtures correct (... cfg-gap: default-features PASS + --features FAIL with E0252)`.

**Leg proven green before gating:**
`cargo check --release -p simple-runtime --features vulkan` -> `Finished
release profile ... in 40.52s`, 2 warnings, 0 errors (2026-08-21, warm).

**Deliberately not gated:** `llvm`, `wasm*`, `pytorch`, `cuda`, `monoio-*`,
`ratatui-tui`, `tui`, `gui`, and the compiler crate's own `vulkan`/`vulkan-*`.
None has been proven green on this host, and gating on an unproven-red
condition gets routed around with `--no-verify`, which protects nothing. The
general form is a per-feature matrix; add each leg as it is proven green, and
bump the recipe tag with it.
