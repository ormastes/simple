# Stage 3 stopped self-hosting: `--entry` / `--source` delegate the build to the Rust seed

- **Status:** FIXED (2026-08-04)
- **Severity:** critical — silently converted the self-host verification into a
  second Rust-seed build. Stage 3 reported success the entire time.
- **Component:** `scripts/bootstrap/bootstrap-from-scratch.sh`,
  `src/app/cli/bootstrap_main.spl`
- **Introduced by:** `f650e0fef2a` *fix(bootstrap): build stage3 through entry
  closure* (added `--entry`), compounded by a later commit that copied Stage 2's
  `--source src/compiler --source src/app --source src/lib --entry-closure`
  onto Stage 3.

## Mechanism

`run_native_build_bootstrap` in `src/app/cli/bootstrap_main.spl` has exactly two
routes:

1. **Pure-Simple in-process `CompilerDriver`** — reached ONLY by
   `native_build_single_spl_positional`, i.e. exactly one bare `.spl` positional
   **and no `--source`**. This branch seeds `SIMPLE_NATIVE_BUILD_ENTRY` and
   `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=0` itself, then runs the self-hosted
   driver.
2. **`run_rt_native_build` → `extern fn rt_native_build`** — the Rust seed
   (`src/compiler_rust/native_all/src/lib.rs`), linked into the stage binary by
   `llvm_native_link.spl` to backfill the seed-owned extern.

Route 2 is taken whenever:

- `--entry` is present and `SIMPLE_BOOTSTRAP_STAGE4 != "1"` (unconditional
  `return run_rt_native_build(args)`), **or**
- any `--source` is present, which makes `native_build_single_spl_positional`
  return `""` (it sets `has_source_input = 1`), so the positional branch is
  skipped.

The Stage 3 invocation had acquired **both**. `SIMPLE_BOOTSTRAP_STAGE4` is never
set for Stage 3, and `src/app/cli/bootstrap_main.spl` is not in the Stage 4
allowlist (`src/app/cli/main.spl`, `src/app/os/main.spl`) anyway — so even
setting it would have produced a hard error, not a self-host.

Before `f650e0fef2a` the Stage 3 argv was
`... -o "${stage3_bin}" src/app/cli/bootstrap_main.spl` with no `--source` and
no `--entry-closure` — route 1, a genuine self-host.

## Decisive evidence

**1. Recorded real Stage 3 run (2026-08-03, after `f650e0fef2a`).**
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
carries `argv:7:--entry` / `argv:30:src/app/cli/bootstrap_main.spl` and has no
`SIMPLE_BOOTSTRAP_STAGE4` in `explicit-env`.
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log` reads:

```
warning: unknown option '--low-memory', ignoring
Linked: .../stage3/x86_64-unknown-linux-gnu/simple (124862 KB) via clang++
Build complete: 724 compiled, 0 cached, 0 failed
```

`warning: unknown option '{}', ignoring` exists at exactly one place in the
tree: `src/compiler_rust/native_all/src/lib.rs:481`. `Build complete: {} compiled,
{} cached, {} failed` exists only at `src/compiler_rust/native_all/src/lib.rs:686`
and `src/compiler_rust/driver/src/cli/native_build.rs:557`. **No `.spl` emits
either.** The Rust seed compiled all 724 modules.

Note the symbol probe (`nm` for `rt_enum_check_discriminant`) is *not* decisive
here: `llvm_native_link.spl` links the seed library into every stage binary to
satisfy the `rt_native_build` extern, so that symbol is present regardless of
which compiler ran. The log strings above are the reliable oracle.

**2. Live A/B on the stage 2 compiler that built stage 3**
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`):

| shape | observed |
|---|---|
| `native-build ... -o out hello.spl` (bare positional, no `--source`) | `error: in-process native-build: AOT compile error in ...` → **pure-Simple driver** |
| `native-build ... --entry hello.spl -o out` | `note: --entry without --source scans the DEFAULT source roots ...` then hangs loading the whole project → **`run_rt_native_build`** |

## Fix

1. Stage 3 restored to the bare positional form in **both** the
   `stage3_build_args_sha256` fingerprint block and the real
   `bootstrap_stage3_run_transcribed` invocation: dropped `--entry`,
   `--entry-closure`, and the three `--source` flags. Stage 2 is untouched — it
   is a seed build by design (`SIMPLE_NATIVE_BUILD_RUST=1`) and keeps its
   `--entry`/`--source` form.
2. `f650e0fef2a`'s stated goal ("build stage3 through entry closure") is
   **preserved, not reverted**: the positional branch itself sets
   `SIMPLE_NATIVE_BUILD_ENTRY=<entry>` and `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=0`
   so the self-hosted `CompilerDriver` loads the entry's imports and then flips
   closure mode on. Entry-closure still happens — inside the self-hosted
   compiler, which is the whole point of Stage 3.
3. Added a **fail-closed provenance gate** after the Stage 3 build: if
   `stage3-native-build.log` contains `Build complete: N compiled` or
   `Linked: ... via clang`, the script errors out and exits 1. Any future
   re-introduction of the delegation now fails the bootstrap loudly instead of
   passing as a self-host.
4. Added a comment block above the Stage 3 invocation stating that `--entry`,
   `--entry-closure`, and `--source` must never be added there.

## Residual risk

The gate is a negative marker test. If `native_all`'s summary strings are ever
reworded the gate goes quiet. A stronger long-term fix is a positive marker: have
the pure-Simple in-process path print a `stage3: built in-process by <sha>` line
on success (it is currently silent on success) and gate on that instead.
