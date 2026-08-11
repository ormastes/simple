# BUG: `native-build` fails with "MIR module has no functions" for extern/return-typed probes

**Status:** ALREADY-FIXED (re-verified 2026-08-10 — see re-verification section at end)
**Found:** 2026-07-25
**Blocks:** `doc/09_report/stage4_deepfree_chain_status_2026-07-25.md` step 5
(reclamation measurement), which blocks Stage4 memory work → redeploy → RISC-V
FPGA goal AC-1..AC-12.

## Symptom

```
error: AOT compile error in probes.freeprobe.free_probe: MIR module has no functions
error: native-build worker exited with code 1
  interpreter: src/compiler_rust/target/debug/simple (exit code 1)
```

Command (all flags required; omitting any causes an unrelated bogus timeout):

```
src/compiler_rust/target/debug/simple native-build <file>.spl \
  --runtime-bundle core-c-bootstrap --mode one-binary --entry-closure \
  --cache-dir <fresh dir> -o <out>
```

## What is established

- **Not a general native-build outage.** `fn main(): print "hi"` builds and runs
  (`rc=0`, prints `hi`) on the same seed, same flags.
- **Not caused by the new `rt_string_free` symbol.** A control probe that never
  mentions it fails identically.
- **Not the environment / not a stale worktree.** Reproduces in the main repo on
  a freshly built seed. Two earlier agent reports dismissed this exact signature
  as "a pre-existing environmental regression in this worktree" — that
  attribution is WRONG and should not be repeated.
- **Seed is otherwise healthy.** `simple run` on a trivial file prints `ok`; the
  interpreter lane resolves externs with no dispatch error.
- **It is a regression against the older seed.** The identical probe file built
  and ran clean (`BUILD_RC=0`) on the 06:43 seed; it fails on the rebuilt one.
- **`CORE_REQUIRED` was NOT the cause.** Adding `rt_string_free` to
  `CORE_REQUIRED_RUNTIME_SYMBOLS` was a genuine bug, reverted in `34c40a95b28`
  (the freestanding `simple_core` archive does not define it, so
  `find_abi_complete_simple_core_runtime_library()` returned `None`) — but
  removing it did **not** fix this failure. That commit message overstates its
  effect.

## Failing vs passing inputs

| input | result |
|---|---|
| `triv.spl` — `fn main(): print "hi"` | **rc=0**, prints `hi` |
| `varA.spl` — `fn main() -> i64`, NO extern | **rc=0**, prints `A` |
| `varB.spl` — module-level `extern fn`, main with no return type | **rc=1, no functions** |
| `ctrl_probe.spl` — extern + `fn main() -> i64` + `val` | rc=1, no functions |
| `free_probe.spl` — externs + `fn main() -> i64` + `var`/loops | rc=1, no functions |

## BLAST RADIUS IS WIDER THAN FIRST FILED — module-level `val` triggers it too

A second, independent investigation reproduced the same failure with **no
extern at all**. A module-level `val` is sufficient, *even when never
referenced*:

| fixture | source | rc |
|---|---|---|
| `triv` | `fn main(): print(5)` | **0** |
| `valunref` | `val BASE: i64 = 5` + `fn main(): print(5)` — val NEVER referenced | **1** |
| `ctl` | `val BASE: i64 = 5` + `fn main(): print(BASE)` | **1** |
| `imp` | `use owner.{BASE}` | **1** |
| `fnw` | accessor-function workaround | **1** |
| `scripts/check/check-seed-native-build-invariant.shs` | the repo's own gate | **1** |

So the trigger is not specifically `extern fn` — it is a module-level ITEM
(extern or `val`) alongside `main`. The unreferenced case is the sharpest clue:
nothing *uses* the item, so this is about how module-level items are collected,
not about resolving a reference to one.

This also means **the repo's own seed native-build gate cannot pass right now**,
and any `.spl` module with a module-level `val` or `extern` is affected — far
beyond the deep-free work that surfaced it.

### RETRACTED: the `_skip_dirs` "harness trap" — my claim was WRONG

An earlier revision of this document (and its commit message) claimed that
`_skip_dirs` at `driver_source_loading.spl:24` excludes `scripts/` and `build/`
from compilation, and therefore that the seed gate's fixture "cannot work where
it lives". **That is false. Do not act on it. Do not relocate the fixture.**

Disproof, static and empirical:

- `_skip_dirs` feeds only `_driver_should_skip_dir` (`driver_source_loading.spl:29`),
  which has **no live caller** — `driver.spl:71` imports the name but never
  calls it. A second copy at `driver_helpers.spl:77` *is* called (line 115), but
  `driver_helpers.spl` is imported by **nothing** (orphan), so that path is
  unreachable too.
- The LIVE collector `_driver_collect_sources` filters on substrings
  `/test/ /tests/ /testdata/ /doc/ /verification/` **only** (lines 689, 715,
  750). `scripts`, `build`, `docs`, `resources` are NOT among them.
- Empirical A/B, identical minimal fixture, same flags, fresh cache each:
  under `probes/` → `undefined symbol: __simple_main`; under
  `scripts/check/cert/redeploy_gate/fixtures/` → **identical** error.
- Positive control: a single-file fixture *under `scripts/`* builds `rc=0` and
  prints `5`. Files under `scripts/` compile fine.
- The gate's own failure names the module
  `...simple.scripts.check.cert.redeploy_gate.fixtures.seed_cross_module.owner`,
  which is itself proof the fixture under `scripts/` WAS read, parsed, and
  reached AOT.

Lesson: reading a `val` list is not evidence it is wired. Check for live callers
before filing a "silently excludes" claim.

### SECOND, INDEPENDENT BLOCKER — fixing this bug will NOT make the gate pass

A fixture with **no module-level globals at all** still fails:

| invocation | failure |
|---|---|
| `--source` + `--entry` | `ld.lld: error: undefined symbol: __simple_main` |
| positional entry | `native-build produced no code-bearing MIR modules` |

So the seed native-build gate is blocked by **two** distinct defects: the
module-level-item bug documented here, and this multi-module `__simple_main`
failure. Both must be fixed before the gate can pass on a good seed — which is
still only half its contract.

## FIRST ISOLATION: a module-level `extern fn` declaration

Single-variable result. A return-typed `main` is RULED OUT (`varA` passes);
adding nothing but an `extern fn` at module scope makes the build fail:

```
extern fn rt_heap_registry_count() -> i64   # <-- remove this line and it builds

fn main():
    print "B"
```

Two consequences worth stating:

1. **This is not about `rt_string_free`.** `varB` declares
   `rt_heap_registry_count`, a long-pre-existing extern. Any module-level extern
   appears to trigger it, so the blast radius is much wider than the deep-free
   work — it plausibly affects any `.spl` module that declares an extern and is
   built with `--entry-closure`.
2. It is still a regression against the older seed: `free_probe.spl`, which
   declares externs, built and ran clean (`BUILD_RC=0`) on the 06:43 seed.

**Where to look first:** how extern declarations are collected into a module's
MIR function list. A module whose items are externs plus `main` ends up with
zero MIR functions, which suggests externs are either displacing real functions
in that list or causing the collection to bail early. Note the seed edits in
`d479d1a4302` touched exactly the extern registration surface
(`runtime_sffi.rs` `RuntimeFuncSpec`, `elf_utils.rs`,
`interpreter_extern/{mod,sffi_string}.rs`, `runtime/src/value/mod.rs`), so start
by reverting those one at a time and rebuilding between each — `runtime_sffi.rs`
first, since a `RuntimeFuncSpec` entry is the change most likely to alter how
externs are enumerated.

Fast repro loop (~1 build): `varB.spl` vs `triv.spl`. Do NOT use `free_probe.spl`
for bisecting — it is slower and has extra variables.

Also rule out working-copy `src/compiler/**` edits from parallel sessions
(`cuda_backend.spl`, `contracts.spl` were dirty at the time) and the
uncommitted `driver_types.spl` change — native-build compiles `.spl` from the
working tree, so a dirty tree is part of the input.

## Diagnostic traps hit while narrowing this

- `tail -N` on the build log **hides the real error**: the useful line was 13
  lines in, buried under ~350 lines of `gc-warning`. Use a persistent
  `--cache-dir` and grep the whole log.
- `--runtime-bundle core-c-bootstrap` stages the **Rust** `libsimple_runtime.a`,
  not `src/runtime/runtime_native.c`, and `cargo build -p simple-runtime`
  refreshes only `target/debug` while that lane links the **bootstrap** profile.

## Re-verification 2026-08-10 — ALREADY-FIXED

Re-ran the exact `varB.spl` isolation fixture from this doc (module-level
`extern fn rt_heap_registry_count() -> i64` + `fn main(): print "B"`) with the
exact documented flags, against the current
`src/compiler_rust/target/debug/simple` (dated 2026-08-09):

```
$ src/compiler_rust/target/debug/simple native-build /tmp/nbmirprobe/varB.spl \
    --runtime-bundle core-c-bootstrap --mode one-binary --entry-closure \
    --cache-dir <fresh> -o /tmp/nbmirprobe/out2
# exit 0, no "MIR module has no functions" error
$ /tmp/nbmirprobe/out2
B
# exit 0
```

Also ran the repo's own gate mentioned in this doc:

```
$ sh scripts/check/check-seed-native-build-invariant.shs
PASS  seed-native-build-invariant  seed=.../simple native-built + ran the
cross-module fixture, printed 5
```

Both the module-level-extern isolation case and the repo's own seed
native-build gate now pass cleanly — no code change made this session; the
fix already landed in the Rust seed sometime between 2026-07-25 and
2026-08-09 (no specific commit identified; `git log` on this doc shows only
doc/chore syncs, so the fix landed as part of ordinary seed work without a
doc update). Marking ALREADY-FIXED and closing.
