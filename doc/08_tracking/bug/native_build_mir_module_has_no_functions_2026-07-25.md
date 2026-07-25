# BUG: `native-build` fails with "MIR module has no functions" for extern/return-typed probes

**Status:** OPEN — blocks verification of the Stage4 deep-free chain
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
| `fn main(): print "hi"` | **rc=0**, prints `hi` |
| `extern fn rt_heap_registry_count() -> i64` + `fn main() -> i64` + `val` | rc=1, no functions |
| externs + `fn main() -> i64` + `var`/loops | rc=1, no functions |

## Next step — discriminate before bisecting

Two single-variable probes are checked in under `probes/freeprobe/`:
- `varA.spl` — `fn main() -> i64` and NO extern (isolates the return type)
- `varB.spl` — a module-level `extern fn` and `fn main()` with NO return type
  (isolates the extern declaration)

Run both with the flags above. Whichever fails localises the defect. Only if
BOTH pass should the seed be bisected, reverting these in order and rebuilding
between each: `runtime_sffi.rs` (`RuntimeFuncSpec`), `elf_utils.rs`,
`interpreter_extern/{mod,sffi_string}.rs`, `runtime/src/value/mod.rs`.

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
