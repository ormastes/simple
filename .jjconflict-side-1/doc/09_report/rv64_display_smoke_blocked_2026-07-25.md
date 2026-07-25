# RV64 Display-Smoke QMP Evidence

- contract_version: 2
- status: fail
- reason: no-runnable-pure-simple-compiler
- elf: build/os/simpleos_riscv64_display_smoke.elf
- serial_log: (not produced — QEMU never launched)
- scanout_ppm: (not produced)
- scanout_raw: (not produced)
- ready: 0
- lifecycle_markers: 0
- width: 0
- height: 0
- stride: 0
- present_revision: 0
- scanout_address: 0
- scanout_bpp: 0
- scanout_format:
- scanout_generation: 0
- scanout_scene_revision: 0
- scanout_capture_size: 0
- scanout_capture_origin: qemu-pmemsave
- nonblack: 0
- canonical_palette_witnesses: 0
- canonical_palette_names:
- wm_font_input_mode: 0
- wm_font_input_contract_version: 1

## Verdict (retry, after coordinator's dash `test -s /dev/stdin` fix landed)

BLOCKED. Not a display/rendering FAIL — the ELF still was never produced,
QEMU was never launched, no QMP scanout capture was attempted. This report
makes no scanout claim, real or zero-as-pass.

## Retry status: media-phase gate PASSED, build now blocked one phase further

1. Confirmed the coordinator's fix is present:
   `grep -c 'test -s /dev/stdin' src/os/_QemuRunner/scenario_exec.spl` → `0`.
   Both sites now use `mtype ... | grep -qa .`, matching the idiom already
   used at lines 85-88 of that file.
2. Re-ran `bin/simple os build --scenario=riscv64-display-smoke` with the
   `~/.local/bin` mtools symlinks from the first pass still in place (kept,
   per instructions, as an environment dependency note rather than a repo
   change). Result: the media/font-projection gate that failed 3/3 times
   last round now **passes** —
   `[ensure_riscv64_desktop_disk_image]` no longer prints "desktop font
   projection is incomplete"; the build advances past `phase=media` into
   `phase=build`.
3. The build then fails at a **new, later, unrelated phase**:
   ```
   [scenario][riscv64-display-smoke] phase=build target=build/os/simpleos_riscv64_display_smoke.elf
   [build][riscv64] phase=tooling FAILED: no runnable pure-Simple compiler
   [scenario][riscv64-display-smoke] phase=build FAILED target=build/os/simpleos_riscv64_display_smoke.elf
   ```

## Root cause of the new blocker (pre-existing, already tracked — not introduced by this session)

`no runnable pure-Simple compiler` comes from `_find_simple_binary_for_target()`
in `src/os/_QemuRunner/os_build_run.spl`, which requires every candidate binary
(`release/x86_64-unknown-linux-gnu/simple`, `bin/simple`, ...) to pass
`_simple_binary_is_valid()` → `_candidate_frontend_smoke()`: a real
`native-build --backend cranelift --runtime-bundle core-c-bootstrap --mode
one-binary` of the fixture `scripts/check/cert/redeploy_gate/fixtures/p2_add.spl`,
then running the produced binary and checking it prints `5`.

Reproduced directly, deterministically (2/2 tries), independent of the RV64
scenario:

```
$ release/x86_64-unknown-linux-gnu/simple native-build --backend cranelift \
    --runtime-bundle core-c-bootstrap --entry-closure \
    --entry scripts/check/cert/redeploy_gate/fixtures/p2_add.spl \
    --cache-dir <tmp>/cache --mode one-binary --output <tmp>/p2_add
Segmentation fault (exit 139)
```

GDB backtrace:
```
SIGSEGV in __strlen_avx2
  <- __add_to_environ(name="SIMPLE_OS_LOG_MODE", value=0x12 <invalid>, ...)
  <- rt_env_set
  <- io.cli_ops.env_set
  <- io___CliCompile__compile_targets__cli_native_build
  <- cli___CliMain__main_and_help__main
  <- spl_main -> main
```

This is not a bug I found fresh — it is the exact, already-filed defect in
`doc/08_tracking/bug/deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`:
the tracked `release/x86_64-unknown-linux-gnu/simple` artifact (unchanged
SHA-256 lineage since 2026-07-14, last reconfirmed still-broken 2026-07-23)
has a **stale two-argument `rt_env_set` ABI linked in**, while current source
(`runtime_native.c`, callers) uses the four-argument `(key_ptr, key_len,
value_ptr, value_len)` ABI. Any `env_set()` call — `check`, `test --help`,
and now `native-build`'s own admission probe — forwards the wrong register as
the value pointer and glibc `strlen()`s garbage. `bin/simple` is a symlink to
this same artifact, so every candidate in `_find_simple_binary_for_target()`
fails identically; there is no working "runnable pure-Simple compiler" on
this host to build the RV64 kernel with.

The documented required fix is a full self-hosted redeploy from a strict
Stage 2/3/4 pure-Simple bootstrap (doc's "Required fix and gate" section) —
which this lane is explicitly forbidden from running (`Do NOT run a stage4
bootstrap or full bin/simple build bootstrap — peaks near 65GB and trips a
64GB kill cap`). I did not attempt a bootstrap, did not fall back to the Rust
seed as a substitute build path (forbidden by project rules — "don't fall
back to the seed"), and did not patch runtime ABI code — all out of scope
for a probe/build lane and would not be a real fix without the redeploy this
bug requires.

## Attempts this retry (fresh 3-cycle cap, 1 of 3 used)

1. `bin/simple os build --scenario=riscv64-display-smoke` — media phase now
   passes (coordinator's fix confirmed effective); fails at `phase=build`
   with "no runnable pure-Simple compiler". Root-caused via 2 direct
   reproductions + 1 GDB backtrace of the admission-probe fixture build
   (diagnostic, not counted against the build-attempt cap). Stopping here:
   the blocker is deterministic, pre-existing, already tracked, and its
   documented fix (full bootstrap redeploy) is out of this lane's scope.

## What is/isn't evidence

- `build/os/fat32-riscv64-desktop.img` — present, valid, gate now passes
  cleanly (media phase fix confirmed working end-to-end this retry).
- `build/os/simpleos_riscv64_display_smoke.elf` — still absent. No QEMU
  session was started. No serial log, no QMP scanout, no
  width/height/stride/nonblack/palette evidence exists for this run.
- Environment note (not a repo change): `~/.local/bin/{mtype,mdir,...}` are
  symlinked to a pre-existing local mtools build at
  `/tmp/simple-mtools/root/usr/bin/` for this host/session, since `mtools`
  is not apt-installed here. Kept in place per instructions.
