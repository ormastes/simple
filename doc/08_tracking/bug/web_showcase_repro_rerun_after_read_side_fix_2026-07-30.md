# Web showcase repro re-run after the read-side fix — STILL BLOCKED, and it is the already-documented write-side defect, not a new gap

This is the original repro that launched the whole JIT chase this
session: `web_standards_showcase status=fail reason=blank-or-uniform
pixels=0 nonzero=0 checksum=0`, first attributed to gap 7, then gap 8,
then gap 9. Gap 9 (and gaps 10 and one manifestation of the same
mechanism) were closed by the read-side fix `26a0c4ad9ef` (`doc/
08_tracking/bug/jit_run_file_pipeline_gaps_2026-07-30.md` §11). **Nobody
had re-run this specific repro since that fix landed.** Per instruction:
re-run it, do not report the cell unblocked unless it produces non-zero
pixels, and characterize precisely rather than force a fix if it is still
blocked.

## Result: still blocked. Do not report this cell as unblocked.

`pixels=0 nonzero=0 checksum=0`, identical to every prior attempt.

## Binary identity (PROVED, per instruction to confirm before running)

The deployed binary has moved twice today; both runs below record exact
identity, not just "the deployed binary":

| Binary | Path | sha256 | Has the read-side fix (`26a0c4ad9ef`)? |
|---|---|---|---|
| Baseline | `bin/release/x86_64-unknown-linux-gnu/simple` (deployed, copied to `build/tmp/claude_simple_deployed`) | `ea4af9a4498297e3c4f31ca74082c20ebb10d7d2cc65218cea022960e15e597d` | **No** — confirmed empirically (see below), not just by hash/date |
| Fixed | Built this pass from a fresh worktree at `ba99705924f3` (this session's current `main` tip), copied to `build/tmp/claude_simple_fixed` | `dde638a7b3ab317d5ae13b8ff6a6a7fac810cf46011a0d7476373bc869b5d852` | **Yes** — confirmed empirically |

**Fix-presence confirmed by behavior, not by hash/date alone** (the
standard this whole sweep has used): ran both binaries against
`test/fixtures/jit_differential/module_global_direct_read_untagged.spl`
(`val X = 100; print("X={X}")`) before doing anything else.

```
$ SIMPLE_EXECUTION_MODE=jit build/tmp/claude_simple_deployed run module_global_direct_read_untagged.spl
X=<value:0x64>          # unfixed
$ SIMPLE_EXECUTION_MODE=jit build/tmp/claude_simple_fixed run module_global_direct_read_untagged.spl
X=100                    # fixed
```

## Environment preconditions (confirmed before running, per instruction)

- **`assets/fonts` count**: the shared working copy has only 1 file
  present (clean `git status`, stale HEAD). Ran from a fresh `git
  worktree add --detach` at the SSH-verified `main` tip
  (`ba99705924f39d0ed355426597899d471522ade3`) instead. Confirmed
  `find assets/fonts -type f | wc -l` → **57** in that worktree before
  running anything.
- `SIMPLE_TIMEOUT_SECONDS=0` set (the 10s hard timeout on any
  `examples/`-containing path would otherwise fire mid-render).
- Both binaries copied to `build/tmp/claude_simple_{deployed,fixed}`
  (not the default cache path `kill_simple_monitor.shs` watches) before
  running.
- `stdbuf -oL -eL` wrapping every run; output captured to a file, not
  relied on live (block-buffering off-TTY plus a watchdog kill drops
  output silently otherwise).
- Host load ~7, ~71 `simple`/`cargo` processes at run time (other lanes'
  heavy builds) — both runs completed in well under a minute regardless,
  not a hang; polled in a bounded loop rather than parked on a
  notification.

## Exact commands and raw results

```
cd <fresh worktree at ba99705924f3>
SIMPLE_EXECUTION_MODE=jit SHOWCASE_RESOLUTION=480x360 SIMPLE_TIMEOUT_SECONDS=0 \
  stdbuf -oL -eL build/tmp/claude_simple_deployed run examples/06_io/ui/web_render_file_gui.spl
  → web_standards_showcase status=fail reason=blank-or-uniform pixels=0 nonzero=0 checksum=0

SIMPLE_EXECUTION_MODE=jit SHOWCASE_RESOLUTION=480x360 SIMPLE_TIMEOUT_SECONDS=0 \
  stdbuf -oL -eL build/tmp/claude_simple_fixed run examples/06_io/ui/web_render_file_gui.spl
  → web_standards_showcase status=fail reason=blank-or-uniform pixels=0 nonzero=0 checksum=0
```

**The two full captured logs (577 lines each, all warnings plus the
final status line) are byte-for-byte identical**
(`sha256: 346a094a3db059521001934be44096280937cd810f1868c5a8ac5c39b2f869f5`
for both). The read-side fix changed nothing observable about this run
at all — not the warnings, not the timing shape, not the result.

## Shape of the failure — checked precisely, per instruction

**Not a crash, not a die-early.** Both runs complete the full pipeline
through HTML load, resolution resolve, and the actual render call, reach
the real correctness checks in `web_render_file_gui.spl`, and exit
cleanly with a diagnostic message — the same "pixels=0 with everything
else sane" shape as every prior attempt in this chase, not a different
failure mode.

**Precisely which check fires, and why that pins the root cause exactly.**
`web_render_file_gui.spl` has two possible failure branches before
`blank-or-uniform`:
```simple
if pixels.len() != RW * RH:
    print "...reason=wrong-pixel-count expected={RW * RH} actual={pixels.len()}"
    return 2
...
if not varied or nonzero == 0 or checksum == 0:
    print "...reason=blank-or-uniform pixels={pixels.len()} nonzero={nonzero} checksum={checksum}"
    return 3
```
The run hits `reason=blank-or-uniform` (return 3), **not**
`reason=wrong-pixel-count` (return 2) — which means `pixels.len() ==
RW * RH` was true. Since the printed `pixels=0`, this means `RW * RH`
is *also* 0. The pixel buffer was allocated at size 0 and is trivially
"blank" — this is not a rendering-engine defect at all, it is `RW`/`RH`
themselves still resolving to 0.

## Root cause: the already-documented WRITE-side defect, not a new gap

`RW`/`RH`'s declarations (`examples/06_io/ui/web_render_file_gui.spl:157-159`):

```simple
val SHOWCASE_DIMS: ShowcaseDims = showcase_resolution_dims()   # function-call initializer
val RW: i32 = SHOWCASE_DIMS.w                                   # field access on that global
val RH: i32 = SHOWCASE_DIMS.h
```

`SHOWCASE_DIMS`'s initializer is a **function call**
(`showcase_resolution_dims()`, which parses `SHOWCASE_RESOLUTION` and
returns a struct) — exactly gap 8's original shape, and exactly the
class `generate_module_init`/`runtime_init_globals` has no code path for
(`doc/08_tracking/bug/jit_run_file_pipeline_gaps_2026-07-30.md` §12,
confirmed in AOT binaries in §13, explicitly scoped OUT of this pass's
read-side fix by instruction — "leave gap 8's write-side defect alone").
`RW`/`RH` have explicit `i32` type annotations, so the *read*-side fix
(§11, which only changes inference for *unannotated* globals) was never
even reachable for them — their type was already concrete before and
after that fix. The chain is: `showcase_resolution_dims()` never actually
executes (write-side defect) → `SHOWCASE_DIMS` stays at its zeroed
default → `RW = SHOWCASE_DIMS.w` and `RH = SHOWCASE_DIMS.h` correctly
read that zero (nothing wrong with reading a genuine `0`) → `RW * RH ==
0` → an empty pixel buffer → trivially "blank."

**Confirmed with an isolated, minimal, decisive repro** (not relying on
the full pipeline's complexity alone) matching the exact construct shape
— struct-returning function, then two globals derived via field access:

```simple
struct Dims:
    w: i32
    h: i32

fn resolve_dims() -> Dims:
    Dims(w: 480, h: 360)

val DIMS: Dims = resolve_dims()
val RW: i32 = DIMS.w
val RH: i32 = DIMS.h

fn main():
    print("RW={RW} RH={RH} product={RW * RH}")
```

```
$ SIMPLE_EXECUTION_MODE=interpret <fixed binary> run probe.spl
RW=480 RH=360 product=172800
$ SIMPLE_EXECUTION_MODE=jit <fixed binary> run probe.spl
RW=0 RH=0 product=0
```

Exact match to the real repro's mechanism, isolated from any GPU/font/
rendering-engine confound.

## Disposition

**This is not gap 11.** It is the write-side defect already
characterized in `doc/08_tracking/bug/
jit_run_file_pipeline_gaps_2026-07-30.md` §12-§13 (and confirmed there to
also affect real, standalone AOT binaries via `simple compile --native`),
now additionally confirmed to be the actual, real-world blocker in the
code that originally motivated this entire campaign — not a new,
previously-uncharacterized defect. The read-side fix this pass landed
(§11 there) closed three real, independent gaps (9, 10, and one general
manifestation) but was never going to touch this one, because `RW`/`RH`'s
problem was never a read/tag-boxing problem — their inputs are never
computed in the first place.

**Not fixed here, per instruction and per the standing scope decision**:
the write-side fix needs a new codegen capability (lowering an arbitrary
module-level initializer expression as real code inside the generated
`__module_init`, for the Rust-seed's `generate_module_init`), which
`jit_run_file_pipeline_gaps_2026-07-30.md` §12.4 already scoped as an
architecture decision, not a patch, alongside gap 9's cross-file-identity
question. This pass's job was to re-run the repro and characterize
precisely why it is still blocked, not to reopen that decision.

**The one new, concrete piece of information this pass adds**: the
web-showcase cell's specific blocking mechanism is now pinned exactly
(`SHOWCASE_DIMS = showcase_resolution_dims()`, not any other global in
the file), and confirmed with an isolated repro independent of the full
rendering pipeline — so whoever picks up the write-side fix has an exact,
minimal, real-world-motivated regression case to verify against, not just
the synthetic `val X = get_value()` fixture.

## Evidence artifact index

- `build/tmp/webshowcase_evidence/webshowcase_baseline_deployed.log` —
  full 577-line capture, deployed (unfixed) binary.
- `build/tmp/webshowcase_evidence/webshowcase_fixed.log` — full 577-line
  capture, fixed binary; byte-identical to the above
  (sha256 `346a094a3db059521001934be44096280937cd810f1868c5a8ac5c39b2f869f5`
  for both).
- `build/tmp/webshowcase_evidence/showcase_dims_probe.spl` — the isolated
  minimal repro.
- Both binaries preserved at `build/tmp/claude_simple_deployed` (sha256
  `ea4af9a4498297e3c4f31ca74082c20ebb10d7d2cc65218cea022960e15e597d`) and
  `build/tmp/claude_simple_fixed` (sha256
  `dde638a7b3ab317d5ae13b8ff6a6a7fac810cf46011a0d7476373bc869b5d852`).
- Timestamps: baseline run started 2026-07-30 19:45:24 UTC, fixed-binary
  run started 2026-07-30 19:48:19 UTC; both completed in well under a
  minute.
