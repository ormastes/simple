# `check-store-open-acid.shs` cannot run on macOS aarch64 — and the recorded blocker is not the one that fires here

- Date: 2026-08-17
- Area: enterprise_store / native ACID evidence / pre-existing gate portability
- Severity: medium — the AC-5/AC-6 native-ACID row is recorded as blocked on
  one cause, but on this host it is blocked on three different ones, none of
  which is that cause. Anyone resuming from the recorded note will chase the
  wrong thing.
- Found by: `.spipe/simple_enterprise_suite` lane, macOS aarch64 host

## The recorded resume condition does not match this host

`.spipe/simple_enterprise_suite/state.md` (lane W13-A) records the native-ACID
row as blocked on a specific link failure:

> `BLOCKED — AOT native build failed: error: codegen: undefined symbol:
> rt_sqlite_open` … the source fix is in the seed, and this row stays BLOCKED
> for anyone using the deployed binary until a redeploy.

Measured on macOS aarch64 against `origin/main`, that error **never appears**.
Three distinct blockers fire instead, in this order:

### 1. `bin/simple` is the bootstrap-only binary — cannot emit native at all

```
$ sh scripts/check/check-store-open-acid.shs
BLOCKED — AOT native build failed: error: bootstrap compile supports --format=smf only
```

`bin/simple` on this host resolves to a wrapper over the bootstrap binary,
whose `compile` accepts `--format=smf` only. The gate defaults to
`SIMPLE="${SIMPLE_BIN:-$ROOT/bin/simple}"`, so out of the box it can never
reach the ACID probe here.

### 2. With the full-CLI binary, `compile` rejects EVERY source file

Re-run pointed at the other deployed binary:

```
$ SIMPLE_BIN=.../bin/release/aarch64-apple-darwin/simple sh scripts/check/check-store-open-acid.shs
BLOCKED — AOT native build failed: error: compile requires a source file
```

This is not a gate bug. The binary rejects its own documented invocation:

```
$ .../aarch64-apple-darwin/simple compile <probe>.spl --native -o /tmp/out
error: compile requires a source file
Usage: simple compile <source.spl> [-o <output>] [--native] ...
```

The usage line printed by the failure describes exactly the command that was
given. Reproduced with a relative path, an absolute path, and with `--native`
placed before the source file — all three fail identically, so it is neither
argument order nor path form. `--version` reports `Simple v1.0.0-beta` and the
binary prints the Rust-seed banner. **On this host, `compile` is unusable for
any source file**, which blocks every AOT-native evidence lane, not just ACID.

### 3. The fresh-binary path is blocked by ENOSPC

The resume condition for both of the above is a current binary, i.e. a seed or
bootstrap build. That is not possible here right now:

```
/System/Volumes/Data   460Gi   424Gi   2.1Gi   100%
```

2.1 GiB free. A cargo seed build needs far more. Repo-local consumption is
`build/` **88G** (of which `build/worktrees` 47G, `build/bootstrap` 14G, plus
several one-off lane bootstraps of 2.9–9.1G each) and `.git` 15G, across **37
registered worktrees** belonging to many concurrent sessions. Freeing space
means deleting other sessions' warm caches, which is a cross-session decision
and is deliberately NOT taken unilaterally here.

## Secondary defect found in the gate itself

The gate's binary-identity line uses a GNU-only `stat` flag:

```
scripts/check/check-store-open-acid.shs:27
echo "binary: $(readlink -f "$SIMPLE") ($(stat -c %s "$(readlink -f "$SIMPLE")") bytes)"
```

On macOS (BSD `stat`) this prints `stat: illegal option -- c` and the size
comes out **empty**:

```
binary: /Users/ormastes/simple/bin/release/aarch64-apple-darwin/simple ( bytes)
```

The line still prints, so the gate does not fail — it just silently emits
binary-identity evidence with the size missing. That is the weakest possible
failure mode for an evidence line whose whole job is pinning which artifact
produced a verdict. Portable form: `stat -c %s "$f" 2>/dev/null || stat -f %z "$f"`.

Related: two of the gate's inputs (`scripts/check/check-store-open-acid.shs`
itself and `test/fixture/enterprise_store/*.spl`) were ABSENT from the shared
working copy and had to be restored from `origin/main` before the gate could
run at all — the staleness filed in
`shared_working_copy_109k_lines_behind_origin_2026-08-17.md`. The gate
correctly refused to run vacuously (`ERROR — nothing was checked: missing
probe …`) rather than reporting a pass, which is the right behaviour.

## What this means for the acceptance row

The native-ACID row stays **blocked**, but the resume condition should be
rewritten. It is not "wait for the `rt_sqlite_open` seed fix to be deployed".
On this host it is:

1. free enough disk to build (a cross-session decision, see above), then
2. build a current binary, then
3. re-run `SIMPLE_BIN=<fresh binary> sh scripts/check/check-store-open-acid.shs`
   and read the last stdout line.

Only after step 3 can anyone say whether the `rt_sqlite_open` link failure is
still the frontier — on this host nothing has yet reached the link stage.

## Suggested fixes

1. Make the gate's `stat` call portable (one line, no behaviour change).
2. Have the gate fail fast with a NAMED reason when `SIMPLE` cannot compile a
   trivial source file at all, distinguishing "this binary cannot do native
   builds" from "this build failed" — currently both surface as
   `BLOCKED — AOT native build failed`, which is what made the recorded
   resume condition drift from reality.
3. File the `compile requires a source file` CLI defect against the deployed
   aarch64 binary separately if it reproduces on a fresh build; if it does not,
   it is another symptom of that artifact's age and the redeploy closes it.

---

## RESUMED 2026-08-21 with a fresh seed — the frontier moved three stages

The blocking prerequisite from the section above (ENOSPC) was cleared: four
abandoned lane build dirs (`wm-to-i64-bootstrap` 9.1G, `-fix2` 2.9G,
`gui-lane-bootstrap` 2.9G, `bootstrap-fix` 2.9G — all last touched 2026-08-01
to 08-11, no open file handles) were removed with the user's approval, taking
free space from 2.1 GiB to 23 GiB. Note for whoever hits this next: `rm -rf`
failed on them until `chmod -R u+w` — the trees are written read-only
(`-r-x------`), which reads like a permissions/ownership problem and is not one.

A fresh seed was then built from `origin/main` in an isolated worktree
(`cargo build --release --bin simple`, `CARGO_INCREMENTAL=0`, dedicated
`CARGO_TARGET_DIR`): **36,546,776 bytes, sha256 `e3850cedfc7e471c0fa07d86…`,
1m53s**. The shared `bin/` was NOT touched — the gate was driven via
`SIMPLE_BIN`, and the worktree got its own `bin/simple` symlink.

### Both blockers from the section above are GONE

Findings 1 and 2 (`bootstrap compile supports --format=smf only`, and
`compile requires a source file`) do **not** reproduce on the fresh seed. They
were artifacts of the deployed binaries' age, exactly as suspected. `compile
<src> --native` now parses and runs.

### New frontier A: the default linker is ELF-mode lld, fed Mach-O objects

```
BLOCKED — AOT native build failed: error: codegen: linker failed with exit code 1: lld failed
```

The underlying errors:

```
ld.lld: warning: libsimple_runtime.a: archive member '…-negti2.o' is neither ET_REL nor LLVM bitcode   (x ~40)
ld.lld: error: unable to find library -lSystem
ld.lld: error: unable to find library -lsqlite3
ld.lld: error: …/_main_shim.o: unknown file type
```

`-lSystem` is the Mach-O libc; "neither ET_REL nor LLVM bitcode" and "unknown
file type" are ELF-mode lld refusing Mach-O objects. The linker menu confirms
the whole selection surface is GNU/ELF-shaped and has no Darwin entry:

```
$ simple linkers
  ✗ mold   - Modern, fastest linker (Linux only, …)
  ✓ lld    - LLVM's linker (cross-platform, fast)   Homebrew LLD 22.1.2 (compatible with GNU linkers)
  ✓ ld     - GNU ld (traditional fallback)
Auto-detected: lld (will be used by default)
```

There is no `ld64.lld` / `-flavor darwin` option, and auto-detection picks
`lld` on macOS, where it cannot work. **`--linker ld` is the working override
on this host** — on macOS `ld` is Apple's ld64, not GNU ld as the help text
claims, and it consumes the Mach-O objects correctly.

### New frontier B: two runtime symbols undefined at link, both present in the archive

With `--linker ld` the link proceeds and fails on exactly two symbols:

```
Undefined symbols for architecture arm64:
  "_rt_alloc", referenced from: …
  "_rt_pool_safepoint", referenced from: _sqlite_query_all in main.o, _sqlite_row_get in main.o, _marker_present in main.o
```

Both **are** defined in the archive the link is given:

```
$ nm -gUA libsimple_runtime.a | grep -E 'T _rt_alloc$|T _rt_pool_safepoint$'
…-runtime_memory.o: 00000000000008ac T _rt_alloc
…-runtime_pool.o:   00000000000002b8 T _rt_pool_safepoint
```

A symbol that is defined in a supplied archive yet reported undefined is the
classic **archive-ordering** failure: ld64 pulls an archive member only if it
resolves an undefined symbol *already seen*, so an archive listed before the
object that references it contributes nothing. lld and GNU ld are routinely
more forgiving (and `--start-group` hides it entirely), which is consistent
with this never being seen on the Linux lane. Candidate fixes, in order of
preference: place `libsimple_runtime.a` after all objects on the link line;
or `-force_load`/`-all_load` the runtime archive on Darwin.

### Status of the recorded `rt_sqlite_open` blocker

Still **not reproduced on this host**. The link now fails earlier, on
`rt_alloc`/`rt_pool_safepoint`. Whether `rt_sqlite_open` is a further frontier
behind them is unknown until the ordering issue is fixed — note that
`-lsqlite3` was also unfound in the lld attempt, so the sqlite library path may
be a third, separate Darwin gap.

### Corrected resume sequence

1. Fix the Darwin link path: add a Darwin linker flavor (or make `--linker ld`
   the macOS auto-detection default, and correct the help text that calls it
   "GNU ld"), and fix the archive ordering / add `-force_load`.
2. Re-run `SIMPLE_BIN=<fresh seed> sh scripts/check/check-store-open-acid.shs`.
3. Only then is it meaningful to ask whether `rt_sqlite_open` is still the
   frontier.

The AC-5/AC-6 native-ACID row remains **blocked**, but the blocker is now
located three stages further in and is a concrete, named compiler defect
rather than an environment condition.
