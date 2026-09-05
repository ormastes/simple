# Bootstrap "determinism check" compares builds of DIFFERENT source trees; PARTIAL then deploys

- Date: 2026-08-21
- Status: OPEN
- Area: `src/compiler_rust/driver/src/cli/commands/misc_commands.rs` (bootstrap gate)
- Severity: high — the gate's central claim ("deterministic output") is unfalsifiable as written, and its
  fallback verdict deploys on the strength of that claim.

## Symptom

A live `bin/simple build bootstrap` reported:

```
Stage 1: OK (9252160 bytes, hash=00b93cff12c0588c68cc21692fda7b72a0f0b9e079712dfaad64d47b57ff83dc)
Stage 2: OK (9256280 bytes, hash=450b649d490bf0feb2b656740c856216ffbce098e125c3b206df879edd0b1661)
```

All three stages invoke `compile_stage(&compiler, ...)` with the **same seed compiler** (`misc_commands.rs:405-470`);
per the in-code comment this is a determinism check, not self-hosting. Two "identical" invocations differed.

## What actually differs between the artifacts

Measured read-only on `bootstrap/stage1/simple` vs `bootstrap/stage2/simple`:

| section | stage1 | stage2 | delta |
|---|---|---|---|
| `.text`   | 0x008831e3 | 0x008843e3 | +4608 |
| `.rodata` | 0x0004a839 | 0x0004a939 | +256 |
| `.data`   | 0x00000228 | 0x00000240 | +24 |

- First `.text` divergence at **+0xf** — i.e. essentially from the start, not a localised insertion.
- **88.6%** of bytes differ across the aligned overlap; common `.text` suffix is 10 bytes.
- 16-byte chunk multiset overlap only 60.4% — consistent with wholesale function reordering *plus*
  repatched relative call targets, not a small delta.
- Both binaries are **stripped** (`nm` yields 0 symbols).
- String content is **identical**: 0 word-like strings unique to either binary, and 0 strings with
  differing occurrence counts. **The embedded-output-basename theory is disproven** — the same-basename
  isolation described in the code comment does hold, and no path or timestamp is embedded.

## Root cause

**The two stages did not compile the same source.** The bootstrap re-reads `src/**` from the *live working
copy* on every stage, and each stage takes ~15 minutes. Concurrent agent sessions edited the compiler
sources mid-run.

Stage1 artifact mtime `02:52:54`, stage2 `03:07:30`. Files under `src/` modified **between** those two points:

```
02:55:19  src/compiler/40.mono/monomorphize/__init__.spl
02:55:49  src/lib/nogc_sync_mut/test_runner/test_runner_files.spl
02:56:35  src/compiler/40.mono/monomorphize_integration.spl
02:59:16  src/compiler/40.mono/monomorphize/type_subst.spl
03:01:06  src/compiler/50.mir/mir_lowering_types.spl
03:01:33  src/compiler/50.mir/mir_types.spl
03:01:36  src/compiler/50.mir/_MirLowering/module_lowering.spl
03:01:51  src/compiler/50.mir/mir_lowering_stmts.spl
03:01:51  src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl
03:05:42  src/compiler/60.mir_opt/mir_opt/_Inline/policy.spl
```

(23 `src/**.spl` files were modified across the whole run window; the 10 above fall strictly between the
two stage outputs. All are `git status` dirty.)

These files are inside the compiled closure: the entry is `src/app/cli/bootstrap_main.spl` built with
`--entry-closure`, and the stage1 binary contains compiler-internal strings (`MethodResolver.*`,
`error[layer_dag]`, monomorphisation diagnostics). Monomorphisation, MIR lowering and inline-policy edits
are precisely the kind that shift every emitted function — which matches the observed 88% churn and the
small net size growth.

## Ruled out (evidence, not assumption)

- **Embedded output path / basename** — string sets are byte-identical between the two artifacts.
- **Seed compiler changed mid-run** — `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
  mtime `02:37:25`, i.e. stable before stage1 and unchanged through stage2.
- **Nondeterministic module discovery order** — `discovery.rs:1102-1107` sorts `found_deps` before
  enqueue, `discovery.rs:1113` sorts `files`; package-facade resolution uses `BTreeMap` and a
  sorted/deduped sibling `Vec` (`discovery.rs:931-946`).
- **Nondeterministic link order** — `mod.rs:1071` re-sorts `object_paths_with_indices` by index.
- **`--timeout 180` silently dropping code** — it is a per-file timeout that fails the build closed
  (`compiler.rs:1031-1033`, `mod.rs:1077-1092`), and stub fallback is disabled by
  `SIMPLE_NO_STUB_FALLBACK=1` (`linker.rs:1591`).
- **Time/rand in codegen** — none; `Instant::now()` is used only for timing reports, `SystemTime` only in
  a `compiler_fingerprint()` fallback that feeds a cache key, never emitted content.

So there is **no evidence of a codegen determinism defect**. There is also no evidence *against* one: the
experiment as run cannot distinguish the two, because its control (identical input) was not held.

## Why this is still a real defect

The gate asserts determinism while re-reading a mutable input on each trial. Every verdict it can emit is
therefore uninterpretable in a repo with concurrent sessions:

- `MISMATCH` may mean nondeterministic codegen **or** an edit landed mid-run (this incident).
- `VERIFIED` only means no one happened to edit the closure during the window.
- `PARTIAL` is the *expected* shape when edits stop partway through — exactly what happened here.

## Verdict on the `PARTIAL` -> deploy path

`PARTIAL` (stage2 == stage3, stage1 differs) deploys. This is a fail-open and should fail closed.

The stated rationale — two of three agree, so the odd one out was a warm-up — has no mechanism behind it:
all three stages are the same command with the same compiler, so there is no reason stage1 should be
privileged as the wrong one. Under the actual failure mode here, `PARTIAL` is what a *mid-run source edit*
looks like, and deploying on it ships a binary built from an unpinned, unrecorded snapshot of a dirty tree.
It would equally mask genuine intermittent nondeterminism that happens to hit one stage in three.

**No gate behaviour was changed by this investigation.** Flipping `PARTIAL` to exit 1 on its own is not the
right first move: with the tree racing, that would make bootstrap permanently red for reasons unrelated to
the compiler. Validity must be fixed before strictness.

## Exact next step

1. **Make the check valid — pin the input.** Snapshot the closure once (e.g. `git worktree add --detach`
   or a content-addressed copy) and point all three stages at that immutable path, as
   `check-seed-builds-push.shs` already does for the Rust seed. Record the snapshot's tree id in the
   verdict line.
2. **Fail closed on a moving tree** even before (1) lands: capture the max mtime over the discovered
   closure before stage1 and after stage3; if it moved, emit `ERROR — inputs changed during the run`
   (exit 2), never `VERIFIED`/`PARTIAL`. This is cheap and is the honest verdict for the run above.
3. **Only then** re-run the three stages on the pinned snapshot to determine whether codegen
   nondeterminism exists at all. Until (1) and (2) exist, no bootstrap determinism claim in this repo is
   supported by evidence.
4. After (3) is green, remove the `PARTIAL` -> deploy branch so deployment requires `VERIFIED`.

## Reproduce / re-verify

```bash
# section deltas
objdump -h bootstrap/stage1/simple | grep -E ' \.(text|rodata|data) '
objdump -h bootstrap/stage2/simple | grep -E ' \.(text|rodata|data) '

# the decisive evidence: closure sources edited between the two stage mtimes
find src -name '*.spl' -newermt '<stage1 mtime>' ! -newermt '<stage2 mtime>' -printf '%TT %p\n' | sort
```

## Implementation (2026-08-21)

Steps 1 and 2 landed in `src/compiler_rust/driver/src/cli/commands/misc_commands.rs`:

- **Pinned input closure.** `create_bootstrap_snapshot()` materialises the closure once at
  `<output_dir>/.input-snapshot` (override: `SIMPLE_BOOTSTRAP_SNAPSHOT_DIR`) before stage 1;
  `compile_stage()` takes a `workdir` and all three stages run from it. `git worktree add --detach`
  (the `check-seed-builds-push.shs` pattern) was **rejected**: the tree is dirty, so it would compile
  HEAD rather than the source the operator asked for. Instead the live working-copy CONTENT is
  snapshotted — `.spl`/`.sdn` under `src/` are copied (141 MB), everything else (16 GB of build output,
  `.a`/`.o`, C runtime) is symlinked, and `target`/`build`/`vendor`/`node_modules`/`.git` are symlinked
  wholesale. Compiler and stage output paths are absolutised so the changed cwd is transparent.
- **Race safety net.** The closure is fingerprinted (per-file sha256, sorted, folded into one tree
  digest) before stage 1 and again after stage 3. If it moved:
  `ERROR — inputs changed during the run: <k> of <n> source file(s) differ: <paths>` (exit 2), emitted
  before any VERIFIED/PARTIAL/MISMATCH verdict. An empty closure is
  `ERROR — nothing was checked (...)` (exit 2), never a pass. A stable run prints the tree id.
- **`PARTIAL` -> deploy left in place**, with a `TODO(bootstrap-determinism)` naming this record and the
  removal precondition (one VERIFIED run on a pinned snapshot). Step 3 of this record — the actual
  re-run — is still outstanding; a bootstrap was in flight and was not disturbed.
