# Stage 3 self-host: the 405 "HIR lowering error" blocker is stale; the live blocker is a SIGSEGV

Date: 2026-08-24
Lane: E (stage3 self-host)
Status: OPEN — root cause reclassified, not yet fixed

## Summary

Stage 3 self-host fails, so Stage 4 and every deploy path are unreachable. The
evidence carried into this lane was
`build/bootstrap/goal-stage2/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(copy: `/mnt/data/goal-logs/stage3-failure.log`, 405 `HIR lowering error`
lines). **That log predates `e0e308c8681` and no longer describes the tree.**
Re-measured at HEAD with the admitted Stage-2 binary, the error count is **0**
and the run dies with **SIGSEGV (rc=139)** instead.

## What the stale log said (405 errors, 4 classes)

| count | class |
|---|---|
| 207 | `unresolved name` |
| 152 | `field ... is not visible from this module` |
| 42 | `unresolved type` |
| 4 | `ambiguous explicit callable dependency` |

Mechanism, confirmed by static analysis of all 41 distinct `(file, name)`
pairs behind the 207 `unresolved name` errors: **every one** was a reference to
a symbol defined in a SIBLING file of the same package with **no explicit
`use`** (`imported_in_use=0` for 41/41). Examples: `hir_expr_env_get`
(`_Expressions/expression_support.spl` -> `expression_components.spl`),
`local_count_increment` (`mir_opt/var_reassign_analysis.spl` ->
`var_reassign_ssa.spl`), `X86_OP_CALL` (`native/mach_inst.spl` ->
`regalloc.spl`), 9 names from `_Items/lowering_helpers.spl`. The Rust seed
resolves these implicitly; the pure-Simple HIR lowering requires an explicit
import. This is the same defect class the in-tree comment at
`src/compiler/70.backend/linker/link.spl:25` already documents.

**This class is already fixed at HEAD** by `e0e308c8681`
("fix(hir): explicit imports for glob-only dependencies — stage 3 HIR reach
600 -> 692/692, fatals 1400 -> 300"), which is an ancestor of the lane HEAD
`94564e9030e`. The 152 field-visibility errors are covered by the in-flight
guards documented in
`src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl:332-385`
(owner-symbol-absent -> `-1` unknown rather than `0` denied), whose own
measurements record that `branch=retained-false` — the only arm that is a
genuine private-field violation — fired **0 times** across two full 692/692
runs. Remaining field denials there are symbol-id aliasing, a separate
documented family.

## What HEAD actually does (measured 2026-08-24)

Binary: the admitted Stage-2 compiler
`build/bootstrap/goal-stage2/stage2/x86_64-unknown-linux-gnu/simple`
(copied to `/mnt/data/lane-e-bin/stage2`, `simple-bootstrap 1.0.0-RC`).

```
cd <lane worktree>
SIMPLE_TIMEOUT_SECONDS=0 \
  ./stage2 compile --format=smf -o /tmp/bm_base.smf src/app/cli/bootstrap_main.spl
```

Result: `rc=139` ("dumped core"). `HIR lowering error` count: **0**.
`field ... is not visible`: **0**. `ambiguous explicit callable dependency`:
**0**. Source closure 692 modules, parse completed 692/692 at +217s, crash
during phase `hir` (step 2/6).

The apparent crash point in the default-buffered log (`hir 0/692`) is **not**
trustworthy: stdout was block-buffered and the tail was lost on the signal. A
line-buffered rerun is the only way to name the module.

## Open questions / next steps

1. Line-buffered + `ulimit -s unlimited` rerun (`stdbuf -oL -eL`) to name the
   crashing module. If it passes, rerun at the default 8 MB stack to separate
   "stack overflow from deep recursion in HIR lowering" from "flaky crash".
2. `apport` owns `core_pattern` here and discarded the core for this
   non-packaged binary; a `gdb -batch -ex bt` run is the fallback. Note
   `/var/lib/apport/coredump/` already holds an unrelated 2026-08-23 core for
   another lane's `build/bootstrap/stage2/.../simple`, so stage2 SIGSEGVs are
   recurring, not a one-off of this lane.
3. A single-file `compile --format=smf` of a compiler module additionally
   fails with `hir codec: no \`Visibility\` arm for tag -1; regenerate
   src/compiler/20.hir/generated/hir_codec.spl` — an unset (-1) Visibility
   reaching the codec. Filed here as an observation; it is on the smf-output
   path, not the crash path.

## Non-finding, stated so it is not re-chased

`src/compiler/{hir,backend,frontend,loader,mir_opt,types,...}` are **symlinks**
to the numbered directories (`20.hir`, `70.backend`, ...), not duplicate
trees. The "duplicate module trees" lead is therefore false as stated; the
`logical=832 physical=614` gap in the loader log is the symlink aliasing, and
the canonical import spelling used everywhere in-tree is the unnumbered one
(`compiler.hir....`).

## RESOLVED QUESTION (measured after the first write-up): the Stage-2 artifact is itself broken

The line-buffered + `ulimit -s unlimited` rerun reproduces the SIGSEGV exactly:
`[build] hir 0/692 step 2/6 +269693ms dt=145ms app.cli.bootstrap_main` then
`Segmentation fault`, `rc=139`, with `HIR lowering error` = 0 and
`not visible from this module` = 0. Unlimited stack did **not** help, so it is
not stack overflow from deep recursion.

The decisive test is much smaller than the compiler. A **two-line hello world**
fails on **both** commands the bootstrap CLI supports:

```
printf 'fn main():\n    print("hi")\n' > /tmp/hw.spl
stage2 compile --format=smf -o /tmp/hw.smf /tmp/hw.spl   # rc=1
stage2 native-build /tmp/hw.spl -o /tmp/hw_bin           # rc=1
```

Both print:

```
error: hir codec: no `Visibility` arm for tag -1; regenerate src/compiler/20.hir/generated/hir_codec.spl
```

**The admitted Stage-2 compiler cannot compile anything at all.** So:

- The 405-error narrative is doubly stale: the source class it names is fixed at
  HEAD, and the binary the lane was told to verify with cannot compile a
  hello world, let alone the compiler.
- The SIGSEGV above is that binary's defect, on its broken codec path — it is
  **not** evidence about HEAD sources. Nothing measured with this artifact can
  clear or condemn `src/compiler` at HEAD.
- `-1` is an UNSET `Visibility` tag reaching the HIR codec. This is the same
  malformed-tagged-value family as `7c453e7b076` ("contain malformed tagged
  values at the HirBlock clone — stage 3 SIGSEGV eliminated, 6/6 runs") and
  `e52f3e4de26` ("bare-lift `HirSymbol.type_` — heap `Some` box segfaulted
  HIR-cache encode"), both of which post-date the binary
  (`build/bootstrap/goal-stage2/stage2/x86_64-unknown-linux-gnu/simple`,
  132,944,880 B, mtime 2026-08-24 01:34).

### The gate defect this exposes

Stage 2 was **admitted with a provenance receipt** and Stage 3 was then run
against it. Nothing between those two steps ever asked the artifact to compile
a hello world — which is the exact failure shape
`scripts/check/check-stage-binaries-runnable.shs` was written for (a stage
binary whose `--version` answers cleanly while both of its real commands fail),
and that guard is currently ADVISORY, not MANDATORY, and honestly RED. The
Stage-2 admission path needs the same smoke test before the receipt is issued;
otherwise every Stage-3 failure report is unfalsifiable.

### Correct next action for this lane

Rebuild Stage 2 from HEAD (which contains `7c453e7b076`, `e52f3e4de26`,
`63f4b5d1362` and `e0e308c8681`) and re-run Stage 3 against the fresh artifact.
Do **not** spend further effort interpreting Stage-3 logs produced by the
2026-08-24 01:34 binary.
