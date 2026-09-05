# Why `check-no-jit-module-drop.shs` can only measure ~half its own scope

Date: 2026-08-18 · Lane COVERAGE2 · Guard: `scripts/check/check-no-jit-module-drop.shs`

## The question

Run as the hook runs it (`--candidates`), the guard reported:

```
PASS — 234 of 415 selected module(s) MEASURED (56%), 0 paren-less accessor de-JIT drops;
       181 NOT MEASURED and NOT covered by this verdict
```

Earlier the same day it read `127 measured / 288 unmeasurable`. Two questions:
what is in the 181, and why does the ratio move?

## 1. The WHY breakdown, with counts

From `build/check/jit-module-drop/unmeasurable.txt` (181 rows, one per module),
tallied on the guard's own `bucket` column:

| bucket | count | share | what it means |
|---|---:|---:|---|
| `undefined` | 117 | 65% | semantic resolution failed — an identifier the module uses is not resolvable by `simple compile` in its single-file lane |
| `other` | 35 | 19% | mixed; see sub-split below |
| `lint` | 16 | 9% | a **lint** refused before the compiler ran — e.g. the runtime-family layering rule |
| `emit` | 11 | 6% | SMF emission failed after lowering, but not the recoverable standalone-SMF case |
| `parse` | 2 | 1% | the source does not parse for this compiler |
| timeout / memory budget | **0** | 0% | no module in this run hit the 120s budget |
| unavailable target / feature | **0** | 0% | none — this guard drives no target-specific lane |

Sub-split of the 35 `other`, by first error line:

| shape | count |
|---|---:|
| `codegen: Failed to parse object into relocation-aware SMF: Invalid …` | 5 |
| `SMF emission fail…` (variants, truncated at different columns) | 5 |
| `struct 'DirEntry' / 'LoopInfo' has no field named …` | 6 |
| `HIR lowering: cannot resolve import …` | 3 |
| `MIR lowering: Unsupported …` | 1 |
| remaining assorted semantic failures | 15 |

Mapping onto the categories the task asked for:

- **layering / lint rejections — 16** (9%)
- **genuine compile errors — 42** (`emit` 11 + `parse` 2 + the ~29 of `other`
  that are real semantic/codegen defects)
- **missing dependency / entry context — 117 + 3 unresolved imports = 120** (66%)
- **time or memory budget — 0**
- **unavailable target / feature — 0**
- **probe-harness limitation — see below; it is not a separate bucket, it is the
  cause of most of the 120**

## 2. The dominant cause — one insight, not a dozen fixes

**Two thirds of the gap is one thing: the oracle's symbol resolution is weaker
than the lane it is fencing.**

`simple compile <one file>` must resolve every identifier the module names.
The `run`/JIT lane this guard exists to protect does not have that problem — it
loads the whole program. So the fence is systematically blind to exactly the
modules that depend most on their surroundings.

Two distinguishable sub-causes inside the 117:

- **Symbols that DO exist in the tree but are not visible to the single-file
  probe.** `ds_set_active` (8 modules) is defined in
  `src/lib/nogc_sync_mut/io/debug_state.spl`; `wrap_text` (4 modules) is defined
  in four `cli/formatting.spl` files and `src/lib/common/format_utils.spl`.
  These are **probe-context** losses and are in principle recoverable by a
  better harness (§5).
- **Symbols that exist NOWHERE.** `_bi_bytes_to_hex` (11 modules) has **no
  definition anywhere in `src/`** — it is used in
  `src/lib/common/crypto/types.spl` and `src/lib/common/privilege/store.spl`
  and declared by nothing. That is the same shape as the C-runtime
  `RtCoreUInt` incident (`runtime_native_c_uncompilable_…_2026-08-11.md`): a
  *use* of a never-defined symbol, invisible to every text-and-tree guard.
  **This is a real tree defect this investigation surfaced as a side effect,
  and it is not the JIT guard's to fix.**

The `lint` bucket (16) is the one category where the exclusion is arguably
gratuitous — a runtime-family layering rule has nothing to do with de-JIT
detection. But there is **no `--no-lint` / `--skip-lint` flag on `simple
compile`** (searched; only `SIMPLE_LINT_PROFILE` exists, in the `fix` rule
registry, not on the compile path). Adding one is a compiler change, out of this
lane's scope, and would be a weakening if done carelessly. Recorded, not done.

**There is no cheap win.** The single largest recoverable slice is ~12 modules
(`ds_set_active` + `wrap_text`), and recovering even those needs a harness
change, not a guard tweak.

## 3. Risk in the unmeasured set — an UPPER BOUND, not a defect count

Every one of the 181 matches the candidate filter by construction, so "181
contain an accessor token" is vacuous. The useful narrowing uses the fact
recorded in the guard's own header: **`.length` is the only member of the family
that is silently wrong** — `.size` and `.empty` die at runtime and self-report.

Restricting to paren-less `.length` on non-comment lines in the 181:

> **UPPER BOUND (raw grep): 52 modules, 137 lines.**
>
> **MEASURED (2026-08-18, lane FPLENGTH): 6 genuine sites in 4 modules.**
> **The 137 figure is 95.6% false positive (131 of 137).**

Derivation — every one of the 137 lines was classified by resolving the
RECEIVER's type and asking whether its declaring struct/class actually declares
a `length` field (69 types in `src/` do). Encoded as
`scripts/check/check-paren-less-length-classify.shs` (fatal `--selftest` with
both a must-detect and a must-NOT-detect fixture); the residue it leaves
undetermined was hand-verified.

| bucket | sites | note |
|---|---:|---|
| **METHOD — genuine paren-less call (the defect)** | **6** | 4 found automatically, 2 by hand |
| FIELD — legitimate struct field named `length` | 92 | `RefcBinary`, `BinaryRef`, `H2FrameHeader`, `DerLength`, `SemanticToken`, `SpanOpBatch`, `PmapSidecarEntry`, `NvfsExtentRow`, `SosixFsServiceDispatchPlanV1`, `SafetensorsTensorEntry`, … |
| NON_CODE — not Simple code at all | 35 | inside string literals (embedded JS `document.querySelectorAll(...).length`, Test262 fixtures `'hello'.length`), docstrings (`Hash.length` in RFC 8446 pseudo-code), and one `for i in 0..length:` range that is not an access |
| UNDETERMINED — labelled, not dropped | 4 | `ref_val.length` ×4 in the three `message_transfer.spl` copies: the receiver is `ValueWrapper`, which declares `ref_length`/`ref_offset`/`ref_id` and **no** `length` — a distinct wrong-field-name issue, not this defect class |

Total 6 + 92 + 35 + 4 = 137.

The 6 genuine sites, all on builtin containers:

| site | receiver | why |
|---|---|---|
| `src/app/dap/hooks.spl:327` | `self.current_frames` | field declared `[StackFrame]` — an array |
| `src/app/dap/hooks.spl:443` | `parts` | `condition.split("==")` — an array |
| `src/app/dap/hooks.spl:449` | `mod_parts` | `mod_expr.split("%")` — an array |
| `src/os/port/disk_image_bake.spl:42` | `data` | `val data: [u8]` — an array |
| `src/os/apps/sshd/sshd.spl:134` | `resolved` | `fs_exec_resolve(name) -> text` — a string |
| `src/os/apps/sshd/sshd.spl:179` | `resolved` | same |

The last two are the classifier's known limit: the type comes from a
CROSS-FILE function return, which intra-file textual resolution cannot see, so
the script leaves them UNDETERMINED rather than guessing. That is why the
undetermined bucket exists and why it is never counted as clean.

So the honest statement replacing the upper bound is: **at most 4 of the 181
unmeasured modules contain a paren-less `.length` de-JIT, and all 6 sites are
now named.** The remaining warnings in this section about `SvimPiece.length`
and the `Pair.first` trap are confirmed, quantified: they account for 92 of the
137, and non-Simple text for another 35.

## 4. Why the measured/unmeasured ratio MOVES

Investigated. The headline finding is that **most of the observed move was not
non-determinism at all**:

1. **A code change, not a flake (accounts for essentially all of 127→234).**
   The `LOWERED_CLEAN` category was added to the guard between the two runs. It
   reclassifies "lowering completed, then failed downstream at the
   standalone-SMF check" from unmeasurable to measured, on a mutation-proved
   ordering argument. 288 − 181 = 107 modules moved by that change alone.
   Comparing the two verdicts was comparing two different guards.
2. **The oracle itself is replaced under the guard.** `bin/simple` is a symlink
   other sessions retarget mid-session — three distinct builds in one session is
   documented in `.claude/rules/commands.md`. A different compiler resolves a
   different symbol set and therefore measures a different module set. **This
   was entirely unrecorded.** Fixed: every verdict now stamps
   `oracle=<realpath>(<size>/<mtime>) timeout=<n>s`.
3. **The 120s per-file budget is load-dependent.** On a box at load 33–55 with
   20+ concurrent `simple` processes, a module near the budget flips between
   measured and unmeasurable run to run. It was invisible because timeouts were
   folded into a `silent/timeout` bucket together with signals and OOM kills.
   **Fixed:** `rc 124` is now its own `timeout=` bucket. In this run it is 0 —
   which is itself the useful news: the budget is not currently the problem.
4. **The `--candidates` roster is read from the shared working tree** that ~10
   sessions mutate concurrently, so the *selected* denominator moves too.
5. **(Already fixed before this lane.)** Two concurrent instances shared
   `$LOG_DIR/work/one.log` and the fixed `drop-*.log` paths; logs named for one
   file were found containing another's error, and one instance's startup
   `rm -rf` deleted the other's scratch mid-scan. Runs are now fully
   run-unique (`run-$$-<epoch>/`), with the two summary lists published to their
   stable paths by atomic rename only at the END of a run.

**Non-determinism in a gate's coverage is a defect in its own right**, because
a coverage number that is not reproducible cannot be tracked or regressed
against. Items 2 and 3 are now attributable from the verdict line alone.

## 5. What a better probe harness would need (designed, not built)

Recovering the ~120 context losses is a harness problem:

- **Compile in package context, not file-at-a-time.** The probe would need to
  present the module together with its package siblings/prelude so cross-module
  symbols resolve. This collides with attribution: the guard drives one file at
  a time *precisely because the diagnostic names struct and field but not the
  source file* (see the header). A package-context probe must recover
  attribution some other way — e.g. bisecting a failing package, or a compiler
  change to include the file in the message. **The latter is the real fix and
  should be filed against the compiler, not worked around here.**
- **Do not invent a lint bypass** to harvest the 16 `lint` modules unless the
  compiler grows a first-class, documented flag. A guard that disables checks to
  raise its own coverage number is the fail-open pattern.
- **`_bi_bytes_to_hex` and friends are not harness problems.** They are missing
  declarations and should be fixed in the tree; 11 modules become measurable for
  free when they are.

## 6. What was changed, and what was deliberately not

Changed in `scripts/check/check-no-jit-module-drop.shs`:

- Oracle identity (`readlink -f` + size/mtime) and the per-file timeout are
  recorded in **every** verdict line, including `--selftest`, so two coverage
  numbers can be compared or declared incomparable.
- `rc 124` timeouts split out of the `silent` bucket into their own `timeout=`
  bucket, since they are the load-dependent, run-unstable cause.

Deliberately NOT done:

- **No allowlist**, no reason string added to `LOWERED_RE`, no widening of any
  measured category. `LOWERED_RE` remains the single documented exception with
  a mutation proof behind it.
- **No lint bypass**, no `--skip` of any kind. An unmeasurable module still
  counts as unmeasurable, never clean.
- The verdict wording (`N of M selected MEASURED … K NOT MEASURED and NOT
  covered by this verdict`) was already correct and prominent; it was not
  softened. `n_measured == 0` still exits **2**, not 0.

`--selftest` remains fatal, 5 fixtures, both directions. Fail-closedness was
re-proved by **mutation**: blinding `DROP_RE` and widening `LOWERED_RE` each
make the guard exit 2 and report on nothing.

## Open items worth filing separately

1. `_bi_bytes_to_hex` used at 2 sites, defined nowhere — blocks 11 modules.
2. The accessor diagnostic does not name the source file, forcing one-file-at-a-
   time probing and capping this guard's achievable coverage.
3. No supported way to compile-check a module without the layering lint.
