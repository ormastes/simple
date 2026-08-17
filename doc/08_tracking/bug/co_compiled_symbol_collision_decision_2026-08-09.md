# Co-compiled symbol collisions — root cause, distribution, and decision

**Date:** 2026-08-09
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Supersedes the analysis in:** `duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09.md`
**Measured from:** the SHARED working copy at `/home/ormastes/dev/pub/simple` (a worktree cannot measure this — `use std.X` resolves only to the main repo)

## 0. Reproduction

```
SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1 bin/simple test \
  test/01_unit/compiler/cache/action_key_spec.spl 2>&1 | grep -c co-compiled
```

Measured **375** (the prior doc's 373; the delta is two symbols and is not
material). Full transcript retained in the session scratchpad; every census
below used `/usr/bin/grep` — the wrapped `ugrep` honours `.gitignore` and
undercounts.

## 1. Class A / Class B split — the prior doc had the ratio backwards in impact terms

| class | meaning | count | share |
|---|---|---|---|
| **A** — differing signatures | ambiguity fallback, a type/arity error *can* fire | **25** | 6.7% |
| **B** — IDENTICAL signatures | one definition silently wins, **no diagnostic can ever fire** | **350** | 93.3% |

Class B is not a subset of the problem — it *is* the problem. Of the 350
Class B warnings, **296 name public symbols** (spec-reachable) and 54 name
`_`-prefixed private helpers.

**Diagnostic gap worth recording:** the `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1`
owner-path annotation is emitted **only for Class B**. All 25 Class A warnings
carry no owner paths at all, so Class A is currently *unattributable* from the
diagnostic alone. That is why three prior agents each "found more definitions" —
they were chasing Class A symbols (`file_read_bytes`, `shell`, `dir_remove_all`)
whose owners the tool never printed.

## 2. Distribution by owner-module group (all 375, not a sample)

| count | class | module group |
|---:|---|---|
| 109 | B | `src/app/io` + `src/lib/nogc_sync_mut` |
| 50 | B | `src/compiler/90.tools` + `src/lib/nogc_sync_mut` |
| 28 | B | `src/lib/nogc_sync_mut` (intra-tier) |
| 27 | B | `src/lib/nogc_async_mut` + `src/lib/nogc_sync_mut` |
| 25 | A | *(unattributed — see §1)* |
| 22 | B | `src/compiler/80.driver` (intra-module) |
| 21 | B | `src/lib/gc_async_mut` + `src/lib/nogc_sync_mut` |
| 17 | B | `src/lib/common` + `src/lib/nogc_async_mut` |
| 15 | B | `src/compiler/99.loader` |
| 11 | B | `src/compiler/10.frontend` + `src/lib/common` |
| 9 | B | `src/app/io` (intra-tree) |
| 8 | B | `src/lib/gc_async_mut` |
| 8 | B | `src/compiler/70.backend` |
| 4 | B | `src/compiler/10.frontend` |
| 3 | B | `src/lib/common` |
| 27 | B | 20 further groups, ≤2 each |

### The stated hypothesis is TRUE but accounts for only ~31%

`src/app/io/**` × `src/lib/nogc_sync_mut/**` is the single largest group at
**109 + 9 (intra-app/io) = 118 of 375 (31.5%)**. It is the right place to start
and it is genuinely a parallel-implementation problem (§3). But **it is not the
whole 375**, and a plan scoped only to the io trees will leave ~257 collisions
standing. Three further, independent duplication axes are visible:

- **Tier duplication inside `src/lib`** (~76): the same module is copied across
  `common` / `nogc_sync_mut` / `nogc_async_mut` / `gc_async_mut` — e.g.
  `basename` in both `std.nogc_async_mut.path` and `std.nogc_sync_mut.path`;
  `allocate_buffer` in both `std.common.binary_io` and
  `std.nogc_async_mut.binary_io`. This is the same disease as app/io, one level up.
- **Intra-module facade duplication in the compiler driver** (22): every
  `aot_*_file` symbol is defined in *both* `driver_api_codegen_backends.spl` and
  `driver_public_compile_backends.spl` — an API layer and its public facade both
  carrying full bodies rather than the facade re-exporting.
- **`90.tools` × `lib/tooling`** (50): `src/compiler/90.tools/fix/rules/impl_/*`
  duplicated against `src/lib/nogc_sync_mut/tooling/easy_fix/rules.spl`.

## 3. `src/app/io/**` vs `src/lib/nogc_sync_mut/io/**` — a HALF-COMPLETED migration

72 files in `src/app/io/`, 69 in `src/lib/nogc_sync_mut/io/`, **39 filenames in
both**. Classifying all 39 by content:

- **16 are already pure re-export shims** — 3-line files whose entire body is
  `export use std.nogc_sync_mut.io.<name>.*`
  (`compress_sffi`, `coverage_simple`, `crypto_sffi`, `debug_stubs`, `dir_ops`,
  `env_ops`, `file_discovery`, `ftp_sffi`, `math`, `process_limit_enforcer`,
  `profiler_simple`, `regex_sffi`, `ssh_sffi`, `sysinfo_ops`, `thread`,
  `time_ops`). These emit no collisions.
- **23 are diverged near-copies** — same filename, same public surface, bodies
  that have drifted by a handful of lines. Line-count pairs make the copy origin
  unmistakable: `graphics2d_sffi` 510/510, `rapier2d_sffi` 474/474,
  `vhdl_sffi` 111/111, `gamepad_sffi` 418/417, `http_sffi` 485/483,
  `regex_simple` 388/390, `sqlite_sffi` 506/522, `window_sffi` 738/821.
  Measured differing-line counts: `vhdl_sffi` 6, `rapier2d_sffi` 22,
  `graphics2d_sffi` 44, `sffi_common` 11, `string_helpers` 5, `file_shell` 3.
- **0 are byte-identical.** Every surviving pair has drifted.

**Verdict: `src/app/io/**` is a fork of `src/lib/nogc_sync_mut/io/**` that
someone began converging file-by-file into re-export shims and stopped 16/39 of
the way through.** The shim files are the intended end state and they prove the
target architecture already works. This is not two designs in tension; it is one
migration left unfinished.

### They diverge in BEHAVIOUR, not just whitespace — cited

`file_shell.spl`, function `file_size(path: text) -> i64`, identical signature
in both trees:

- `src/app/io/file_shell.spl:28` — after `stat`, validates that every character
  of the trimmed output is a digit and **returns 0** otherwise, then `int(trimmed)`.
- `src/lib/nogc_sync_mut/io/file_shell.spl:28` — the digit-validation loop is
  **absent**; it calls `int(trimmed)` on unvalidated shell output directly.

Same name, same signature, different answers on malformed/absent `stat` output.
Class B: no diagnostic can distinguish them, one silently wins program-wide.

## 4. Is any spec currently vacuous because of Class B? — YES

Scanned all **25,024** `*_spec.spl` files against the 296 public Class B
symbols, matching each spec's `use` imports against the symbol's co-compiled
owner list.

**149 specs are at risk, across 266 (spec, symbol) pairs** — each is a spec that
imports owner X for a symbol that has ≥2 co-compiled same-signature owners, so
its call may bind to Y's body.

Worst-affected specs: `test/03_system/feature/io/native_ops_spec.spl` (8
symbols), `test/01_unit/app/io/cli_ops_handlers_spec.spl` (7),
`test/02_integration/app/sspec_maintain_cli_spec.spl` (7),
`test/01_unit/app/io/process_ops_ext_spec.spl` (6),
`test/03_system/app/mem_cli_spec.spl` (6).

### The proven-shape case

`test/01_unit/app/io/file_shell_exec_spec.spl:1`

```
use app.io.file_shell.{shell, shell_output, file_write, file_delete, file_size}
```

and at line 48 it asserts the size of a **nonexistent** file — precisely the
input on which the two `file_size` bodies of §3 disagree. A repo-wide census
finds **9 definitions of `file_size(text) -> i64`** (`src/app/io/file_ops.spl:131`,
`src/app/io/file_shell.spl:28`, `src/app/io/mod_stub.spl:277`,
`src/lib/nogc_sync_mut/ffi/io.spl:17`, `src/lib/nogc_sync_mut/io/file_ops.spl:137`,
`src/lib/nogc_sync_mut/io/file_shell.spl:28`, `src/lib/nogc_sync_mut/sffi/io.spl:17`,
`src/lib/nogc_async_mut/io/mod_stub.spl:264`, plus the `__init__` re-exports),
and the collision diagnostic reports `file_size` as **6 co-compiled definitions
across 5 modules with the SAME signature `(text)->i64`**. The spec names
`app.io.file_shell` in its import and cannot control which of the six it gets.

**Bearing on the ~180 recently-verified examples:** the failure mode is real and
demonstrated, but note what this scan does and does not establish. It proves
**149 specs cannot state which body they exercised** — their green is
unfalsifiable, not necessarily false. Where the colliding bodies happen to agree
(the majority, since they are copies), the assertion still holds by luck. The
correct reading is: *these 149 results are unverified, not disproven.* Any claim
that a verified example demonstrates a specific module's behaviour is
unsupported for those 149 until the collisions clear. Re-running them after the
fix is mandatory; a green result today is not evidence for the module named in
the import.

## 5. Recommendation

**Finish the migration that is already 16/39 done. Do not merge, do not
namespace, do not rename per-symbol.**

Per-symbol renaming provably cannot converge this (three agents, three
failures), and namespacing would preserve two live implementations of one
surface. Merging the trees as peers is wrong because they are not peers — one is
a stale fork of the other.

### Recommended path, in priority order

**Phase 1 — `src/app/io/**` → shims (clears ~118, 31%).**
For each of the 23 diverged pairs: diff both directions, port any behaviour the
app copy has and the lib copy lacks *into the lib copy* (the `file_size`
digit guard is one such; there will be others — the app fork is ahead on some
axes and behind on others, so this must be read both ways per §3), then replace
the app file with the 3-line `export use std.nogc_sync_mut.io.<name>.*` shim
that the other 16 files already demonstrate.

- **Files touched:** 23 rewritten to 3 lines, plus edits to the lib counterparts
  that receive ported behaviour (≤23). **~46 files.**
- **Importers do NOT need to change** — this is the key cost saver. 387 `src`
  files and 649 `test` files say `use app.io.*`; the shim keeps every one of
  those import paths valid. **1,036 files untouched.**
- **Risk: MEDIUM.** The whole risk is concentrated in the behaviour-porting
  step. Every dropped divergence is a silent regression, and it lands in io —
  the code every other subsystem sits on. Do it **one file per commit**, and
  re-measure the 375 after each; a file that does not lower the count did not do
  what you thought.

**Phase 2 — `src/compiler/80.driver` facade — ~~clears 22, cheapest win~~
DO NOT SHIM. This rating was WRONG.**

> **CORRECTION 2026-08-09, after inspection.** The original text below said "make
> `driver_public_compile_backends.spl` re-export the `aot_*` symbols from
> `driver_api_*.spl` instead of redefining them, ~3 files, risk LOW — same
> module, same tree, no cross-tier semantics." **Every clause of that is wrong.**
>
> The two sides are not duplicates; they are two deliberate execution strategies
> that collide on 9 `aot_*` names by accident:
>
> - `driver_api_codegen_backends.spl` compiles **in-process**
>   (`compiler_driver_create` / `compiler_driver_run_compile`).
> - `driver_public_compile_backends.spl` spawns a **subprocess**
>   (`rt_process_run(simple_bin, ["compile", ...])`), guarded by
>   `check_compile_delegation_guard` / `mark_compile_delegated` in
>   `driver_public_shared.spl` — anti-recursion machinery whose comment records
>   that a naive `/proc/self/exe` shell-out **caused a fork bomb on 2026-07-25**.
> - `driver_public_compile_vhdl.spl::aot_vhdl_file` deliberately imports
>   `run_compile_to_path` FROM the public facade to reach the subprocess path.
> - A prior session already treated this collision as intentional:
>   `src/app/cli/bootstrap_main.spl:304-307` documents working AROUND the
>   ambiguous import rather than merging the two.
>
> Collapsing the facade into `export use` would silently convert every
> subprocess-isolated caller to in-process compilation and defeat the recursion
> guard. "Diff both directions and port the divergence" does not apply: the
> divergence is not a bug-fix gap, it is two load-bearing behaviours sharing a
> name.
>
> **Correct fix is RENAME, not merge** — e.g. `aot_*_delegated` on the public
> side or `_inprocess` on the API side, so both survive under distinct names.
> That touches the facade re-export lists (`driver_public_compile.spl`,
> `driver.spl`, `driver_api.spl`, `__init__.spl`) and is NOT a low-risk slice.
> Return it to triage.
>
> General lesson, consistent with the `file_read_bytes` failure: **a name
> collision is not evidence of duplication.** Before shimming, establish that
> the two bodies are the same *thing*, not merely the same *signature*.

**Phase 3 — `90.tools` × `lib/tooling/easy_fix` (clears 50).** Same shim
technique. **~10-15 files, risk LOW-MEDIUM.**

**Phase 4 — `src/lib` tier duplication (clears ~76).** This one needs a design
ruling first, not a refactor: whether `common`/`nogc_sync_mut`/`nogc_async_mut`/
`gc_async_mut` are permitted to redefine a symbol at all, or must re-export from
the lowest tier that can host it. Do not start Phase 4 before that ruling.

**Phase 5 — Class A (25).** Blocked on a tooling fix: extend the
`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1` owner-path annotation to the
differing-signature branch. Class A is currently unattributable and every prior
attempt to fix it blind failed. **Fix the diagnostic before touching the code.**

### Regression metric

The 375 count is the campaign metric; re-measure with the §0 command after every
commit. Per-phase targets: P1 → ~257, P2 → ~235, P3 → ~185, P4 → ~109.
A phase that does not move the number did not land.

### Separately, and independently valuable

The 149 at-risk specs should be re-run and re-verified **after** Phase 1, and
their prior green results should not be cited as evidence for any specific
module's behaviour until then.
