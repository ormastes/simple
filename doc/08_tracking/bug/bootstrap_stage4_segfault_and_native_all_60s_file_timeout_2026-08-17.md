# Stage 4 segfaults in load_sources; native_all's embedded CLI defaults per-file timeout to 60s (2026-08-17)

Status: OPEN (P1)

First end-to-end hand-driven bootstrap of seed -> stage2 -> stage3 -> stage4 in
an isolated worktree (`/mnt/data/worktrees/simple-phase2`, detached at
`c19b514ff2e`). Stages 2 and 3 both COMPLETED and were observed to run. Stage 4
did not. Three separate defects were found on the way; all evidence below is
from real artifacts, not fixtures.

## Observed stage results

| stage | producer | result |
|---|---|---|
| seed (Rust) | cargo `--release --bin simple` | exit 0, 10m52s, 59,618,496 B |
| stage 2 | seed -> `bootstrap_main.spl` | **COMPLETE**, 865 modules, 35,307,368 B, sha `67a572a2c19005a0…` |
| stage 3 | stage2 -> `bootstrap_main.spl` | **COMPLETE**, 865 modules, 35,307,368 B, sha `467cab5d4d5ece3f…` |
| stage 4 | stage3 -> `main.spl` | **SEGFAULT (exit 139)**, reproduced twice |

Stage 2 and stage 3 both satisfy the canonical Stage-2/3 sanity profile:
`--version` prints exactly `simple-bootstrap 1.0.0-beta` with **no Rust-seed
banner** (verified with `SIMPLE_BOOTSTRAP` and `SIMPLE_RUST_SEED_WARNING`
scrubbed from the environment), and `run` / `test` / `lint` are all rejected as
`unknown command` — expected for the minimal bootstrap entry, not a defect.

Stage 3 is **not** a byte-identical fixpoint of stage 2 (same size, different
sha256). That is a separate question from the crash and is not investigated
here.

## Defect 1 — stage 4 segfaults in `load_sources` (the blocker)

`stage3 native-build --entry src/app/cli/main.spl --mode one-binary` with the
canonical `--source src/compiler --source src/app --source src/lib --source
examples/10_tooling` completes closure discovery (`source_closure 1793/1793 step
1/6 complete`) and then dies:

```
[build] load_sources unknown/unknown step 0/6 starting
Segmentation fault (core dumped)
STAGE4_EXIT=139
```

Reproduced twice, ~30s in, at `--threads 8` and `--threads 4`. **Not an OOM**:
no `earlyoom` journal entry, 54 GB still available, and the exit is 139 (SIGSEGV)
rather than a kill. bootstrap.md's "a native-build timeout is often an OOM" note
does not apply — this is a genuine crash, and it is not a timeout at all.

Narrowing it is what produced Defect 3: with `--source src/app/cli` instead of
`--source src/app` (1793 -> smaller closure) the SAME compiler reaches a clean
diagnostic and exits 1 instead of crashing. So the crash is scale- or
ordering-dependent in `load_sources`, and it *masks a real diagnostic*: the
compiler segfaults where it should have printed the parse error below.

## Defect 2 — `native_all`'s embedded CLI defaults `--timeout` to 60s

Stage 3's first attempt failed with:

```
FAILED FILES (2):
  - src/app/io/mod.spl => timeout (60s)
  - src/compiler/10.frontend/core/__init__.spl => timeout (60s)
Build failed: native-build aborted: 2 file(s) failed to compile
```

863 of 865 modules compiled; only the two largest aggregator files exceeded the
per-file budget. Root cause is a **default inconsistency**, not slow code:

- `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:445` —
  library default `file_timeout: 300`
- `src/compiler_rust/native_all/src/lib.rs:169` — `let mut timeout: u64 = 60;`

A stage-2/stage-3 binary links `libsimple_native_all.a`, so its `native-build`
is served by native_all's embedded CLI and silently gets **60s, not 300s**. The
pure-Simple stage binary is slower than the Rust seed, so the seed clears 60s on
those two files and the self-hosted compiler does not — which is exactly why
this only ever bites at stage 3 and later. The same path also prints `warning:
unknown option '--low-memory', ignoring`, confirming which CLI parsed the argv.

**Workaround (used, and it works):** pass `--timeout 900` explicitly. Stage 3
then completed: `Build complete: 5 compiled, 860 cached, 0 failed`.

**Fix:** align native_all's default with the library's 300s (or have it inherit
rather than re-declare). A 60s default that only the self-hosted lane ever sees
is a bootstrap trap.

## Defect 3 — a valid comparison is parsed as a generic argument list

Revealed once the segfault was routed around. `src/app/office/sheets/data_ops.spl`
line 38 is:

```
    if key_col < 0 or key_col > (max_col - min_col):
```

which the stage-3 compiler rejects at **38:18** (the `0`) with:

```
Unexpected token: expected a type in generic argument position (Simple has no
const generic parameters, so a numeric literal such as `Tensor<i64, 2>` is not
a valid generic argument; ...), found integer literal
```

The source is valid Simple; `key_col<0 or key_col>` is being taken as a generic
argument list. The message is a red herring — nothing here is a `Tensor` and
nothing is a const generic. Related, possibly the same root cause:
`doc/08_tracking/bug/const_generic_argument_rejected_in_constructor_call_2026-08-17.md`.

Not yet minimised: an isolated `if a < 0 or b > c:` in a two-function fixture
parses cleanly on BOTH the seed and stage 3, so the bare comparison shape is not
sufficient to trigger it. Something else in `data_ops.spl` arms the
generic-argument path first. Whoever picks this up should start by bisecting
that file rather than by writing a fresh fixture — the obvious fixture does not
reproduce.

## Not a blocker: ByteOrder

`.claude/rules/bootstrap.md`'s KNOWN BLOCKER section still says stage 3 fails
with `unresolved type: ByteOrder` in `cache_validator.spl`. **That is stale.**
The fix is committed at `cffc414c2de` (save/restore of
`registering_import_symbols` around the lazy import registration in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`), and stage 3 was
observed to compile all 865 modules here with no ByteOrder error of any kind.
That rules-file section should be updated so the next lane does not budget
effort for an already-fixed defect.

## Gate status: correct, but unreachable

`scripts/check/check-bootstrap-stage3-selfverify.shs` (copied here from
`/mnt/data/worktrees/simple-bootverify`) was run against the real stage-3
artifact — its first non-fixture exercise. Verbatim verdict:

```
ERROR — nothing was checked
```

with `stage3_selfverify_reason=no_stage3_provenance_manifest_found`. **The gate
is not wrong** — its own `--selftest` passes (`PASS — 7 selftest fixture(s)
checked, gate behaves as specified`), its platform-dir glob is correct
(`stage3/*/provenance.env`, so the informational `platform=x86_64` line is
harmless), and refusing to grade an artifact whose provenance it cannot read is
the right behaviour. It correctly did NOT false-green a real stage-3 binary.

But it is currently **unreachable in practice**: the only writer of
`stage3/*/provenance.env` is `scripts/bootstrap/bootstrap-from-scratch.sh`, and
that script cannot run at all — see
`bootstrap_admission_v2_fail_closed_blocks_all_bootstraps_2026-08-17.md`;
`bootstrap_planner_v2_verify` ends in an unconditional `return 1`. So today the
gate can only ever return ERROR on a real artifact, and hand-writing the
manifest to satisfy it would be fabricating provenance. Either the admission
producer ships, or the gate needs a documented way to grade an
explicitly-declared hand-driven artifact.
