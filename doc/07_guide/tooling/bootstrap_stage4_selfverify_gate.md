# Bootstrap Stage-4 self-verification gate

`scripts/check/check-bootstrap-stage4-selfverify.shs` — proves, **by executing
the stage-4 artifact**, that it is what Stage 4 is defined to produce. It is the
runtime half of stage-4 verification; the existing
`scripts/check/check-post-bootstrap-stage4-sspec.shs` is the paper half.

## What Stage 4 actually is (derived, not guessed)

`doc/07_guide/compiler/build.md` § "Bootstrap Stages" is authoritative:

```
Stage 3: stage2 native-build --entry bootstrap_main.spl -> build/bootstrap/stage3/<triple>/simple
Stage 4: stage3 native-build --entry main.spl           -> build/bootstrap/full/<triple>/simple
```

and `.claude/rules/bootstrap.md`: Stage 3 "only proves the Stage-2 binary can
recompile the *minimal bootstrap entry* — it is NOT the full-featured CLI. Stage 4
('Full CLI') is the separate step where the verified Stage-3 binary compiles
`main.spl`, producing the actual deployable `bin/simple` with every subcommand
(`test`, `lint`, `duplicate-check`, etc.). A binary at
`build/bootstrap/stage3/<triple>/simple` correctly answers only
`compile`/`native-build` — it has no `run`/`test`/`duplicate-check`."

So the self-hosting property Stage 4 claims is **not a fixpoint**. It is three
things, and this gate asserts all three:

1. **Lineage** — the artifact was produced *by* the verified stage-3 binary
   (`parent_compiler_path` / `parent_compiler_sha256` in the provenance), and is
   a genuinely distinct artifact from it.
2. **Not-seed** — it is a pure-Simple binary, not the Rust seed.
3. **Capability delta** — it answers the full-CLI subcommands that its own
   stage-3 parent demonstrably rejects. This is the only property that
   mechanically separates a stage-4 binary from a stage-3 one at runtime, which
   is why the gate probes **both** binaries.

## Gap this closes: the existing sspec gate never runs the binary

`check-post-bootstrap-stage4-sspec.shs` is a good paper gate — it re-runs
`stage4_verify_candidate_provenance`, which recomputes every sha256 in the 21-key
provenance manifest, re-binds the stage-3 manifest, and re-validates the
build/smoke log lane. But it **never spawns the stage-4 binary**. Its closing
lines —

```
post_bootstrap_stage4_test_runner=true
post_bootstrap_stage4_lint=true
post_bootstrap_stage4_duplicate_check=true
post_bootstrap_stage4_acceptance=true
```

— are unconditional literal `echo`s emitted once the paper check succeeds. They
assert tool capability **by fiat**. Neither that script nor
`scripts/check/lib/stage4-candidate-provenance.shs` executes anything.

`scripts/check/check-bootstrap-essential-tools-smoke.shs` *does* execute the
binary and exercises the test runner, lint and duplicate-check deeply — but it
runs *inside* bootstrap as a build step, has no verdict-line convention, no
`--selftest`, no non-vacuity guarantee, no artifact-identity record, and no
seed detection. This gate is the standalone, fail-closed, re-runnable
re-verification of the finished artifact; it does not duplicate the smoke
gate's per-subcommand depth.

## Assertions

| # | Assertion | Notes |
|---|-----------|-------|
| A1 | Artifact exists, is a regular file, executable, non-empty | path, **size and sha256 are printed**; never inferred from an exit code |
| A2 | Provenance adjacent, `schema=simple-bootstrap-stage4-provenance-v1`, `status=pass`, `artifact_kind=pure-simple-full-cli` | provenance is parsed, never sourced |
| A3 | `output_path` == the binary and `output_sha256` == the **recomputed** hash | binds the manifest to this exact file |
| A4 | **Lineage**: `parent_compiler_path` exists and its recomputed sha256 matches `parent_compiler_sha256` | stage 4 was produced by stage 3 |
| A5 | **Distinct**: sha256(stage4) != sha256(parent) | different entry points; identical bytes means stage 4 produced nothing new |
| A6 | **Not the Rust seed**: `--version` succeeds, is non-empty, and carries no seed banner | see env scrubbing below |
| A7 | A trivial `fn main(): print(1300 + 37)` program actually runs | compared against captured **stdout content**, never exit code — `simple run` exits 0 after a fatal `error: semantic:` |
| A8–A11 | `lint`, `duplicate-check`, `test`, `run` are each recognised subcommands | the full-CLI set stage 3 lacks |
| A12 | **Negative control**: the stage-3 parent must *reject* `lint` | if the parent accepts it, the delta is not a discriminator → **ERROR**, not PASS |

Twelve assertions on a healthy artifact.

### A green `simple test` is never consulted

`.claude/rules/commands.md`: "No pure-Simple binary can lint:
`bootstrap/stage3/simple lint` is `unknown command` (exit 1). `simple test`
GREEN does not prove self-hosted." A green suite is an explicitly documented
false signal here, so the gate never runs the suite and never accepts its
result as evidence. A8–A11 assert only that the `test` **subcommand exists** —
a capability fact about the binary, not a claim about any spec passing. The
run prints `stage4_simple_test_green_consulted=false` to make this auditable.

### Seed-suppression environment is scrubbed

`SIMPLE_BOOTSTRAP=1` and `SIMPLE_RUST_SEED_WARNING=0` both silence the Rust-seed
banner (`src/compiler_rust/driver/src/seed_warning.rs`). Either leaking in from
the caller would let a seed sail through A6, so every probe is launched through
`env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUST_SEED_WARNING`.

### Exit status is never read through a pipe

Every CLI invocation is followed by `_rc=$?` on the very next line. A pipeline's
`$?` is the last stage's status and has produced false greens in this repo before.

## Known gap: no fixpoint evidence exists to verify

This gate deliberately does **not** assert `stage4 == stage3` bytes (that would
be a defect — the stages compile different entry points, and A5 FAILs on it),
nor "stage 4 rebuilds itself and reproduces its own bytes". Neither property is
claimed by the design, and **no script in this repo performs any stage-to-stage
binary comparison** — the only `cmp` in `bootstrap-from-scratch.sh` compares
source fingerprints, not binaries. There is no reproduction receipt to check.
Asserting a fixpoint here would be asserting something the bootstrap never
produces evidence for; recording the gap is the honest move. Each run prints
`stage4_fixpoint_asserted=false_known_gap`. Closing it would require the stage-4
binary to rebuild `main.spl` and a byte comparison of the two outputs — a real
piece of work, not a flag on this gate.

## Verdicts

| verdict | exit | meaning |
|---------|------|---------|
| `PASS — <n> assertion(s) checked, stage 4 self-verified (sha256=… size=… parent=…)` | 0 | safe; `n` is always > 0 |
| `PASS — selftest only, no scan requested (<n> fixture(s) correct)` | 0 | `--selftest-only` |
| `FAIL — <n> assertion(s) checked in <bin>, <k> failed: <names>` | 1 | do not trust the artifact |
| `ERROR — nothing was checked (<why>)` | 2 | could not determine |

ERROR covers every vacuous or unprovable case: missing binary, missing
provenance, no `sha256sum`/`shasum`, no `timeout`/`gtimeout`, zero assertions
evaluated, and a void negative control. **A missing tool or binary is ERROR,
never a pass** — absence of evidence is never evidence.

## Usage

```bash
sh scripts/check/check-bootstrap-stage4-selfverify.shs                 # default target
sh scripts/check/check-bootstrap-stage4-selfverify.shs <stage4-binary>
STAGE4_SELFVERIFY_TIMEOUT=120 sh scripts/check/check-bootstrap-stage4-selfverify.shs
sh scripts/check/check-bootstrap-stage4-selfverify.shs --selftest-only # fixtures only
```

Default target is `build/bootstrap/full/<triple>/simple` — the stage-4 output
path from `build.md`. The triple is taken from `bin/release/*/` when present,
otherwise derived from `uname`.

`--selftest` runs before **every** scan and is fatal; there is no flag that
skips it (`--no-selftest` exists solely for the selftest's own recursive
fixture invocations).

## Fixtures (8, all fatal)

| fixture | expect | shape |
|---------|--------|-------|
| `fixture1_wellformed` | PASS (0) | a well-formed stage-4 artifact with a stage-3-shaped parent |
| `fixture2_rust_seed` | FAIL (1) | a Rust seed masquerading as stage 4 — the redeploy defect `.claude/rules/bootstrap.md` warns about |
| `fixture3_stage3_shaped` | FAIL (1) | a stage-3-shaped binary published as stage 4: rejects `lint`/`test`/`duplicate-check`/`run` with `unknown command`, exactly the documented shape |
| `fixture4_sha_mismatch` | FAIL (1) | provenance records a different binary than the one on disk |
| `fixture5_copy_of_parent` | FAIL (1) | stage 4 byte-identical to its stage-3 parent |
| `fixture6_vacuous_missing_binary` | ERROR (2) | no artifact at all — proves the caller is forced to ERROR, not handed a PASS |
| `fixture7_vacuous_no_provenance` | ERROR (2) | binary present, identity unbindable |
| `fixture8_void_negative_control` | ERROR (2) | the "parent" accepts `lint`, so the capability delta proves nothing |

Fixtures drive **this script recursively**, so they exercise the real `scan()`
rather than a reimplementation of it.

## Validation status

**Fixtures only — no real bootstrap was run.** At the time of writing, a clean
checkout of `origin/main` contains no `build/bootstrap/` directory and no
stage-3 or stage-4 artifact, and Stage 4 is documented as unreachable while the
Stage-3 `ByteOrder` blocker stands (`.claude/rules/bootstrap.md`). The gate has
therefore been proven against its 8 fixtures (all correct) and against the real
default path, where it correctly reports
`ERROR — nothing was checked (stage-4 binary not found: …)` and exits 2. It has
**not** yet been run against a genuine stage-4 binary; do that on the first
successful full bootstrap and record the verdict line here.

## Spec coverage: deliberately skipped

Same reasoning as `deployed_binary_capabilities_gate.md`: this gate's entire
value is spawning a real binary as a subprocess and comparing captured output.
In-process specs cannot reach that, and the `*_gate_spec.spl` pattern only greps
source text for expected strings, which here would vacuously assert this
script's own text. The gate script and its fixtures are the test.
