# Stage-3 self-verification gate

`scripts/check/check-bootstrap-stage3-selfverify.shs`

Validates the **output** of a bootstrap Stage 3 (self-hosted) build. It never
starts a bootstrap; it is a consumer-side gate that can be run at any time after
a stage has been produced, and it fails closed when nothing was produced.

## Why it exists

Before this gate, "Stage 3 passed" was inferred from the bootstrap wrapper's
exit code plus a provenance manifest that the wrapper wrote itself. Nothing
outside the wrapper rehashed the live artifacts, asserted the self-host chain,
or ran the Stage-3 binary. An exit code is not evidence.

## Relationship to sibling gates (no duplication)

| Script | Scope | Overlap |
|---|---|---|
| `scripts/check/lib/bootstrap-stage3/manifest-verify.shs` | Manifest **shape**: every key singular, sha fields well-formed, canonical lane paths, stage2/stage3 sha rehash. A library, not a CLI, with no verdict line. | Reused, not re-implemented — invoked via `--full-provenance`. |
| `check-bootstrap-stage2-struct-receiver.shs` | Stage-2 capability probe (builds a fixture with stage2). | None — different stage. |
| `check-post-bootstrap-stage4-sspec.shs` | Stage-4 **candidate** binary + adjacent provenance. Assumes Stage 3 is already trusted. | None — this gate supplies the trust it assumes. |
| `check-bootstrap-essential-tools-smoke.shs` | Stage-4 full CLI (`test`/`lint`/`duplicate-check`). | Must **never** be pointed at Stage 3, which has none of those commands. This gate asserts that boundary instead. |
| `check-bootstrap-portability.shs`, `check-bootstrap-platform-handoff-readiness.shs`, `bootstrap-diagnostic-sweep.shs` | Portability/handoff/diagnostics. | None. |

## What it asserts

| # | Assertion | Rationale |
|---|---|---|
| A1 | Stage-3 provenance manifest exists, is a regular non-symlink file | vacuity guard |
| A2 | `schema=simple-bootstrap-stage3-provenance-v*` | manifest is the expected artifact |
| A3 | `status=pass` | recorded verdict, not an inferred one |
| A4 | Stage-3 binary exists at `stage3_path`, regular, non-symlink, executable, non-empty; **path, size, and sha256 are printed as a receipt** | success is never inferred from an exit code |
| A5 | live sha256 of the Stage-3 binary equals `stage3_sha256` | artifact was not swapped or truncated after the build |
| A6 | Stage-2 binary exists and its live sha256 equals `stage2_sha256` | the producer is pinned too |
| A7 | **Self-host chain**: the `executable:` line of the Stage-3 command transcript equals `stage2_path` | Stage 3 was produced *by* Stage 2, not by the seed or a stray compiler |
| A8 | **Same program**: Stage-2 and Stage-3 transcripts name the same `--entry` | both stages compiled `bootstrap_main.spl`; a fixpoint claim over two different programs is meaningless |
| A9 | **Stage 3 is not a byte-copy of Stage 2** (`stage3_sha256 != stage2_sha256`) | see the fixpoint note below |
| A10-A12 | `stage2_sanity_status`, `stage2_receiver_status`, `stage3_sanity_status` are all `pass` | the wrapper's own recorded stage sanity |
| A13 | Stage 3 runs: `--version` exits 0 with non-empty output | functional, live |
| A14 | That output carries no Rust-seed banner (`Rust-built`, `bootstrap seed only`) | the classic "freshly copied seed masquerading as self-hosted" failure |
| A15 | **Capability boundary**: `stage3 lint` exits non-zero | Stage 3 is the minimal bootstrap entry (`compile`/`native-build` only); `lint` is a documented `unknown command`. Asserting the refusal keeps a green verdict from ever being read as full-CLI evidence. |
| A16 | **Functional**: Stage 3 `native-build`s a trivial program and the produced executable runs and prints the expected line (`--no-deep` to skip) | end-to-end proof the binary compiles and its output executes |
| A17 | *(optional)* `--fixpoint-binary PATH` is byte-identical to the Stage-3 binary | strict fixpoint |
| A18 | *(optional)* `--full-provenance` delegates to `bootstrap_stage3_verify_manifest` | full manifest authority |

## The fixpoint property — what the design actually guarantees

The naive reading of "3-stage self-compilation" is *stage2 output ≡ stage3
output, byte for byte*. **That does not hold here, and asserting it would be
wrong.** Per `doc/07_guide/compiler/build.md` § Bootstrap Stages, Stage 2 is
emitted by the **Rust seed** and Stage 3 is emitted by the **Stage-2 compiler**:
two different code generators compiling the same entry. Byte-identity between
them is not claimed by the design and is not expected.

So the gate asserts the properties the design *does* guarantee:

- **Producer chain (A7)** — Stage 3's transcript proves Stage 2 was the compiler
  that produced it. This is the actual self-hosting claim.
- **Same entry (A8)** — both stages compiled the same program.
- **Inequality (A9)** — because the producers differ, byte-*equality* would mean
  Stage 3 was copied rather than compiled (`cp stage2 stage3`). The guaranteed
  direction is therefore inequality, and that is what is enforced.

The strong fixpoint — *stage3 recompiling its own entry reproduces stage3 byte
for byte* — is real but requires a fourth build of `bootstrap_main.spl`. The
gate asserts it only when that artifact is handed to it via
`--fixpoint-binary`; otherwise it prints
`stage3_strict_fixpoint=not_supplied` and makes no claim about it.

## Verdict table

| verdict | exit | meaning |
|---|---|---|
| `PASS — <n> assertion(s) checked, stage3 self-verified at <manifest>` | 0 | safe; `n` is always > 0 |
| `PASS — <n> selftest fixture(s) checked, gate behaves as specified` | 0 | `--selftest` only |
| `FAIL — <n> assertion(s) checked, first failure: <reason>` | 1 | do not trust this Stage 3 |
| `ERROR — nothing was checked` | 2 | no manifest / nothing verifiable; never a pass |

A run that examined 0 assertions is always ERROR. Absence of a Stage-3 artifact
is ERROR, never a pass. Every command exit status is read directly into a
variable on the line after the invocation — never through a pipe.

## Selftest fixtures (fatal, run before every scan)

| fixture | expected | replays |
|---|---|---|
| `healthy` | PASS (exit 0) | a well-formed stage output, including the deep compile+run path |
| `tampered` | FAIL | Stage-3 bytes changed after the manifest was written (sha mismatch) |
| `copy_of_stage2` | FAIL | Stage 3 is a byte-copy of Stage 2 and its transcript names a producer that is not Stage 2 |
| `no_version` | FAIL | Stage-3 binary exists but is dead (`--version` exits 3) |
| `seed_banner` | FAIL | Stage 3 is really a Rust seed (banner in `--version`) |
| `lint_accepted` | FAIL | Stage 3 answers `lint` with exit 0 — a false full-CLI capability claim |
| `vacuous` | ERROR (exit 2) | empty fixture directory: the caller is forced to ERROR, proving non-vacuity |

## Usage

```sh
sh scripts/check/check-bootstrap-stage3-selfverify.shs --selftest
sh scripts/check/check-bootstrap-stage3-selfverify.shs            # default output dir
sh scripts/check/check-bootstrap-stage3-selfverify.shs \
    --manifest build/bootstrap/stage3/<platform>/provenance.env \
    --fixpoint-binary <stage3-recompiled> --full-provenance
```

## Validation status

As of the commit that adds this gate, **no real Stage-3 artifact existed on this
host** (`build/bootstrap/stage3/` is absent; the Stage-3 self-host blocker in
`.claude/rules/bootstrap.md` is still open). The gate was therefore validated
**against fixtures only**, plus a live no-artifact run that correctly produced
`ERROR — nothing was checked` (exit 2). It has not yet been run against a
genuine Stage-3 binary; the first real bootstrap that reaches Stage 3 should run
it with `--full-provenance` and record the verdict line.
