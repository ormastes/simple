# Site 16: the Stage-2 compatibility manifest can never be written on a seed-built Stage 2

- **Status:** OPEN (2026-09-13) — needs an owner decision, NOT a one-line fix.
- **Lane:** macOS `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`,
  worktree `agent-aee4c61a47998a6a9`, run 29 (carrying the site-13/14/15 fixes).
- **Severity:** the Stage-2 blocker that succeeds site 15. Not caused by it —
  masked by it, and by 14 and 13 before that: no macOS run had ever got this far.

## The verdict

```
Stage 2: admitted parent → bootstrap_main.spl
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
error: Stage 2 did not publish its compatibility manifest
```

Everything before this passed: the candidate built, both capability probes
passed, the admission receipt published, and — new this run — the producer-bound
parent receipts published (site 15 cleared; that error is gone).

## Measured cause — the writer lives in the pure-Simple driver, the producer is the Rust seed

`bootstrap-from-scratch.sh:3288` is fail-closed on the file existing:

```sh
[ -f "${stage2_compatibility_manifest_absolute}" ] || {
  echo "error: Stage 2 did not publish its compatibility manifest" >&2
  exit 1
}
```

The lane does set the write hook on the Stage-2 build invocation
(`:2848`, `SIMPLE_PHASE2_COMPATIBILITY_MANIFEST_WRITE=<path>`), and a writer for
it does exist — `driver_emit_phase2_compatibility_manifest_v1`, called at
`src/compiler/80.driver/driver_aot_native_output.spl:2051-2063`.

But that writer is **pure-Simple**, and this lane's Stage 2 is built by the
**Rust seed** — the lane says so itself:

```
mode:     manual (seed → bootstrap_main → bootstrap_main)
```

and the seed has no implementation of the hook at all:

```
$ /usr/bin/grep -rn "PHASE2_COMPATIBILITY_MANIFEST" src/compiler_rust/
(no matches)
```

Corroborating: the Stage-2 build log contains **zero** `[M3 ledger]` or
manifest lines, and no `phase2-compatibility.manifest` exists anywhere under the
bootstrap output tree.

So the env var is set on a producer that ignores it, and the check then fails
closed on its absence. On this lane the gate is unsatisfiable by construction.

## Why this is not a one-liner, and what the options are

Both plausible repairs change a contract, so this needs an owner rather than a
drive-by fix:

1. **Teach the seed to write the manifest.** Correct if the manifest is meant to
   describe any Stage-2 producer. Cost: a Rust change mirroring
   `driver_emit_phase2_compatibility_manifest_v1`, and the two emitters must then
   stay byte-compatible — a new dual-implementation obligation.
2. **Scope the check to a pure-Simple-produced Stage 2.** Correct if the manifest
   is by design an artifact only the self-hosted driver can produce. Cost: the
   condition must be a POSITIVE fact about the producer (e.g. the lane recorded
   that Stage 2 was built by a pure-Simple compiler), never "the file is missing,
   so skip" — that inverts a fail-closed gate into a fail-open one, which is the
   exact failure mode `.claude/rules/vcs.md` documents for the seed-build guard.

Do NOT "fix" this by deleting the check or by `touch`ing the manifest.

## State of the lane at this site

Stage 2 built, both capability probes PASS, admission receipt and parent receipts
published; Stage 3, the full CLI and Stage 4 were never reached. Nothing was
deployed. The candidate that reached this point:
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple`.

## RESOLVED 2026-09-13 — option 2 (producer-scoped gate), with the option-1 path measured dead

Option 1 ("teach the seed to write the manifest") was rejected on evidence, not
preference: the writer returns `m2-receipt-<reason>`
(`driver_aot_native_output.spl:415-418`) unless
`reverse_reference_read_current_admitted_v1`
(`80.driver/cache/reverse_reference_receipt.spl:243`) finds a generation pointer
and `<digest>.receipt` under the Phase-2 cache root. Those receipts are written
only by that pure-Simple module — `grep -rl 'reverse_reference|current-admitted'
src/compiler_rust/` is EMPTY. So "minimal emission mirroring the writer" is
actually a port of the whole M2 reuse-admission authority into Rust, as a second
authoritative implementation of a trust mechanism. Running the pure-Simple writer
inside the Stage-2 candidate against a seed-written cache fails at the same line,
so that variant is unsatisfiable too.

Not macOS-specific: `bootstrap-from-scratch.sh` pins `can_full_bootstrap=0`
("Force manual bootstrap"), so on EVERY OS Stage 2's producer is the admitted
Rust seed unless `--stage2-parent`/`--pure-simple` supplies an admitted
pure-Simple parent. The gate was only ever satisfiable on that producer; no
Linux run on the default lane ever crossed it either.

The gate is kept and scoped on a POSITIVE producer fact that the script already
computes BEFORE Stage 2 runs (`bootstrap_stage2_parent_override`, set only after
`admit-stage2-parent.shs` verified an admitted pure-Simple release, plus the
`--pure-simple` flag) — never "the file is missing, so skip".

- `scripts/check/lib/bootstrap-stage3/phase2-compat-manifest.shs` —
  `bootstrap_phase2_compat_producer_kind` and
  `bootstrap_phase2_compat_manifest_gate`, 12 fatal selftest fixtures.
- `scripts/check/check-stage2-compat-manifest-gate.shs` — wrapper; selftest runs
  first and is fatal. Verdict is the last stdout line: PASS 0 / FAIL 1 / ERROR 2.
- pure-simple producer: manifest must exist AND carry the frozen schema header
  `simple-phase2-phase3-compatibility-v1`
  (`phase_compatibility_manifest.spl:166`) — strictly stronger than the old bare
  `[ -f ]`. rust-seed producer: absence is admitted only with a
  `<manifest>.not-published` evidence record naming the producer; a manifest that
  IS present is still schema-checked.
- Fail-closed downstream is unchanged: Stage 3 still receives
  `SIMPLE_PHASE2_COMPATIBILITY_MANIFEST_READ` (that env vector is bound into
  `bootstrap_stage3_args_sha256` and the canonical env-name lists, so it must not
  change); `driver_admit_phase2_compatibility_manifest_v1` refuses the absent
  path, `[M3] reject manifest` is printed, and Phase 3 does a clean build with
  ZERO Phase-2 reuse. No reuse is ever admitted without a manifest.
