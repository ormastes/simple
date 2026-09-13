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
