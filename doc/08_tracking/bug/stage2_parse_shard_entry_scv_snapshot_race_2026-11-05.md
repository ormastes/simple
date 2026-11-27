# Stage-2 candidate native-build: parse-shard entry collection races the SCV snapshot (2026-11-05)

**Status:** OPEN. Diagnosed 2026-11-05 on an aarch64 Linux host; reproduction is
flaky (succeeded on retry in one of four runs).

## Symptom

The stage-2 pure-Simple candidate (trust-root bootstrap, cranelift,
aarch64-unknown-linux-gnu, worktree at df48a86ff5a) intermittently fails
`native-build` before any compilation:

```
[first-compile-error] compiler entry '<entry>.spl' collected zero source
files: the entry must be a path to a .spl file ... the path is resolved
relative to the current working directory
[parse-shard] shard=0/2 ... FAILED exit=1 ... retrying
... (all retries fail)
error: HIR aggregate failure; final worker and artifact publication blocked
```

## Observations

- The entry path is correct and resolvable from the invoking CWD; the
  failing children run with a different working directory (the
  `build/scv/snapshots/scv-revision-v1-<hash>/` tree), so the entry
  collection inside the parse shard depends on the SCV snapshot copy of the
  entry file existing at shard-spawn time.
- Failure shape is a race, not a deterministic path defect: the same
  invocation that failed three times (with `--source src/os --source
  src/lib`) succeeded once (entry without os imports but same `--source`
  set), with one full retry cycle (`reclaim: 2 dead shard(s) ... retrying`)
  inside the successful log.
- The Rust seed ran the identical invocation shape without the failure
  (seed probe progressed past parse into MIR/codegen), so the race is in
  the pure-Simple candidate's parse-shard spawn/snapshot ordering, not the
  shared harness script.
- Flaky pre-compilation failures like this can masquerade as codegen or
  admission defects in lane receipts; a failed run should be retried before
  attribution.

## Repro recipe

```
$CANDIDATE native-build --emit-object --backend cranelift --threads 2 \
  --mode one-binary --runtime-bundle core-c-bootstrap \
  --entry test/_probe_root_tmp/<dir>/main.spl \
  --source src/os --source src/lib --output <out>
```

(repeat several times; ~3/4 failed on 2026-11-05).

## Suggested fix direction

Order the SCV snapshot materialization before parse-shard spawn (or pass
the resolved absolute entry path into the shard environment) so entry
collection does not depend on snapshot timing.
