# Bootstrap lock is keyed on `--output`, but the seed path is not — concurrent bootstraps still collide

**Found:** 2026-07-31, during a `--full-bootstrap --deploy` redeploy on a shared
working copy with several other sessions active.
**Severity:** blocks any bootstrap while another session is executing the seed;
worse, the documented workaround for the symptom would reintroduce a known
0-byte-clobber race.
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Symptom

```
cp: cannot create regular file 'src/compiler_rust/target/bootstrap/simple': Text file busy
```

The run reaches the Rust seed build, then dies at the staging copy
(`scripts/bootstrap/bootstrap-from-scratch.sh:947`,
`cp -p "${rust_authority_profile_dir}/simple${exe_suffix}" "${seed_bin}"`).

Peak `simple` RSS at death was **5 GB** — this is NOT the ~65 GB stage-4 memory
ceiling and NOT the 64 GB `KILL_ANY_MEM_MB` monitor cap. Do not misfile it as an
OOM/cap kill.

`fuser` showed two live holders, both another session's work, ~86 min in:

| pid | cmdline |
|---|---|
| 2120349 | `.../target/bootstrap/simple native-build --backend cranelift --source src/co…` |
| 2120359 | `.../target/bootstrap/simple run src/app/cli/native_build_worker.spl …` |

"Text file busy" (`ETXTBSY`) means the target is being **executed**, not merely
open.

## Root cause: the guard does not cover the shared artifact

The script already has a concurrency guard (~line 191) added after a real
incident:

> Concurrency guard: two bootstraps sharing one `${output_dir}` interleave logs
> and race binary writes (observed 2026-07-24: twin stage2 builds truncated
> each other's linked binary to 0 KB, and `target/bootstrap/simple` was
> clobbered to 0 bytes by the same class of race). Directory-based lock,
> stale-safe.

It locks `"${output_dir}.lock"` and tells a loser to *"Wait for it to finish, or
run with `--output=<other-dir>` for an isolated build."*

**But `seed_bin` is not derived from `output_dir`.** Line 629 hardcodes it:

```sh
seed_bin="src/compiler_rust/target/bootstrap/simple${exe_suffix}"
```

So the escape hatch the guard offers — use a different `--output` — does NOT
isolate the seed. Two bootstraps with different output dirs each acquire their
own lock, then both write the same `src/compiler_rust/target/bootstrap/simple`.
The lock creates a false sense of isolation for exactly the artifact whose
clobbering motivated it.

The same applies to the siblings staged next to it (`simple_native_all`,
`simple_compiler_backfill`, the runtime artifact copied at line 954).

## Why nothing was forced

`CLAUDE.md` documents a `cp` → `.new` + `mv` pattern for this error (used for
MCP servers), and a rename WOULD have succeeded here: replacing a directory
entry does not disturb already-running processes, which keep their old inode.

It was deliberately NOT applied, for two reasons:

1. The other session's build was 86 minutes in and still executing that seed.
   Swapping the binary underneath it means any later `exec` in that build picks
   up a *different* compiler mid-run — a torn build, which is the same class of
   race the 2026-07-24 comment records.
2. Even done atomically, two full bootstraps cannot share one seed path
   coherently. The correct fix is isolation, not a faster overwrite.

## Suggested fix (pick one; do not just swap cp for mv)

1. **Parameterize the seed path by `output_dir`** so `--output=<other-dir>`
   genuinely isolates a build, making the guard's own advice true.
2. **Extend the lock to cover the seed staging directory**, so a second
   bootstrap blocks with the clear "another bootstrap already runs" message
   instead of dying on a bare `cp` error hundreds of lines later.
3. At minimum, **detect `ETXTBSY` and fail with an actionable message** naming
   the holding pids (`fuser`/`lsof`), rather than a raw `cp:` error that reads
   like a permissions or disk problem.

Option 3 is strictly a diagnosis improvement and does not fix the collision.

## Update 2026-07-31 04:10 — the collision recurred, with THREE deploys queued

Later the same session, after the blocking `native-build` finally exited (34 min
wait), `ps` showed **three** independent bootstrap trees all carrying `--deploy`:

| pid | age | invocation |
|---|---|---|
| 3464685 | 17 min | `--pure-simple --full-cli --deploy --no-mcp --jobs=half` |
| 3906074 | 2 min | `--pure-simple --full-cli --deploy --no-mcp` |
| 3983320 | 2 min | `--full-bootstrap --deploy --jobs=4` (this session's) |

None of them is protected from the others: they differ in `--output` (or don't
set it), so each acquires a *different* `${output_dir}.lock` and the guard stays
quiet — while all three target the same hardcoded
`src/compiler_rust/target/bootstrap/simple` **and** the same deploy destination
`bin/release/<triple>/simple`.

This session's run was **deliberately stood down** (SIGTERM) rather than raced,
leaving the oldest to finish. That is a manual workaround for a guard that should
have serialized them automatically, and it only works because a human/agent
happened to run `ps` first. Two `--deploy` runs finishing near-simultaneously can
also interleave writes to the *deployed* binary, not just the staged seed — worth
noting that `--deploy` widens the blast radius beyond what the "Root cause"
section above describes.

Note the killed run's own log ends with `error: failed to fingerprint Rust seed
inputs` after the TERM — a torn shutdown leaves a misleading error, so don't read
that line as the cause of a stand-down.

This raises the priority of suggested fix 2 (extend the lock to the seed staging
dir): fix 1 (parameterize by `output_dir`) would NOT have helped here, since two
of the three runs never passed `--output` at all.

## Update 2026-07-31 05:40 — the provenance gate is incompatible with a mutating shared WC

A later run got **further than any other today** and still produced no binary:

```
Stage 2: Build complete: 727 compiled, 0 cached, 0 failed
         Binary: build/bootstrap/stage2/<triple>/simple (124566 KB)
         Time: 166.4s compile + 58.6s link = 225.0s total
Stage 2: running bootstrap compiler sanity      -> PASS
Stage 3: stage2 -> bootstrap_main.spl           -> succeeded, passed sanity
bootstrap Stage 3 provenance: FAIL (git-head-or-dirty-state-changed-during-bootstrap)
error: refusing Stage 3 without canonical provenance
```

The compile and link were **fine**. Stage 2 and Stage 3 both produced binaries
and passed the sanity gate. The run was rejected purely because the working tree
changed while it ran — in this instance because this session restored 190
origin-present-but-locally-absent files mid-build. That is the gate working
correctly: a binary whose sources mutated mid-build has no verifiable provenance.

**But the failure mode is structural, not a one-off mistake.** This is a shared
working copy with many concurrent sessions. In the ~20 minutes a full bootstrap
needs, origin routinely gains several commits (three landed during this very
run), and any session's edit or restore dirties the tree. The gate demands a
stable git HEAD **and** a clean-state-delta for the whole build window; the
environment cannot reliably supply one.

Consequences worth designing around:
1. Retrying harder does not help — each retry re-enters the same race, and with
   5 concurrent bootstraps observed at once the odds worsen.
2. The gate is not the thing to weaken. Provenance is exactly what makes a
   deployed pure-Simple binary trustworthy.
3. The fix is **isolation**: build from an immutable snapshot (a git worktree or
   export pinned at a specific sha) rather than the live shared WC, so HEAD and
   dirty-state are constant by construction. Note the worktree trap in
   `.claude/rules/bootstrap.md` — a fresh worktree has an empty `build/`, so seed
   the native cache first or pay a full cold rebuild.
4. Until then, a redeploy needs a quiet window: no other bootstraps running, and
   no session editing the tree — coordinate rather than launch opportunistically.

Do NOT restore missing files or edit sources while other bootstraps are running;
that dirties the tree under every one of them.

## Reproduction

1. Start any long `simple native-build` (it executes
   `src/compiler_rust/target/bootstrap/simple`).
2. While it runs, `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`.
3. It builds the Rust seed, then fails at line 947 with `Text file busy`.

Note step 2 succeeds in acquiring its own `${output_dir}.lock` — the guard does
not fire, which is the point of this report.
