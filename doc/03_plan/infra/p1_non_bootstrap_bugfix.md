# The 240 P1 bugs that do not block the bootstrap

Third companion to `offhost_bug_assignment_2026-08-17.md` (where work can happen)
and `p2_p3_bugfix.md` (the non-critical bulk). This one covers the P1s that are
**severe but not on the bootstrap critical path** — they can be worked by anyone,
on any machine, without waiting for a stage-3 binary.

Derived from the 2026-08-17 triage of all 2,630 bug docs against **current
source**: 1,281 live, 628 already-fixed-but-stale (29%), 164 closeable, 59
duplicate.

## The split

`P1/P2/P3` are **severity**, unrelated to bootstrap phase 1/2/3/4 — a name
collision worth stating, because both appear constantly in this repo.

| | count |
|---|---|
| P1 total | 301 |
| ↳ bootstrap-critical (mentions a stage / self-host) | 61 |
| ↳ **not bootstrap-critical — this document** | **240** |

Worklist: `scratchpad/triage/p1_not_bootstrap.tsv`. Columns: `docfile · verdict ·
severity · title · file · line · reproducible_by · evidence`.

## Where they are

| area | count | needs a build? |
|---|---|---|
| `src/compiler` | 69 | **no** — `.spl`, read as source every run |
| `src/compiler_rust` | 62 | yes — cargo, and the shared tree is often unbuildable |
| `src/lib` | 59 | **no** |
| `src/app` | 18 | **no** |
| `src/os` | 13 | mixed |
| `src/runtime` | 8 | yes (C) |

**146 of 240 need no build at all.** The stdlib and pure-Simple compiler sources
are read as SOURCE on every process start (82 `.spl` opens, 0 `.smf`, measured by
strace). Edit and run. Start there.

**33 of 240 are security-flavoured** (crypto, cipher, key, token, signature,
auth, tampering, leakage). Those deserve to go first regardless of build cost.
Two already found and fixed this way were genuinely serious:

- `ed25519` signing branched on every secret scalar bit — and the constant-time
  windowed path its docstring promised **did not exist**; the function signing
  actually called was also branchful.
- P-256 ECDH was non-functional behind a public API that advertised it:
  `ecdh_p256.spl:46` imported eleven symbols from a module that had never
  existed. It was implemented properly rather than stubbed, because the spec is
  `p256_ct_property_spec` — a placeholder field would have turned an honest RED
  into a green that leaks keys by timing.

Still open in that group: `PASETO v4 verification accepts a tampered token`.

## Expect ~29% to be already fixed

Measured repeatedly: individual lanes reported 7-of-8, 10-of-13, and 4-of-17
rows not reproducing. **"Did not reproduce — here is the commit or symbol that
fixed it" is a successful outcome.** It retires the row.

Two rules keep those closes honest:

1. **Classify by CONTENT, never SHA ancestry.** Rebasing rewrites SHAs here;
   commits routinely sit unreachable from `origin/main` while their content is
   present. Grep the fix in current source.
2. **The `evidence` column is not trustworthy on its own.** Two of fourteen rows
   audited carried demonstrably false evidence strings — greps that missed an
   existing fix by a few lines and reported "zero hits". Re-grep before believing
   a row.
3. A wrong close loses a real defect permanently. When unsure, leave it open.

## Collapse before you patch

Confirmed multi-row causes in this set:

- **The 61-bit boxed-int truncation.** The inline form is `v<<3` plus a 3-bit
  tag, so any `|v| >= 2^60` loses its top bits and the matching `>>3`
  sign-extends a different number. This was the root of **three** separately
  filed docs, proven arithmetically:
  `(0x4008000000000000 << 3) mod 2^64 >> 3 = 2251799813685248` — exactly the
  value one of them reported. One doc named the wrong mechanism entirely:
  `print(a)` is correct on the JIT, only `"{a}"` corrupts, so it is the
  tagged-slot boxing boundary, not constant materialization.
- **`rt_fork_parent_wait_bounded`** (`src/runtime/runtime_fork.c`) exits its read
  loop early and silently truncates captured test output repo-wide. Rows about
  missing or short output are probably this one cause.
- **Unresolved `use` imports** were warnings until `1478ca64460`, and the JIT
  fallback swallowed even that. Four instances shipped that way. Rows saying
  "function not found at runtime" are probably this class.

## Method, per bug

Reproduce first and quote the RED `Results: N total, N passed, N failed` line
*before* changing anything. Then fix. Then ship **two** specs — a reproducing
one, and a similar-problem detection spec generalizing to the defect *class* —
and quote the after-line.

The detection spec is not ceremony. It caught a gap its own reproducer missed
**six times** in one session, including one case where the reproducing
assertions passed with the fix *removed*, and another where it reported 9 failure
lines to the reproducer's 1 while the reproducer's own case *passed* — which is
precisely why single-site reproducers kept missing the shape.

## Traps that produce false results

- **`bin/release/simple` is not the compiler.** It is a 2,181-byte
  production-guard wrapper that refuses the deployed seed and exits 1. **88 specs
  spawned it as their tool-under-test**, so the subprocess never ran and every
  assertion failed on empty stdout — a *compiler-shaped* false RED. Any RED from
  a shell-out spec predating `ee794da3a69` is suspect.
- A subprocess spec asserting only `contains()` cannot tell "ran wrong" from
  "did not run". Assert `rc == 0` and non-empty stdout **before** content.
- `process_run` returns a **3-tuple** — rc is `.2`, not `.1`.
- `print` auto-appends `\n`; split `print("PASS ")` + `print(name)` emits
  `PASS\nname` and every `to_contain` fails silently.
- Embedded fixture sources containing `{...}` die with `zero-examples` — the
  *spec's* lexer resolves the interpolation, not the fixture's.
- A spec body runs INTERPRETED; JIT/native defects can never go red from a spec
  body alone. Shell out.
- Never read rc through a pipe: `cmd | tail` yields *tail's* status.
- `rc=143`/`rc=144` with no `Results:` line means **unverified**, not failed.
- `cargo test --bin simple` printed "0 tests, 9 filtered out" and was read as
  green — the tests are in the **lib** target.

## Committing, in a repo with concurrent lanes

- `git commit -- <explicit paths>` only. Never `git add -A` / `commit -a`.
- **`git write-tree` sweeps the shared index** — one lane produced a commit
  deleting other lanes' docs and caught it only in the audit.
- **`commit-tree -p HEAD` is unsafe** — one lane silently reverted two others'
  fixes. Capture `BASE=$(git rev-parse HEAD)`, use `-p "$BASE"`, publish with CAS
  `git update-ref refs/heads/main <new> "$BASE"`, then **always** audit
  `git diff-tree -r --name-status <sha>`.
- Commit per-edit. A parallel session reverted three of one lane's uncommitted
  files to HEAD mid-session.
- **`land.shs` can exit 0 without pushing.** Only `git ls-remote` settles it.

## Suggested order

1. **33 security rows** — regardless of build cost.
2. **146 no-build `.spl` rows** (`src/compiler` 69, `src/lib` 59, `src/app` 18),
   grouped by subsystem so concurrent workers never share a file.
3. **62 `src/compiler_rust` rows** last — they need cargo, and the shared tree
   has repeatedly been unbuildable mid-session (most recently 9 `E0599` errors
   from a half-landed uncommitted change).
