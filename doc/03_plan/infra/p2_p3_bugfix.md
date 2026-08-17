# Fixing the 980 P2/P3 bugs

Companion to `offhost_bug_assignment_2026-08-17.md`. That document answers
*where* work can happen; this one answers *how* to work the non-critical bulk.

Derived from the 2026-08-17 triage of all 2,630 bug docs against **current
source** (not the prose in the docs): **1,281 live**, 628 already-fixed-but-stale
(29%), 164 closeable, 59 duplicate. Of the live set, 301 are P1 — those are
covered elsewhere. This plan covers the remaining **980**.

## Severity, since the names collide with bootstrap stages

`P1/P2/P3` are **severity**, unrelated to bootstrap phase 1/2/3/4. A bug can be
P1 *and* stage-3-blocking, or P1 and irrelevant to the bootstrap.

| | meaning | count |
|---|---|---|
| P1 | wrong results, data loss, security, or blocks the bootstrap | 301 |
| **P2** | a real defect, but contained or with a workaround | **730** |
| **P3** | cosmetic, docs, tooling, policy | **250** |

## Where they live

| area | P2+P3 |
|---|---|
| `src/lib` | 257 |
| `src/compiler` | 212 |
| `src/app` | 127 |
| `src/compiler_rust` | 121 |
| `src/os` | 80 |
| `scripts/check` | 48 |
| `test/01_unit` | 33 |
| `src/runtime` | 23 |

Two numbers decide the order of attack:

- **594 of 980 are pure `.spl` under `lib`/`app`/`compiler` — these need NO
  BUILD.** The stdlib and compiler sources are read as SOURCE on every process
  start (82 `.spl` opens, 0 `.smf`, measured by strace). Edit and run. No cargo,
  no bootstrap.
- **487 of 980 already name a reproducible_by spec.** Those start with a
  measurement instead of an investigation.

The intersection — pure-`.spl` **and** already has a spec — is where to begin.

## Expect a third of them to be already fixed

Measured repeatedly across every lane that checked: **29% of the corpus was
already fixed and merely mislabelled.** Individual lanes reported 7-of-8,
10-of-13, and 4-of-17 rows not reproducing. P2 is where the triage's
when-unsure rule dumped the most uncertainty, so the rate is likely *higher*
here than in P1.

**"Did not reproduce — here is the commit or symbol that fixed it" is a
successful outcome.** It retires the row. Closing 300 stale rows with evidence
is worth more than 30 shallow fixes, and it is much cheaper.

Two rules make those closes trustworthy:

1. **Classify by CONTENT, never by SHA ancestry.** Constant rebasing rewrites
   SHAs in this repo; commits routinely sit unreachable from `origin/main` while
   their content is present. Grep the fix in current source.
2. **A wrong close loses a real defect permanently.** When unsure, leave it open.

## Working method, per bug

1. **Reproduce first.** Quote the RED `Results: N total, N passed, N failed`
   line *before* changing anything.
2. **Fix.**
3. **Ship two specs** — a reproducing one, and a similar-problem detection spec
   that generalizes to the defect *class*.
4. **Quote the after-line.**

The detection spec is not ceremony. It caught a gap its own reproducer missed
**six separate times in one session**:

- `occurs_check` — the first fix looked right and the `T=[T]` reproducer passed
  it; `TYPE_VAR_BASE`(50000) > `TYPE_NAMED_BASE`(10000) meant every unbound type
  var fell into the named-type arm and over-reported. Only the over-report guards
  caught it.
- u64 ordering — detection failed 6 cases to the reproducer's 3, covering
  unsuffixed `u64 > 0` (Int-typed), the commoner way to write it.
- ed25519 — the reproducer audited only `ed_scalar_mul`; detection swept every
  scalar-mul entry point and found the function *signing actually calls* was also
  branchful, despite a docstring promising constant time.
- A wide-int probe reported **9 FAIL lines** where two single-site reproducers
  each reported one — and `field_i64_max` *passed*, which is exactly why
  single-site reproducers kept missing the shape.

## Collapse before you patch

Several P2 clusters share one cause. Confirmed examples:

- One runtime boxing bug (`core.rs`, 61-bit `v<<3|TAG`) was the root of **three**
  separately-filed docs. The inline boxed-int form gives a 61-bit signed payload,
  so any `|v| ≥ 2^60` loses its top bits. Proof:
  `(0x4008000000000000 << 3) mod 2⁶⁴ >> 3 = 2251799813685248`, exactly the value
  a second doc reported.
- `rt_fork_parent_wait_bounded` (`src/runtime/runtime_fork.c`) exits its read loop
  early and **silently truncates captured test output repo-wide**. Rows about
  missing or short output are probably this one cause, not N bugs.
- Unresolved `use` imports were warnings until `1478ca64460`, and the JIT
  fallback swallowed even that — four instances shipped that way, one hiding a
  completely missing P-256 implementation. Rows saying "function not found at
  runtime" are probably this class.

Report a collapse explicitly. It is worth more than the individual patches.

## Traps that produced false results (all measured)

**Vacuous specs — three shipped, one was guarding crypto:**

- `ed25519_ct_property_spec` searched the wrong file (`ed25519.spl` while the
  function lives in `ed25519_ops.spl`), so `find()` returned −1 and it could
  never pass *or* catch a regression.
- A subprocess spec asserting only `contains()` cannot distinguish "ran wrong"
  from "did not run". **Assert rc == 0 and non-empty stdout before asserting
  content.**
- Embedded fixture sources containing `{...}` die with `zero-examples` before any
  example runs — the *spec's* lexer resolves the interpolation, not the
  fixture's.

**`bin/release/simple` is not the compiler.** It is a 2,181-byte production-guard
wrapper that refuses the deployed seed and exits 1. **88 specs spawned it as
their tool-under-test**, so the subprocess never ran and every assertion failed
on empty stdout — presenting as a *compiler-shaped* false RED. Any RED from a
shell-out spec predating `ee794da3a69` is suspect.

**Other measured traps:**

- `process_run` returns a **3-tuple** — rc is `.2`, not `.1`.
- `print` auto-appends `\n`, so split `print("PASS ")` + `print(name)` emits
  `PASS\nname` and every `to_contain` fails silently.
- Never read rc through a pipe: `cmd | tail` yields *tail's* status.
- `cargo test --bin simple` printed "0 tests, 9 filtered out" and was read as
  green — the tests are in the **lib** target. Check the executed count.
- A spec body runs INTERPRETED. JIT/native defects can never go red from a spec
  body alone — shell out to a subprocess.
- `rc=143`/`rc=144` with no `Results:` line means **unverified**, not failed.
- Use `--timeout <n>`; `SIMPLE_TIMEOUT_SECONDS` still misbehaves.
- Each `it` in a shell-out spec spawns a full compiler launch against the
  daemon's 120s budget.

## Committing in this repo

Concurrent lanes make the obvious commands unsafe:

- `git commit -- <explicit paths>` only. **Never** `git add -A` / `commit -a`.
- **`git write-tree` sweeps the shared index** — one lane produced a commit
  deleting other lanes' docs that way and caught it only in the audit.
- **`commit-tree -p HEAD` is unsafe** — one lane silently reverted two other
  lanes' fixes. Capture `BASE=$(git rev-parse HEAD)`, use `-p "$BASE"`, publish
  with CAS `git update-ref refs/heads/main <new> "$BASE"`, and **always** audit
  `git diff-tree -r --name-status <sha>` shows only your paths.
- Commit per-edit, not batched — a parallel session reverted three of one lane's
  uncommitted files to HEAD mid-session.
- **`land.shs` can exit 0 without pushing.** Verify with `git ls-remote`.

## Suggested order

1. **Stale-close sweep** over the 487 rows that name a spec — cheapest, and at a
   ~29% hit rate it should retire ~140 rows for little effort.
2. **The 594 no-build `.spl` rows**, grouped by subsystem so concurrent workers
   never share a file.
3. **`src/compiler_rust` (121)** last — those need a cargo build, and the shared
   tree has repeatedly been unbuildable mid-session.

`scripts/check` (48) and `test/01_unit` (33) are good parallel work for anyone
blocked on a build: they need no compiler at all.
