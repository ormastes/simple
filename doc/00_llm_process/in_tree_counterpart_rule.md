# In-Tree Counterpart Rule (research-stage process rule)

## Role

Own one reusable research rule: **before recording an "external port" or
"blocked on a third-party library" row, search the host repository for a
pure-in-language counterpart that already exists.**

This is a research-stage rule. It belongs to whoever writes
`doc/01_research/local/<feature>.md` and to whoever maintains a blocked-row
ledger.

## Why it exists

On 2026-07-27 three long-standing blockers in the host repository were found to
be stale in a single session, each because a working in-tree implementation
existed and nobody had looked:

| Blocker as written | What was actually in the tree |
|---|---|
| "real signature verification blocked on a crypto stack" | 25-file / 12,183-line crypto library with zero stub markers, plus a second 46,404-line tree; Ed25519 passing its RFC 8032 known-answer vectors (15 examples, 0 failures); 60 crypto spec files |
| "OpenSSH port (multi-week)" | 9,576 lines of pure-in-language SSH **server**, wired to real crypto and a real socket facade, advertising curve25519-sha256 / ssh-ed25519 / chacha20-poly1305 / aes-gcm / hmac-sha2. Only the **client** was a foreign-library wrapper |
| "SQLite blocked on a C toolchain" | A ~4,440-line pure-in-language SQL engine with DDL, DML, `WHERE`, and transactions. The C dependency was only in the FFI wrapper |

The common shape: **the blocker names the foreign-linked wrapper, not the
capability.** Everyone downstream then reads it as the capability.

## Procedure

1. Grep `src/**` for the capability noun *and* its common synonyms before
   trusting any blocked row (`sqlite` → also `sql`, `database`, `pure_sql`;
   `openssh` → also `ssh`, `sshd`, `kex`; `crypto` → also the primitive names).
2. Measure what you find: file count, line count, and **stub-marker count**
   (`TODO`, `unimplemented`, `not implemented`). A large tree with zero stub
   markers is a strong signal of real work.
3. **Run its specs.** Present is not proven. Record per-block verdicts.
4. Separate the capability from its foreign-linked wrapper, and rewrite the
   blocked row to name only the part that is genuinely blocked.
5. Watch for **tier shadowing**: if the language resolves a module family in a
   fixed order, an in-tree copy may be unreachable. Confirm which copy executes
   before editing or deleting either.

## Output

- Correct the blocked row in the tracking ledger.
- Add or update the host-repository counterpart map so the next session does not
  re-derive this. In this host that map is
  `doc/07_guide/lib/database/sqlite_counterparts.md` plus the *In-Tree
  Counterpart Rule* section of `doc/glossary.md`.
- Add the user-facing alias to `doc/00_llm_process/llm_wiki.md` when ordinary
  terminology differs from the implementation name. In particular, “Simple
  embedded DB” and “Simple SQLite” resolve to `PureDatabase` / `pure_sql`, not
  to `sqlite_sffi` or `SdnDatabase`.

## Step 3 in practice: what "run its specs" must actually read (2026-08-05)

Step 3 is where this rule most often produces a wrong answer, because the
harness reports success in several shapes that are not one.

- **Score the verdict line, never the exit code.** `bin/simple test` prints
  `Results: N total, M passed, K failed`; `bin/simple run` prints an
  ANSI-wrapped `N examples, M failures` (singular `1 failure`). They are
  different grammars and neither pattern matches the other's output. The
  strongest signal is the per-file line
  `SPEC FILE VERDICT: <path> declared>=N executed=N passed=N failed=N dropped=N`
  (`src/compiler_rust/driver/src/cli/basic.rs:144`).
- **Exit status is fail-open here specifically.** An unresolved `use` is only a
  WARN and still exits 0 — so a counterpart tree whose specs no longer import
  their subject will "pass". That is the exact failure this rule is meant to
  catch, inverted: instead of a stale blocker, you get a fabricated unblock.
- **Never `tail -1`**, and never conclude from a run that produced no output:
  exit 143 (≈60s CPU guard) and exit 255 + `Process timed out` (600s daemon cap)
  are kills, not verdicts.
- **A vacuous spec passes.** A bare `assert` is inert; `check(true)` is a real
  assertion with nothing to say. Read what the assertions can vary over before
  recording "specs pass" as evidence of a working counterpart.
- Full list: `.claude/skills/spipe.md` §"Reading the verdict — how a spec run
  lies to you".

## Constraints

- Do not delete the foreign wrapper just because a native counterpart exists —
  it may be the faster or better-tested path on the host platform. Record which
  is canonical for which target.
- Do not mark a row unblocked on the strength of file size alone. A passing
  known-answer test or spec run is the minimum evidence.
- **Size never indicts either, and step 2's line/stub counts cut both ways.** A
  file measuring 38% of its historical size was a legitimate split, and a
  294-byte file was a deliberate facade over a 123 KB core. Small does not mean
  stub; large does not mean real. Size opens an investigation; it never closes
  one.
- **Validate any census before believing it.** Raw false-positive rates measured
  on this host ran 83.9% (arity), 74% (a constant scan really counting
  deliberate `FAILMARK` sentinels), 46.2% (dead code), and 31.5% (tautology) —
  bare-name collisions were the recurring cause. `ugrep` is the default `grep`
  here, so pin `/usr/bin/grep`, anchor on qualified names, and exclude generic
  identifiers. Reproduce a fact you already know before trusting the facts you
  don't.
- **Unanimity is weak evidence on its own.** When every call site disagrees with
  a declaration in the same way, that counts against the declaration *only* if
  the declaration independently shows stub signs; two counterexamples on this
  host had unanimous call sites and a correct declaration. Ask which side is
  internally consistent, not which side is more numerous.
- **Beware duplicated trees when counting.** `test/unit/` is a frozen legacy
  mirror of `test/01_unit/` (874 shared pairs differ, ~33% with different
  example counts) and `test/` holds 14 symlinks into `src/`. A naive census that
  walks both, or follows links, double-counts — this made 27% of one census's
  "test files" `src/` aliases. This is step 5's tier-shadowing hazard in its
  measurement form.
