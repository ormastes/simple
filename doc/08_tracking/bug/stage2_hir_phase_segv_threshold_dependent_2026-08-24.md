# stage2 SEGVs inside the HIR phase on a large fraction of compiler modules (threshold-dependent, not the HIR-cache class)

- **Filed:** 2026-08-24 (Lane P, slice A compile census)
- **Status:** OPEN — characterised, root cause NOT isolated; almost certainly the
  known "stage2 stays miscompiled until a bootstrap redeploy" state recorded in
  §27 rows dated 2026-08-23 (D1 hir-codec, D2 struct-method/string-arm).
- **Compiler:** `build/bootstrap/goal-r3/stage2/x86_64-unknown-linux-gnu/simple`
  (132945096 bytes, 2026-08-24 02:50)

## Symptom

`simple compile <file> --format=smf` dies with SIGSEGV **during** the HIR phase —
the last log line is `[build] hir 0/N step 2/6 ... <module>` and the
`[bootstrap-error-count] ... point=post-lowering` line is never reached. A run
that dies before that line cannot report that phase's errors, so these files are
classified NOLOWER: **their error status is UNKNOWN, not zero.**

Distinguish from the two benign endings that every run of this binary shows:
- `error: hir codec: no Visibility arm for tag -1` (rc=1) after
  `point=post-diagnostics`, and
- SIGSEGV at SMF *emission*, after `point=post-store`.

Both of those occur with lowering complete. NOLOWER is a SEGV strictly earlier.

## Scope measured

Of the 352-file slice (`src/compiler/{00.common,10.frontend,15.blocks,20.hir}`),
NOLOWER is the second-largest class — see the census summary in the Lane P
commit message for final counts.

## What was ruled out

- **Not the HIR cache (D1).** `SIMPLE_HIR_CACHE=0` does not change the outcome:
  `src/compiler/00.common/config.spl` and `.../compilation_context.spl` both still
  SEGV rc=139 with lowering never completing. §27's D1 row notes `SIMPLE_HIR_CACHE=0`
  bypasses that class, so this is a different one.
- **Not any single language construct.** `config.spl` was bisected by prefix:
  `head -392` compiles (rc=1, reaches post-lowering), `head -393` SEGVs. Line 393
  is an ordinary struct field, `    set: LiteralDefinition`. Extracting that field
  — alone, with its neighbours, with a `Dict<text, L>` field, with the field
  renamed — into standalone fixtures reproduces **nothing**; all such fixtures
  compile normally. The trigger is therefore cumulative (module size / symbol
  count crossing a threshold), not a construct, which is the signature of a
  miscompiled compiler rather than of bad input.

## Consequence for any census run on this binary

A NOLOWER file's source cannot be cleared or condemned by this binary. Any claim
of "N clean files" must exclude them explicitly. This is recorded because
treating an early abort as a clean result has already cost this project two
lanes' work.

## Next step

Re-run the census after a bootstrap redeploy lands. If NOLOWER survives a
redeploy, bisect `config.spl` at the HIR phase with a debug build — the prefix
threshold above is a cheap, deterministic entry point.
