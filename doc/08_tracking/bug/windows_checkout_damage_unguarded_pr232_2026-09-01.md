# Windows-checkout damage landed on main with every guard green (PR #232)

- **Date:** 2026-09-01
- **Status:** guard landed (`scripts/check/check-windows-checkout-damage-push.shs`), damage already repaired by #245/#246
- **Motivating incident:** PR #232 (merged), repaired by PR #245 and PR #246
- **Damaging commit:** `e93d336c05a`

## What happened

A Windows checkout — no `SeCreateSymbolicLinkPrivilege`, `core.autocrlf`
active — wrote three mechanically distinct kinds of damage back into `main`.
Every existing pre-push guard passed, because all of them check tree
structure, conflict text, symbol sets, or source compilability, and none of
them looks at file MODE transitions, symlink target content, or line endings.

1. **Symlink materialization** — 9 paths went `120000 -> 100644`, the link
   target text becoming the file's content:
   `src/app/leak_finder/{__init__,config,discovery,main,memory,reporter,runner,types}.spl`
   and `src/app/lint/main.spl`. git renders a type change as delete+add, so a
   reviewer sees an ordinary small file edit.
2. **Absolute Windows symlink targets** — 4 paths kept mode 120000 (so the
   diff status is `M`, invisible to signature 1) and were rewritten to
   `C:/Users/ormas/dev/simple/src/...`:
   `test/01_unit/app/desugar/app`, `test/01_unit/lib/database/lib`, and their
   `test/unit/**` mirrors.
3. **Newly-introduced CRLF** — `src/compiler_rust/compiler/src/interpreter_eval.rs`
   gained 1860 CRLF lines, against `.gitattributes`' repo-wide `* text=auto eol=lf`.

## Why the existing symlink guard could not catch it

`scripts/check/check-no-new-symlinks-push(.shs)` detects the OPPOSITE
direction — a range that ADDS a symlink, which a jj-managed Windows workspace
then cannot check out. It grandfathers the repo's 93 existing symlinks and
carries a recorded `--expect-new-symlinks` escape, because adding one is a
legitimate repo convention. Destroying a symlink, pointing one at `C:\`, and
Windows-ifying line endings are never legitimate, so none of those properties
transfer. It was also wired to nothing
(`scripts/check/guard_wiring_unwired_baseline.txt:190`). A sibling guard with
no escape hatch was the right shape; folding two opposite-signed predicates
into one script would make both verdicts and both selftests incoherent.

## The guard

`scripts/check/check-windows-checkout-damage-push.shs` — a RANGE guard reading
COMMITTED content only (`git diff --raw` / `git cat-file`), never the shared
working tree. Exemptions: vendored trees (`src/compiler_rust/vendor/**`,
`src/runtime/vendor/**`, `miniaudio.h`, `stb_image.h`, `stb_truetype.h`) are
exempt from the CRLF check because Cargo checksums exact bytes there; a path
whose COMMITTED `.gitattributes` resolves `eol=crlf` (read via
`git check-attr --source=<tip>`, e.g. `bin/simple_lsp_mcp_server.cmd`) stores LF
in the repo and is not damaged. CRLF is grandfathered per file: only a file
that gains CRLF where the base had none is flagged. Binary blobs are skipped
via `git diff --numstat`. Every decision exit status is read into a variable on
the line after the command, never through a pipe. `--selftest` runs first,
unconditionally, and is fatal: 7 real git fixtures (typechange must FAIL,
absolute `C:/` target must FAIL, new CRLF in an owned file must FAIL, CRLF in a
vendored path must PASS, an `eol=crlf`-marked file must PASS, a clean forward
range must PASS, an empty range must examine 0 paths so the caller ERRORs).

## Proof it discriminates

```
$ sh scripts/check/check-windows-checkout-damage-push.shs 'e93d336c05a~1..e93d336c05a'   # rc=1
FAIL — 16 path(s) checked in e93d336c05a~1..e93d336c05a, 14 Windows-checkout-damaged (9 materialized symlink(s), 4 absolute Windows symlink target(s), 1 newly-CRLF file(s)): ...

$ sh scripts/check/check-windows-checkout-damage-push.shs 'HEAD~1..HEAD'                 # rc=0
PASS — 4 path(s) checked in HEAD~1..HEAD, 0 Windows-checkout damage (0 materialized symlinks, 0 absolute Windows symlink targets, 0 newly-CRLF files)

$ sh scripts/check/check-windows-checkout-damage-push.shs 'HEAD..HEAD'                   # rc=2
ERROR — nothing was checked (exit 2)
```

## Wiring

`config/check/must_check_gates.sdn` gains a `push`-tier, `push_blocking=true`
row `push-windows-checkout-damage`, and `scripts/check/check-push-must-pass.shs`
gains the matching dispatch case (an id with no case falls through to
`*) return 2` and ERRORs every push). The pre-push dispatcher
`scripts/check/pre-push-conflict-tree-guard.shs` `exec`s `check-push-must-pass.shs`,
so no third edit is needed. No `doc/08_tracking/check/must_check_db.sdn` row is
added: that ledger's id-set equality is built from `bootstrap`-tier rows only,
and a push-tier row there would recreate the drift PR #250 just fixed.
`sh scripts/check/check-guard-wiring.shs` → `PASS ... 0 NEW unwired`.

## Known pre-existing debt this guard surfaces

Scanning `HEAD~40..HEAD` reports 35 wholly-CRLF files already on `main`
(`tools/jupyter/**`, `test/03_system/tools/jupyter/fixtures/*.ipynb`,
`doc/08_tracking/bug/rt_symbol_census_windows_2026-08-30.md`). These are real
violations of `.gitattributes`, not false positives, and they do not block
normal pushes because the guard only inspects the outgoing range. Normalising
them is separate follow-up work.
