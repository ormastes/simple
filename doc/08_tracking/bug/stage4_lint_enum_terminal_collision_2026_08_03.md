# Stage 4 lint enum terminal collision

Status: claimed
Severity: P1 bootstrap blocker
Owner: pure-Simple HIR materialized payload dependency resolution
Fix owner: `/root` at source revision `4505aec902a`

## Exact failure

The canonical no-stub x86 Stage 4 run loaded 2,116/2,116 sources, retained all
1,431 module surfaces, and completed 43 HIR modules before failing declaration
of `compiler.tools.lint.main`. `LintLevel` and `LintCategory` each report the
same deterministic terminal conflict twice:

- `compiler.tools.lint._LintMain.config_and_model::{item}::enum`
- `lib.nogc_sync_mut.tooling.easy_fix.types::{item}::enum`

The last green module was `compiler.tools.formatter.main`. The command exited 1
after 37m57s at 2,634,216 KiB peak RSS. No Stage 4 candidate was produced.

Retained evidence:

- `/tmp/simple-stage4-bootstrap-4505-20260803/output/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- `/tmp/simple-stage4-bootstrap-4505-20260803/progress.log`
- `/tmp/simple-stage4-bootstrap-4505-20260803/output/bootstrap-build-progress.events`

## Prior evidence

`doc/08_tracking/bug/enum_bare_name_collision_enumeration_2026-08-01.tsv`
already classifies the source declarations as duplicated/identical. That static
inventory does not decide whether the correct fix is declaration consolidation,
an explicit adapter, or import-local disambiguation; the compiled HIR reproducer
must decide before source edits.

## Required repair and evidence

1. Trace the exact `compiler.tools.lint.main` import/re-export route and prove
   whether both terminal enums are semantically identical or merely
   name-compatible.
2. Fix the smallest pure-Simple owner. Prefer one canonical shared lint contract
   with explicit adapters over weakening terminal collision checks.
3. Add an exact compiled reproducer for both enums plus an adjacent case where
   same-spelled but genuinely different enum terminals still fail closed.
4. Rerun only the focused failed shard first, rebuild/admit Stage 3 once, then
   resume the canonical Stage 4 cache-backed build within the three-cycle cap.
5. Keep the conflict diagnostic fail-closed; no import reshuffling, local type
   renaming, Rust-seed fallback, stub generation, or source exclusion may be
   accepted as the root fix.

---

## RE-VERIFICATION 2026-08-17 (c_splmisc lane) — ALREADY FIXED BY CONTENT. Close.

Classified by CONTENT, not by SHA (SHAs are rewritten constantly in this repo
and prove nothing in either direction).

`src/compiler/90.tools/lint/_LintMain/config_and_model.spl` today contains
**zero** declarations of `enum LintCategory`:

```
$ /usr/bin/grep -c '^ *enum LintCategory' src/compiler/90.tools/lint/_LintMain/config_and_model.spl
0
$ /usr/bin/grep -n 'LintCategory' src/compiler/90.tools/lint/_LintMain/config_and_model.spl
19:use std.tooling.easy_fix.types.{EasyFix, LintLevel, LintCategory}
723:# A second local `enum LintCategory` used to be declared here, colliding with
731:    category: LintCategory
737:    fn new(code: String, level: LintLevel, category: LintCategory, message: String) -> Lint:
```

Only the single import at line 19 survives. Lines 722-726 are an explicit
tombstone comment recording the removal and its rationale (the two declarations
had byte-identical variant sets, so the local one was pure duplication — the
same defect already fixed for `LintLevel`). Lines 731 and 737 are *uses* of the
imported type, not declarations.

**The triage evidence column for this row is FALSE.** It asserted "line 737
declares enum LintCategory"; line 737 is the signature
`fn new(code: String, level: LintLevel, category: LintCategory, message: String) -> Lint`
— a type reference. Anyone re-triaging from that column will reopen a dead bug.

No code change made. No spec written: a content-close is not a fix, and the
project's two-spec rule applies to fixes.

Residual worth stating: the resolution chosen was deduplication (single
canonical import), which satisfies remediation item 5 (the fail-closed terminal
collision diagnostic was NOT weakened). Remediation item 4 — the canonical
cache-backed Stage 4 rebuild — was NOT run here: a user bootstrap was live and
`build/bootstrap/**` was off-limits.

---

## INDEPENDENT re-verification 2026-08-17 (bug-triage lane) — CONFIRMS the close

The stamp above was NOT taken on trust: re-verification stamps in this tracker
have been wrong on a material fraction of the rows they touch, so the content
claim was re-derived from scratch. It holds.

Exhaustive declaration census over both implicated trees (GNU
`/usr/bin/grep`, not the ambient ugrep, which honours `.gitignore`):

```
$ /usr/bin/grep -rn "enum LintCategory\|enum LintLevel" \
    src/compiler/90.tools/lint/ src/lib/nogc_sync_mut/tooling/easy_fix/
src/compiler/90.tools/lint/_LintMain/config_and_model.spl:723:# A second local `enum LintCategory` used to be declared here, colliding with
src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:8:pub enum LintLevel:
src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:13:pub enum LintCategory:
```

**Exactly ONE declaration of each enum survives, and both are in the single
canonical module `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl`.** The only
hit inside the lint tree is a comment. Every other `LintLevel`/`LintCategory`
occurrence in `config_and_model.spl` (lines 19, 317-326, 434-457, 477, 523-533,
597-609, 730-737) is an import or a type *reference* — never a declaration. A
terminal collision between two declarations is therefore not constructible from
current source: there is no second terminal to collide with.

Also linted the surviving canonical declaration site (one file at a time — cost
here is superlinear in declaration content, and batching two files has exceeded
600s where one took 119s):

```
$ sh scripts/check/lint-cached.shs src/lib/nogc_sync_mut/tooling/easy_fix/types.spl
PASS — 1 file(s) checked (0 cached, 1 linted)
```

**Row RETIRED.** Caveats carried forward unchanged, and deliberately not
papered over: (a) the 2026-08-03 runtime failure itself was NOT re-run — no
self-hosted stage2/stage3 binary exists in this checkout, `bin/simple` is the
Rust seed (mtime 2026-08-16 22:59) which never reads `src/compiler/**.spl` as
compiler logic, and `build/bootstrap/**` was off-limits to this lane; the close
rests on the collision being unconstructible from source, which is the stronger
claim anyway. (b) Remediation item 5 is satisfied — the fail-closed terminal
collision diagnostic was NOT weakened; the fix was deduplication. (c) No specs
added: this row is retired as a content-close, not a fix, so the two-spec rule
does not attach. (d) The `evidence` column for this row remains FALSE (it cites
line 737, a function signature, as a declaration) — do not re-triage from it.

### Third-lane census widening 2026-08-17 (worker W7) — retirement holds

Both stamps above scoped their census to two directories. Widened to the whole
owned source tree, `.spl` only, GNU grep, anchored to a declaration:

```
$ /usr/bin/grep -rn --include=*.spl -E "^[[:space:]]*(pub )?enum (LintCategory|LintLevel)\b" \
    src/compiler src/lib src/app src/os
src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:8:pub enum LintLevel:
src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:13:pub enum LintCategory:
```

Two hits, one module — no third terminal exists anywhere in `src/` to collide
with. Retirement confirmed on a strictly larger scan than either prior stamp.

---

## Concurrent variant landed on origin/main (merged 2026-08-17, both sides kept)

Neither side was a superset of the other, so this appendix preserves the
origin/main text verbatim rather than dropping evidence. Owning lane should
reconcile the two halves.

# Stage 4 lint enum terminal collision

Status: fix implemented — focused native and full Stage 4 replay pending
Severity: P1 bootstrap blocker
Owner: pure-Simple lint contract ownership
Fix owner: `/root/priority_lint_enum` at source revision `1a2fd808fc`

## Exact failure

The canonical no-stub x86 Stage 4 run loaded 2,116/2,116 sources, retained all
1,431 module surfaces, and completed 43 HIR modules before failing declaration
of `compiler.tools.lint.main`. `LintLevel` and `LintCategory` each report the
same deterministic terminal conflict twice:

- `compiler.tools.lint._LintMain.config_and_model::{item}::enum`
- `lib.nogc_sync_mut.tooling.easy_fix.types::{item}::enum`

The last green module was `compiler.tools.formatter.main`. The command exited 1
after 37m57s at 2,634,216 KiB peak RSS. No Stage 4 candidate was produced.

Retained evidence:

- `/tmp/simple-stage4-bootstrap-4505-20260803/output/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- `/tmp/simple-stage4-bootstrap-4505-20260803/progress.log`
- `/tmp/simple-stage4-bootstrap-4505-20260803/output/bootstrap-build-progress.events`

## Prior evidence

`doc/08_tracking/bug/enum_bare_name_collision_enumeration_2026-08-01.tsv`
already classifies the source declarations as duplicated/identical. That static
inventory does not decide whether the correct fix is declaration consolidation,
an explicit adapter, or import-local disambiguation; the compiled HIR reproducer
must decide before source edits.

## Required repair and evidence

1. Trace the exact `compiler.tools.lint.main` import/re-export route and prove
   whether both terminal enums are semantically identical or merely
   name-compatible.
2. Fix the smallest pure-Simple owner. Prefer one canonical shared lint contract
   with explicit adapters over weakening terminal collision checks.
3. Add an exact compiled reproducer for both enums plus an adjacent case where
   same-spelled but genuinely different enum terminals still fail closed.
4. Rerun only the focused failed shard first, rebuild/admit Stage 3 once, then
   resume the canonical Stage 4 cache-backed build within the three-cycle cap.
5. Keep the conflict diagnostic fail-closed; no import reshuffling, local type
   renaming, Rust-seed fallback, stub generation, or source exclusion may be
   accepted as the root fix.

## Implemented repair (2026-08-17)

The declarations are semantically identical: both enums have the same variant
sets and the lint model already imports `LintLevel` from
`std.tooling.easy_fix.types`. The same import also named `LintCategory`, but a
stale local `LintCategory` declaration shadowed it. The smallest canonical fix
deletes that one duplicate declaration, leaving the public lint facade to
re-export both physical enum terminals from the shared easy-fix contract.

`test/03_system/native/lint_enum_terminal_canonical_owner.spl` is the exact
compiled entry-closure regression: it imports both enums through both public
routes under their original spellings. The adjacent fail-closed guard is the
same-spelled/different-terminal branch in
`test/03_system/native/hir_materialized_enum_payload_dependencies.spl`.

The one permitted focused replay was attempted before editing, but the deployed
wrapper rejected its missing release target during the bounded identity probe,
before compiler startup. Consequently this record remains verification-pending;
neither focused native success nor a resumed canonical Stage 4 build is claimed.
