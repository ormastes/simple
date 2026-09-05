# Duplicate top-level type name audit (COLLISION lane, 2026-07-17)

**Severity:** systemic (P1-class root cause, most individual instances P3-and-below)
**Status:** 3 confirmed offenders fixed; standalone DUP001 checker added; 85 class-A collisions remain (tracked, not all fixed — see Disposition)

## Why this audit exists

Four independent production bugs landed in a 2-day span, all from the same
mechanism: the seed interpreter's `classes`/`enums` registries are **flat and
global** — a struct/class and an enum sharing a top-level name in different
modules collide at runtime (whichever registers last wins, or class
resolution is tried before enum resolution), with **zero compile-time
signal**. Confirmed instances:

- vtable NAME-keying (`8932fcb3a14`)
- Wall-2 `StmtKind.Expr`-vs-struct-`Expr` (`b1a58671`)
- Compiler-internal `SdnValue` (this audit — fixed below)
- `RunnerTestDb`/`TestDatabase` (`d051505b0c0`,
  `doc/08_tracking/bug/interp_testdatabase_class_collision_kills_aggregate_test_runs_2026-07-17.md`)

Also flagged going in: `X509ParseResult` declared in both
`src/lib/common/cert/x509_typed.spl` and `src/lib/common/crypto/x509.spl`
(fixed below), and a stale duplicate `enum SdnValue` under
`src/compiler_rust/lib/std/src/sdn/value.spl` (mirror tree — noted, not
touched; see Disposition).

## Method

Mechanical scan of `src/lib/**`, `src/compiler/**`, `src/app/**`,
`src/os/**` (owned code; `src/compiler_rust/**` excluded per
`CLAUDE.md` owned-code scope, including its `lib/std` mirror of `src/lib`).
Extracted every top-level (column-0, non-indented) declaration matching
`^(pub )?(enum|struct|class|trait) NAME` — 12,337 `.spl` files, 14,984
declarations, 11,294 distinct names. Grouped by name; a name is "duplicate"
when declared in **2+ distinct files**. `impl` blocks, facade
re-export/`export use` lines, and indented (nested) matches are not counted —
only real declaration bodies.

**2,198 names are declared in 2+ files.** Classified by risk (the mechanism
above only bites when a `struct`/`class` collides with an `enum` of the same
name — that shadowing is what makes construction/pattern-match resolution
ambiguous):

| Class | Meaning | Count | Risk |
|---|---|---|---|
| A | `enum` collides with `struct`/`class` (same name) | **85** (86 pre-fix) | **Highest — confirmed bug mechanism** |
| B | 2+ `enum`s, same name, different variants | 258 | Medium (variant-set mismatch on accidental cross-import) |
| C | 2+ `struct`/`class`, same name, different fields | 1,822 | Low-medium — mostly intentional per-tier mirrors (`nogc_sync_mut`/`nogc_async_mut`/`gc_async_mut`/`nogc_async_mut_noalloc` each re-implement the same stdlib surface by design; a single build normally picks one tier, so these rarely co-load) |
| D | `trait` involved | 32 | Not scored — traits don't construct/pattern-match the same way; lowest urgency |

Class A is the audit's focus: every confirmed incident to date is an
enum-vs-struct/class shadow. Class C's bulk (~1,130 of 1,822 are pure
same-tier `src/lib/**` duplicates) is the **expected, documented** noise the
task brief warned about and is not re-litigated here.

**Caveat — this is a textual scan, not a reachability analysis.** Some
class-A hits are 100% dead code with zero real collision risk. Example:
`HirType` tops the list at 27 files purely because `src/compiler/30.types/`
contains a graveyard of `*_phase{1,4,5,6,7,8}{a,b,c,d}.spl` historical
snapshots (documented in `src/compiler/PHASE_FILES.md` as superseded by a
merged file) that are **not** `mod`-wired into `30.types/__init__.spl` and
have **zero** external references outside their own file (verified for
`bidir_phase1a.spl`, `associated_types_phase4b/c/d.spl`,
`const_keys_phase8b/c.spl`, `higher_rank_poly_phase5c/d.spl`,
`macro_checker_phase7b/c.spl`, `variance_phase6b/c/d.spl` — 20 of
`HirType`'s 27 files). Even the 7 non-`_phase` files in that cluster
(`trait_method_resolution.spl`, `associated_types_defs.spl`,
`bidirectional_types.spl`, `const_key_type.spl`,
`higher_rank_poly_types.spl`, `macro_def.spl`, `variance_types.spl`) have
only **one** external reference across the whole numbered-layer compiler tree
(`macro_registry.spl` → `macro_def`). Read every hit before acting on it —
the checker (below) does not attempt dead-code elimination and will keep
reporting `HirType` until `30.types/` is cleaned up separately (that cleanup
is out of scope here: it's a dead-code sweep, not a name-collision fix, and
the brief says "never over-engineer").

## Top-20 class-A collisions (ranked by file count)

| # | Name | Files | Notes |
|---|---|---|---|
| 1 | `HirType` | 27 | ~20 dead `30.types/*_phaseNx.spl` snapshots (see Caveat); real type is `src/compiler/20.hir/hir_types.spl:576` |
| 2 | `Token` | 10 | Per-subsystem lexers (compiler frontend, sdn, js engine, sksl) — each self-contained, low co-load risk |
| 3 | `EvalResult` | 8 | `app/`+3-tier `nogc_*`/`gc_*` mirrors of dap/mcp debug-eval hooks |
| 4 | `Expr` | 8 | AST node type; 4 of 8 are the `30.types/macro_checker_phase7{a,b,c}.spl` + `macro_def.spl` dead cluster |
| 5 | `ResolutionResult` | 8 | pkg resolver + dependency-tracker, 3-tier mirrored |
| 6 | `RuntimeValue` | 8 | interpreter core value type, 3-tier mirrored |
| 7 | `ParseError` | 7 | per-parser (interpreter, linker_gen, treesitter, mdsoc, sffi_gen, common, gc_async_mut) |
| 8 | `Effect` | 6 | effect-system type across HIR/MIR/type-system layers + `30.types/effects_phase3a.spl` |
| 9 | `LoadResult` | 6 | module loader (×2 compiler-internal) + 3-tier `privilege/store_fs.spl` |
| 10 | `Pattern` | 6 | AST pattern node vs. regex/search `Pattern` — genuinely different domains sharing a name |
| 11 | `TaskState` | 6 | async runtime task state vs. `os/kernel` task state — cross-domain, real risk if ever co-loaded |
| 12 | `Value` | 6 | interpreter core value vs. **`compiler/70.backend/backend_types.spl:169` `enum Value`** — compiler-internal, same family as the fixed `SdnValue`; flagged for follow-up (not fixed this pass, see Disposition) |
| 13 | `ActorState` | 5 | actor runtime state, 3-tier + `nogc_async_immut` snapshot |
| 14 | `BuildResult` | 5 | backend/driver build pipeline, multiple compiler-internal copies |
| 15 | `LazyError` | 5 | lazy-value error type, `app/` + 3-tier |
| 16 | `LazyState` | 5 | lazy-value state, `app/` + 3-tier |
| 17 | `SessionState` | 5 | mcp/debug session state vs. `os/apps/smux` and `os/apps/sshd` session state |
| 18 | `WsFrame` | 5 | websocket frame codec, `gc_async_mut`/`nogc_async_mut` mirrors |
| 19 | `BackendSessionMode` | 4 | GPU engine2d backend session mode, `gc_async_mut`/`nogc_sync_mut` |
| 20 | `CompileResult` | 4 | Two compiler-internal `enum`s (`compiler/00.common/driver_core_types.spl`, `compiler/00.common/parallel.spl` — a class-B pair on their own) both collide with two `nogc_sync_mut/jit/jit_{arm,x86}_mixed.spl` `class`es — the class-A driver is the enum-vs-class pairing, not the enum-vs-enum pair within `00.common` |

Full per-name file:line detail for all 85 is reproducible via
`sh scripts/check/check-type-name-collisions.shs` (below) — not pasted here
in full to keep this doc reviewable.

## Fixed this pass

1. **`struct SdnValue`** in `src/compiler/70.backend/backend_types.spl:124`
   → renamed to **`BackendSdnValue`** (collided with
   `enum SdnValue` in `src/lib/common/sdn/value.spl`). Module-internal type
   (verified via `git grep` — only consumed inside `src/compiler/70.backend/**`
   through two re-export chains, both updated: `70.backend/__init__.spl:15`
   and, caught only on a second sweep after the first "12/12 + specs green"
   verification pass, `src/compiler/70.backend/backend.spl:58`'s
   `export SdnValue, SdnValueKind` — that line wildcard-imports
   `backend_types.*` and re-exports it by bare name, so it silently went
   dangling after the rename with no test catching it (nothing in the
   affected-spec set imports `compiler.backend.backend` — the `backend.spl`
   leaf module — directly). Fixed to `export BackendSdnValue, SdnValueKind`.
   `SdnValueKind` (the paired enum, itself unique/non-colliding) was
   deliberately left untouched throughout.
2. **`struct SdnValue`** in `src/compiler/80.driver/init.spl:280` → renamed
   to **`DriverInitSdnValue`** ("Placeholder type" per its own comment,
   module-private — no `pub`, no export line, zero external consumers of the
   type name; `pub fn parse_sdn_safe`'s return type updated along with it).
3. **`enum X509ParseResult`** in `src/lib/common/crypto/x509.spl:60` →
   renamed to **`X509DerParseResult`** (collided with
   `enum X509ParseResult` in `src/lib/common/cert/x509_typed.spl:46` — the
   real/typed one, used by `src/lib/nogc_sync_mut/tls/certificate.spl`,
   whose own top comment already says "NOT `use` crypto/x509.spl, so
   `x509_parse_der`/`X509ParseResult` never [collide]" — confirming the
   collision was already known-and-dodged by convention, not by a real
   fix). `crypto/x509.spl` has **zero** external consumers of the type name
   (`git grep` confirms all 26 uses are self-contained); safe, low-risk
   rename.

### Verification

- `cargo test -p simple-compiler --lib interpreter_patterns::` — **12/12
  pass** (unchanged). The two `sdnvalue_style_*` tests construct their own
  synthetic `struct SdnValue`/`enum SdnValue` collision inline in the test
  source string — they don't reference the renamed production types, so this
  is an unaffected-not-broken result, not a false positive.
- `src/compiler_rust/target/release/simple run
  test/01_unit/lib/common/cert/x509_spec.spl` — **21/21 examples pass**
  (13+4+2+2 across 4 groups; spec imports `x509_typed.spl`, unaffected by
  the `crypto/x509.spl` rename; confirms no collateral breakage).
- `src/compiler_rust/target/release/simple run
  test/01_unit/compiler/backend/backend_api_spec.spl` — imports
  `backend_types` directly; **4/5 pass**, 1 pre-existing failure
  (`Backend cranelift does not support target x86` casing) traced to a
  *different* file (`src/compiler/70.backend/backend/backend_types.spl` —
  note the extra `backend/` path segment, not the file this audit touched)
  and confirmed unrelated to the rename.
- `simple compile src/compiler/80.driver/init.spl` as a standalone
  single-file target fails on **both** the renamed and the pristine
  (backed-up, restored-and-diffed) version of `init.spl` — with two
  *different* unrelated undefined-identifier errors (`SdnValue` renamed vs.
  `NativeTensor` original) — proving `simple compile <file>` cannot resolve
  this file's full transitive closure standalone regardless of this change;
  not a regression.
- Full-tree bootstrap rebuild was **not** run (out of budget for this pass);
  the two targeted specs above plus the Rust unit tests are the verification
  evidence.

All three fixes and the checker script are on disk, uncommitted — this lane
does not commit (coordinator lands the change).

## DUP001 prevention: standalone checker, not an in-framework lint

The task's default plan was a new
`src/compiler/90.tools/lint/_LintMain/name_collision_lints.spl`, following
`os_freestanding_lints.spl`'s pattern. **Investigated and rejected**: every
lint check in that framework — including `os_freestanding_lints.spl` itself
— is a pure function `(path, content) -> [Warning]` invoked once **per
file** from `Linter.lint_file(file_path)`. `entry_and_fixes.spl`'s `main()`
takes exactly one `file_path` argument from `args[1]`, and there is no
directory-walking driver anywhere in `src/compiler/90.tools/lint/`. A
same-name-in-two-files check fundamentally needs to see every file before it
can flag anything, which this single-file-per-process model cannot do
without real framework surgery (a first collection pass + a second
comparison pass across the whole invocation, which nothing in this
directory does today). `src/compiler/90.tools/duplicate_check/` was also
checked as a candidate cross-file host — it's a semantic/token-similarity
**code**-duplication detector (embeddings, similarity grouping; see
`project_duplication_infra_audit_2026-07-01` in memory) with no notion of
"declaration name," so reusing it would have been a bigger detour than
writing a standalone script.

Per the task's explicit fallback, added **`scripts/check/check-type-name-collisions.shs`**:
a POSIX `/bin/sh` + `awk` whole-tree scanner (same scan/classify logic as
this audit, restricted to class A — enum-vs-struct/class only, since that's
the confirmed mechanism and keeps the hit count in the tens, not thousands).
Single AWK pass (no per-name shell loop — an earlier draft that shelled out
`awk` twice per unique name took >60s and was rewritten to build grouped
file-lists in one streaming pass; now **~0.5s** end-to-end). WARN severity:
report-only (exit 0) by default; `--strict` exits 1 on any hit for gate
wiring; `--help` prints usage. Current hit count on the tree: **85**
(matches this audit's class-A count post-rename, confirming both tools
agree).

```
$ sh scripts/check/check-type-name-collisions.shs
DUP001: 'Pattern' declared as BOTH enum and struct/class in different modules
  enum:         src/app/interpreter/ast_types.spl
  ...
check-type-name-collisions: 85 colliding name(s) found (DUP001, warn severity)
```

Not wired into a CI gate or pre-commit hook this pass (that's a policy
decision — 85 pre-existing hits would need triage/allowlisting first, or the
gate would be red on day one; left for the coordinator to decide alongside
the Disposition list below).

## Disposition — what's fixed vs. what remains

**Fixed (3):** `SdnValue` ×2 (compiler-internal), `X509ParseResult`.

**Remains (85 class-A, 258 class-B, ~692 class-C non-tier-mirror):** not
fixed this pass — renaming 85 enum-vs-struct/class collisions (many spanning
multiple call sites each, some genuinely load-bearing like `RuntimeValue`
and `ParseError`) is a large, multi-day, high-blast-radius change on its
own; the brief scoped this lane to "the confirmed offenders" (the 3 named
explicitly) plus audit + prevention, not a full-repo rename sweep. Two
follow-ups worth flagging explicitly for the next lane:

- `Value`: `src/compiler/70.backend/backend_types.spl:169` (`enum Value`)
  collides with `src/app/interpreter/core/value.spl` (`struct Value`) and
  4 other files — same family/file as the fixed `SdnValue`, same
  "compiler-internal type needs a `Backend`-prefixed name" fix shape. Not
  done this pass (out of the 3 explicitly named offenders); flagged as the
  natural next target since the file is already touched.
- `src/compiler_rust/lib/std/src/sdn/value.spl` `enum SdnValue`: this is the
  **mirror-tree** duplicate the brief called out ("a stale duplicate `enum
  SdnValue`"). Per `CLAUDE.md` owned-code scope and the brief's explicit
  no-touch list (`src/compiler_rust/lib/std/**`), this was **not** edited —
  noted only, per instructions ("NOTE mirrors that shadow").

The 30.types dead-code graveyard (Caveat section) is a separate cleanup
(delete unreferenced `*_phaseNx.spl` files) that would remove ~20 of the 85
hits at zero collision-fix cost but is dead-code hygiene, not a collision
fix — flagged, not actioned, to stay in scope.

A final repo-wide `git grep -nE '\bSdnValue\b'` sweep (word-boundary,
excludes `SdnValueKind`/`BackendSdnValue` by construction) after the
`backend.spl` fix turned up exactly one more non-code hit:
`src/compiler/70.backend/arch_rules.spl:219` `# NOTE: SdnValue parsing
requires sdn module integration` — a comment, not a reference (the file
declares no `SdnValue`-typed code at all); left as-is, harmless.

## Files touched

- `src/compiler/70.backend/backend_types.spl` — `SdnValue` → `BackendSdnValue`
- `src/compiler/70.backend/__init__.spl` — re-export line updated
- `src/compiler/70.backend/backend.spl` — re-export line updated (`SdnValue` → `BackendSdnValue`, caught on second sweep)
- `src/compiler/80.driver/init.spl` — `SdnValue` → `DriverInitSdnValue`
- `src/lib/common/crypto/x509.spl` — `X509ParseResult` → `X509DerParseResult`
- `scripts/check/check-type-name-collisions.shs` — new DUP001 checker
- `doc/08_tracking/bug/duplicate_type_name_collision_audit_2026-07-17.md` — this doc
