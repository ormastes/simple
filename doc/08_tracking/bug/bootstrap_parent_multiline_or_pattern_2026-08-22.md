# Bootstrap parents reject source outside the bootstrap grammar intersection

Date: 2026-08-22
Status: CLOSED 2026-11-11 (FIXED source-side per 2026-11-10 triage, re-verified with seed-smoke spec PASS by lane boot10; seed-capsule residual belongs to the Rust seed lane)

## Reproducer

The official pure-Simple v0.9.8 parent failed discovery of
`src/compiler/20.hir/hir_verification.spl` at the indented body of a multiline
`case A | B | C:` pattern. After that was corrected, the current Rust bootstrap
seed rejected `val bind` in `match_desugaring.spl`; `bind` is a language keyword.
No object was emitted in either case.

## Root cause and fix

The bootstrap parents do not parse that continued OR-pattern form. The
decreases-type predicate now uses one expression-bodied match arm per admitted
unsigned integer width. This preserves behavior while keeping compiler source
inside the bootstrap grammar intersection.

The enum-payload helper now names its local `binding_pattern`, preserving its
HIR value while avoiding the reserved token.

After source discovery and 613 object compilations succeeded, the dedicated
core-C runtime capsule completed its self-checks but aborted at provenance:
the producer used jj for its clean-source gate and then unconditionally invoked
Git in a non-colocated jj workspace. It now derives `head_revision` from jj and
binds `runtime_tree` to a deterministic path-and-content digest of the exact
local runtime input manifest; colocated Git worktrees retain the Git-tree path.

`test/01_unit/compiler/hir/parser_contract_type_owner_spec.spl` already covers
the admitted 8-bit and 128-bit boundaries plus signed, boolean, and text
rejections.

## Evidence and remaining failure

- The official pure-Simple v0.9.8 parent checks both corrected compiler files.
- The HIR contract spec passes: 2 examples, 0 failures.
- The dedicated capsule producer passes 33 checks and emits a deterministic
  archive from the non-colocated jj workspace.
- The current seed's bootstrap entry still ignores the explicit runtime capsule
  for its core-bootstrap lane and fails its internal runtime-archive builder.
  Three bounded build/fix cycles were exhausted, so no Stage-2 executable is
  claimed.
- The v0.9.8 runner cannot execute the capsule source-inspection spec because
  its `file_read` recurses past depth 1000; this is a tool-version limitation,
  not substituted PASS evidence.

## Triage 2026-11-10 (p3-boot2 lane)

SUPERSEDED — both source-side fixes verified live on
work/p3-boot2-20261110 (base origin/release/1.0.0), seed-smoke evidence:

- `src/compiler/20.hir/hir_verification.spl:6-12` —
  `hir_verification_decreases_type_valid` now uses one expression-bodied
  match arm per admitted unsigned width (8/16/32/64/128, `case
  HirTypeKind.Int(w, false): true`), exactly this record's described fix.
  The multiline `case A | B | C:` form the v0.9.8 parent could not discover
  is gone from the compiler source.
- `src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl:276` —
  the enum-payload helper binds `binding_pattern`, not the reserved `bind`.
- Named evidence spec: `SIMPLE_LIB=src bin/simple.exe test
  test/01_unit/compiler/hir/parser_contract_type_owner_spec.spl
  --mode=interpreter` -> `SPEC FILE VERDICT outcome=OK declared>=2
  executed=2 passed=2 failed=0` (covers the admitted 8-bit/128-bit
  boundaries plus signed/boolean/text rejections).

Remaining 2026-08-22 item ("seed's hard-wired runtime builder ignores the
explicit runtime capsule for its core-bootstrap lane"): the seed lane has
since taken extensive capsule/bootstrap fixes, e.g. `8a1b47a255f6`
("let the bootstrap capsule supply C-only runtime exports", 2026-10-22) and
`b91c2221514c` ("root native_all owners of every capsule-retained symbol",
2026-10-22), both ancestors of this branch — that residual belongs to the
Rust seed lane (agent-10 scope), not this record's grammar/provenance scope.

## Triage 2026-11-11 (lane boot10)

FIXED — both source-side fixes re-verified with seed-smoke evidence on
work/p3-boot10-20261111 (base origin/release/1.0.0), one cycle:

- `src/compiler/20.hir/hir_verification.spl:6-12` —
  `hir_verification_decreases_type_valid` uses one expression-bodied match
  arm per admitted unsigned width (8/16/32/64/128); the multiline
  `case A | B | C:` form is gone from the compiler source.
- `src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl:276` —
  the enum-payload helper binds `binding_pattern`, not the reserved `bind`.
- Named evidence spec (seed-smoke, this lane):
  `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe test
  test/01_unit/compiler/hir/parser_contract_type_owner_spec.spl
  --mode=interpreter --no-cache` ->
  `SPEC FILE VERDICT outcome=OK declared>=2 executed=2 passed=2 failed=0`.

Remaining 2026-08-22 item (seed's hard-wired runtime builder ignoring the
explicit runtime capsule): owned by the Rust seed lane — the capsule/bootstrap
fixes `8a1b47a255f6` and `b91c2221514c` (both 2026-10-22, ancestors of this
branch) are that lane's deliveries. No code change this lane.
