# Bootstrap parents reject source outside the bootstrap grammar intersection

Date: 2026-08-22
Status: partial — source grammar and jj capsule provenance fixed; current
Stage-2 link still fails inside the seed's hard-wired runtime builder

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
