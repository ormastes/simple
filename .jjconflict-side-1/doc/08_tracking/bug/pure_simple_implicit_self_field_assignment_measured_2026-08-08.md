# Pure-Simple HIR lowering: implicit self-field assignment measured, verdict REFUTED

Status: CLOSED (verified, no fix needed on the question asked)
Related: `doc/08_tracking/bug/interp_implicit_self_field_assignment_silent_noop_2026-07-17.md`
Seed fix: `867c724e7bd` (HIR lowering, hard error, not `lenient_types`-gated)

## Question

The seed's Rust HIR lowering fix (867c724e7bd) rejects a bare `field = value`
assignment (no `self.`) inside a `me` method, where `field` is a declared
class field with no existing local binding — direction 2 from the bug doc
(hard error, not silent-discard-then-error). The deployed seed binary
demonstrates the rejection (rc=1, diagnostic naming `Counter`). But the seed's
behavior is not evidence about PURE-SIMPLE's own HIR lowering
(`src/compiler/20.hir/hir_lowering/`) — that source is a separate
implementation and had never been measured on its own terms. Per the
project's "Rust is seed, pure-Simple is the deliverable" rule, this needed a
pure-Simple-native answer.

## Verdict

**Pure-Simple already handles this correctly. No fix required, no data-loss
risk exists.** A bare `field = value` in a method hard-errors with
`"unresolved name: {name}"`, gated at HIR lowering, upstream of MIR/codegen.
This is a refutation of the "might silently discard" concern raised for this
task, and it holds for a *structural* reason, not a coincidental one (see
"Why" below).

## Evidence (executed, not inferred)

`bin/simple lint` and `bin/simple run` were **not usable** for this
measurement: `bin/release/x86_64-unknown-linux-gnu/simple` is currently the
**Rust seed** (58 MB debug binary, prints "this Rust-built Simple binary is a
bootstrap seed only"), confirming the pre-existing "Deployed-binary gotcha
(2026-08-08)" note in `.claude/rules/testing.md`. `lint`/`run` against that
binary would only exercise the seed, never pure-Simple's own lowering.

Instead, `bin/simple test` (which hard-defaults to the seed's **tree-walk
interpreter**, per `.claude/rules/testing.md`) was used to *directly invoke*
the real pure-Simple `compiler.hir.hir_lowering` module — `parse_full_frontend`
+ `HirLowering.with_filename(...).lower_module(module)` — the same pattern an
existing spec (`test/01_unit/compiler/hir/domain_block_hir_lowering_spec.spl`)
already uses to drive the pure-Simple frontend/HIR-lowering source directly.
This interprets the actual `.spl` source on disk, not a Rust reimplementation
— confirmed two ways:

1. **Message-text divergence.** The measured diagnostic is `"unresolved name:
   flag"` (from `lower_unresolved_ident` in
   `src/compiler/20.hir/hir_lowering/expressions.spl:398`). The seed's Rust
   message for the *same* shape is completely different wording: `"invalid
   assignment: `flag` is a field of `Counter`; a bare `flag = ...` creates a
   new local..."` (`src/compiler_rust/compiler/src/hir/lower/error.rs`,
   `LowerError::ImplicitSelfFieldAssignment`). The measured text could only
   have come from the pure-Simple `.spl` source, not the seed's native check.
2. **Sabotage-marker edit-visibility proof.** Changing the literal string at
   `expressions.spl:398` to `"unresolved name SABOTAGE: {name}"` and re-running
   the probe changed the measured diagnostic to include `SABOTAGE`; reverting
   removed it again. (First attempt, with the probe spec parked in a `/tmp`
   scratchpad directory, showed NO change and was even immune to a deliberate
   syntax error — traced via `strace -f -e trace=openat` to a **stale bundled
   `src/` snapshot already sitting inside that scratchpad directory**
   (`<scratchpad>/src/compiler/hir/hir_lowering/expressions.spl`, dated a day
   earlier), which module resolution's sibling/parent-directory search
   preferred over the real repo tree — the general form of "`bin/simple run`
   from a directory without `src/lib/` silently serves a BUNDLED stdlib",
   extended to `compiler/`. Moving the probe spec into the real repo tree
   (`test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl`) and
   confirming via `strace` that `openat` hit
   `/home/ormastes/dev/pub/simple/src/compiler/20.hir/hir_lowering/expressions.spl`
   fixed it; the sabotage marker then showed up correctly, and after revert the
   clean text came back. This scratchpad-contamination trap is itself worth
   remembering for future measurements from `/tmp`.)
3. **Hard-error vs. recovered, distinguished, not inferred.**
   `lowering_error_count()` counts both `error()` and `recovered()` pushes to
   the same array, so a raw count does not by itself prove the pipeline halts.
   `lowering_error_is_recovered_at(0)` was checked explicitly and returns
   `false` — this is a genuine hard error (`self.error(...)`, not
   `self.recovered(...)`), matching the source-read of
   `lower_unresolved_ident`'s final branch.

Landed as a real spec (not a throwaway probe) at
`test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl`, green
under `bin/simple test`, 3 examples:

- bare `flag = true` in a method → 1 hard error, `"unresolved name: flag"`,
  not recovered
- explicit `self.flag = true` → 0 diagnostics (still works)
- bare `scratch = 41` (non-field local) → 2 diagnostics, `"unresolved name:
  scratch"` (see divergence below)

## Why (structural, not coincidental)

Read of `src/compiler/20.hir/hir_lowering/statements.spl`
(`StmtKind.Assign` lowering, ~line 497-499) and `expressions.spl`
(`ExprKind.Ident` lowering, ~line 738-791): pure-Simple's HIR lowering has
**no implicit-local-declaration mechanism at all**. An assignment target is
lowered through the identical `ExprKind.Ident` -> `symbols.lookup` path used
for any expression-position identifier; on a miss it always falls to
`lower_unresolved_ident`, which — outside a short allowlist (`me`/`self`
aliasing, interpreter/bootstrap builtins, `Ok`/`Err`/`Some`/`None`,
`Result`/`Option` type names, GPU intrinsics) — hard-errors. There is no
separate "assignment to an unbound name mints a new local" code path for
lowering to accidentally route a field write into, unlike the seed's
(now-fixed) Rust HIR lowering, which *did* have such a path and needed a
field-specific carve-out to stop using it for field names. Pure-Simple simply
never built the mechanism the original defect depended on, so there is no
route by which a field write could be silently rerouted to a fresh local.

The 2-diagnostics-for-2-occurrences symmetry in the `scratch = 41; return
scratch + 1` case (one for the assignment-target `scratch`, one for the
read of `scratch` in the return expression, since neither ever got a symbol)
corroborates that the check is generic bare-ident resolution, not a
field-specific rule — further support that this isn't a narrow accident.

`lower_struct_construct`'s Nil→3 mechanism (the sibling defect in
`50.mir/_MirLoweringExpr/switch_operators_calls.spl:3038`, where an unknown
field name is inserted into a map, never consumed, and falls through to a
`Nil` placeholder that reads as constant `3`) does **not** apply here: that
defect requires the unresolved name to be *accepted* into a data structure
without validation. Here the target never resolves to a symbol at all —
`lower_unresolved_ident` hard-errors immediately, so nothing is
inserted-and-left-unvalidated. This is a resolution failure, not an
accepted-but-unconsumed map entry. (Source-read conclusion only, not
independently executed — the mechanism's absence follows directly from the
control flow already traced above.)

## Message-quality gap (not fixed — out of scope, no data-loss)

Pure-Simple's diagnostic (`"unresolved name: flag"`) does not name the class
or suggest the `self.flag` fix the way the seed's does. This is a
message-quality gap, not a correctness gap — behavior is already correct in
direction (loud, no data loss). Per "never over-engineer / only make
requested changes", this was **not fixed**: the task's scope was
silent-discard-or-mis-assign risk, which does not exist here.

## Separate, filed-but-not-fixed finding: seed/pure-Simple divergence on bare non-field locals

The seed's own spec
(`test/01_unit/compiler/interpreter/implicit_self_field_assign_spec.spl`,
`PLAIN_LOCAL_SRC`) asserts that a bare `scratch = 41` (not a field name) is
**legal** implicit local declaration (`PLAIN_RESULT=42`, exit 0) — this is
the seed's own regression guard for "the fix must not ban implicit
declaration generally, only the field-shadowing case." Pure-Simple's HIR
lowering, having no implicit-local-declaration path at all, **hard-errors on
this shape too** (`"unresolved name: scratch"`, measured above). This is a
genuine seed/pure-Simple behavioral divergence, worth recording, but it is
**out of scope for this task** (which is about the self-field-shadowing
silent-discard risk, not about the general availability of implicit-local
declaration) and is **not fixed here**. Whether pure-Simple should someday
gain implicit-local declaration is a separate design question — recorded
here only as an open, unaddressed divergence, not asserted as a defect.
