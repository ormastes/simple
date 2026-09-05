# Stage 4 CLI HIR misclassifies an Array field as Named

- **Date:** 2026-08-03
- **Status:** FIXED — exact parser/field/HIR native boundary passes
- **Severity:** P1
- **Area:** pure-Simple flat parser declaration storage
- **Owner:** `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`
- **Reproducer:** true `SIMPLE_BOOTSTRAP_STAGE4=1` full-CLI lowering of
  `src/app/cli/_CliMain/args_and_os_commands.spl`

The admitted pure-Simple Stage 3 compiler completed all 1,431 Phase 2 surfaces,
then failed on the third Phase 3 HIR module. Focused diagnostics map both empty
names to `GlobalFlags.mem_infra_requested: [text]`: the real parser type is
Array, but `lower_type` routes it through the Named arm and the owner-local
Named guard correctly returns an empty name.

The failure is not a source workaround candidate. Exact native coverage keeps
the Array field plus bool, custom Named, and generic/container neighbors.

Three bounded candidates were disproved after fresh pure-Simple compiler
rebuilds: direct `rt_enum_discriminant` calls in `lower_type`, a typed
`ParserField`/`Type` rebind in `prescan_composite_field_types`, and both changes
together. All experimental edits remain isolated and unmerged.

The exact boundary probe localized the loss before HIR. `field_types` is a
flat `[i64]` table, but its `ftype` temporary was inferred from the global
`TYPE_ANY` constant. On the staged native path that provenance survived the
later `parser_parse_type()` assignment, so `field_types.push(ftype)` passed a
raw type tag to the tagged array ABI. Array reads then decoded it with `>> 3`.
Making the temporary explicitly `i64` restores the required scalar boxing.

Verified with a freshly rebuilt pure-Simple compiler:

- `stage4_parser_field_hir_boundary_probe.spl`: all eight mismatches removed;
  direct `lower_type` and whole-module lowering both report zero errors.
- `array_i64_call_result_push.spl`: direct call-result and reassigned-local
  `[i64]` pushes preserve positive, negative, and literal values.

The full x86 Stage 4 bootstrap remains the enclosing lane's deployment gate;
it is not needed to keep this now-localized bug open.
