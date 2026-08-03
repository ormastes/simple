# Stage 4 CLI HIR misclassifies an Array field as Named

- **Date:** 2026-08-03
- **Status:** OPEN — CLAIMED by the x86 Stage 4 root lane
- **Severity:** P1
- **Area:** pure-Simple HIR type lowering
- **Owner frontier:** parser `ParserField.type_` transport into
  `src/compiler/20.hir/hir_lowering/types.spl::lower_type`
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

A fresh session must instrument the parsed `GlobalFlags` field before
`lower_module`, then at direct `lower_type` entry, to determine whether the
Array tag is lost in parser-module storage, field extraction, or the method-call
ABI. Do not retry the three rejected candidates.
