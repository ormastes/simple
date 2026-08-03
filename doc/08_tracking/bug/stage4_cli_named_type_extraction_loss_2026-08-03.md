# Stage 4 CLI HIR loses a named type payload

- **Date:** 2026-08-03
- **Status:** OPEN — CLAIMED by the x86 Stage 4 root lane
- **Severity:** P1
- **Area:** pure-Simple HIR type lowering
- **Owner frontier:** `src/compiler/20.hir/hir_lowering/types.spl`
- **Reproducer:** true `SIMPLE_BOOTSTRAP_STAGE4=1` full-CLI lowering of
  `src/app/cli/_CliMain/args_and_os_commands.spl`

The admitted pure-Simple Stage 3 compiler completed all 1,431 Phase 2 surfaces,
then failed on the third Phase 3 HIR module. `lower_type` observed a parser type
whose discriminant was `Named`, but `parser_type_kind_named_name` returned an
empty string and emitted `internal: failed to extract named type`.

The failure is not a source workaround candidate. Preserve the compact named
types in the CLI file and identify whether the payload is lost in parser type
transport, facade extraction, or staged-native tuple/enum handling. Add the
exact type form plus an adjacent generic/container form before retrying the
incremental Stage 4 build.
