# Imported constructor-expression default blocks Lean bootstrap owner

- Canonical ID: `lean_native_constructor_default_argument_2026_10_21`
- Status: OPEN; source workaround active. Bug DB reconciliation pending because
  the available exact compiler is bootstrap-only, not a qualified full CLI.
- Original source/recovery commit: `0bfa8039acd`.
- Owner: imported default-expression lowering in the bootstrap producer;
  `src/plugins/backend_lean/lean_backend.spl:769` is the affected consumer.
- Evidence predates workaround: parent Phase 2 terminal native-build log
  `.simple/storage/build/bootstrap/logs/x86_64-pc-windows-msvc/stage2-native-build.log`
  recorded `compiled=1431 reused=0 failed=5`, including `lean_backend.spl`:
  `call to lean_plan_type_declarations omits argument 3 whose default is not a
  call-site constant; a cross-module/native call cannot evaluate it`.
- Producer: parent's immutable
  `stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe`; exact hash
  and focused command/results are recorded below after diagnostic execution.

`lean_plan_type_declarations` declares argument 3 as
`LeanRecursiveArrayLimitsV1()`. Its defaults are depth 128, nodes 65536, work
1048576, key bytes 1048576, plans 4096. The workaround passes that exact
constructor explicitly; it neither changes policy budgets nor removes the
public default. The missing grammar capability stays open rather than being
normalized into a requirement for all callers to spell defaults explicitly.

The immediately preceding source annotation links this record. The workaround
commit is the Git commit containing this record and that annotation. Retirement
requires a compiler-owner fix plus successful native execution of the original
omitted form against the corrected producer; do not remove the default API.
Related historical diagnosis: `seed_cross_module_selfless_method_drops_receiver_2026-09-26.md`,
section "Still open".

Focused native fixtures in `test/fixtures/compiler/lean_constructor_default_native/`:
`omitted.spl` preserves the failing cross-module constructor-default call;
`explicit.spl` checks the exact five default values, a distinct explicit policy,
and an ordinary imported literal default. They are bootstrap diagnostics, not
SSpec/product-suite or full Lean export qualification. Parent owns the real
Lean module rebuild with retained compatible objects.

Provider usage: input/output/cache-read/cache-create tokens unavailable;
comparable cohort average unavailable; ratio unavailable. No zero-filled or
guessed usage values. Runtime bug-database reconciliation remains pending.

## Focused evidence

AUTHORED_UNEXECUTED at initial workaround commit. No production PASS claimed.
