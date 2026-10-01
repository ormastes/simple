# RC1 fixes forwarded to main

## Scope and branch evidence

User requested synchronizing and landing the fixes on main and release/1.0.
Release PR2069 was already merged externally at f991cfb8ad6 on2026-09-29;
its head was3fb3d723c67. This forward port starts from main f1496d6ca54.
It carries applicable source fixes rather than replacing main with release files.

## Main-specific reconciliation

- Retain main's scalar field-edge traversal, well-formed heap reference guard,
  missing-node guard and explicit HirModule import. Add typed struct-values
  traversal without reconstructed SymbolId dictionary lookup.
- Add mono function-values traversal with stable numeric index ordering and
  regression assertions for actual retained function payloads.
- Retain main's origin-first re-export resolution, private-import export guard,
  caches and tracing. Add explicit result-carrier types and scalar snapshots.
- Preserve main's existing lexer wire conversion, UTF-8 tests, generic HIR
  tagging and source-spec metadata. Remove a stale unreachable enum/integer
  comparison and restore missing MIR generic-template non-emission guards.
- Restore the legacy manifest Effect/AutoLeanMode model with capability tests.
- Preserve main's stronger malformed-type diagnostics. Do not import the RC1
  diagnostic that dereferences a potentially corrupt span. Retain the already
  receiver-qualified MIR helper calls.
- Retain nil guards and existing template-pruning expectations while adding
  nullable Let verification/substitution coverage.
- Prior PR2059 audit: main already has scalar block-tail classification, tuple
  handling, explicit-return preservation, plain Let payloads and broader memo
  promotion. Preserve its newer heap/span and type-copy guards. Forward only
  missing canonical process/lock imports, retaining newer companion imports.
- Adapt bootstrap infrastructure around main's newer admission, storage and
  Cargo environment contracts; shell evidence is recorded below after checks.

Focused bootstrap verification PASS: host capacity and explicit memory ceiling;
Windows TEMP/TMP, Cargo environment and executable/archive contracts; actual
configured-output producer/verifier (three fixtures); shell syntax and workflow
YAML. Main's stronger output allowlist was preserved, not replaced by RC1's
narrower admission implementation. Full portability suite remains unrun.

The accompanying RC1 cycle reports describe historical release producers, not
successful execution of this main candidate.

## Verification limits

No qualified self-hosted full CLI/test runner is available in this session:
main workspace has no bootstrap stage3, stage4 or tool_cache artifacts. The
previously inspected installed release binary is the old Rust seed; it is not
used as normal tooling. Release cycle3's Stage2 compiler is bootstrap-only.
The three authorized RC1 rebuild cycles are exhausted, with failures recorded
in rc1_phase34_cycle3_2026-09-29.md. This synchronization does not claim a fourth
compiler rebuild or successful runtime qualification.

Source conflict review and focused infrastructure checks cannot substitute for
SSpec, compiler/lib/MCP checks, native smoke or full bootstrap. Main landing
qualification remains incomplete until required evidence is available.

Working and staged direct-env-runtime guards PASS. The complete tracked tree
contains zero executable specs under doc/06_spec (including sparse paths).
Assigned compiler lanes passed scoped whitespace review. These are structural
checks, not compiler execution evidence.

**STATUS: WARN — forward-port candidate; runtime verification pending.**
