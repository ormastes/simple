---
paths:
  - "**/*.spl"
  - "**/*.shs"
alwaysApply: false
---
# Simple Language Rules

- **ALL code in `.spl` or `.shs`** - No Python, no Bash (except 3 bootstrap scripts in `scripts/`)
- **Scripts:** Use `.shs` for shell scripts that need to remain shell (e.g., container entrypoints)
- **Generics:** `<>` not `[]` - `Option<T>`, `List<Int>`
- **Pattern binding:** `if val` not `if let`
- **Constructors:** `Point(x: 3, y: 4)` not `.new()`
- **`?` is operator only** - never in names. Use `.?` over `is_*` predicates
- **NO inheritance** - `class Child(Parent)` is NOT supported. Use composition, alias forwarding, traits, or mixins instead
- **SDN format** for all config/data files, not JSON/YAML
- **Error handling:** Use `Result<T, E>` + `?` operator (no try/catch/throw keywords — by design)

## Runtime Limitations
- **Multi-line booleans** - wrap in parentheses: `if (a and\n   b):` works
- **Nested closure capture** - can READ outer vars, CANNOT MODIFY (module closures work fine)
- **Chained methods on erased receivers** - chains fail only when a link's receiver type is erased (e.g. from ANY/dict); typed chains work. Workaround: intermediate typed `val`
- **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`, `examples`, `and_then`
- **`examples` and `and_then`** - declare and read fine as fields, but fail in named-argument position: `Foo(examples: x)` → `function arguments: expected Comma, found Colon`. Rename the field (SAML used `example_cases`). Census run 2026-08-10: these two are the ONLY broken identifiers in that lexer block — `scenario`, `given`, `when`, `then`, `feature`, `outline` are all fine. See `doc/08_tracking/bug/examples_identifier_rejected_in_named_argument_position_2026-08-10.md`

## Syntax Quick Reference
See `doc/07_guide/quick_reference/syntax_quick_reference.md` for complete reference.
See `.claude/memory/ref_coding.md` for coding conventions and common mistakes.

## `.?` is a payload, not a predicate — settled, do not re-file (2026-08-17)

`.?` returns `T?` — the value if present, `nil` if absent (presence = not nil
AND not empty; `syntax_quick_reference.md:548-552`). It is **not** a bool.
`expect(x.?).to_be(true)` compares the unwrapped payload against `true` and the
matcher is telling the truth when it reports the value. Correct predicate form:

    expect(x.? != nil).to_be(true)     # or assert_true(x.? != nil)

This has been triaged twice and closed both times — `3264274affec` ("SPEC
MISUSE, not a compiler defect") and `4e73e47eb2ad` (re-triage closing
`existence_check_conflates_absent_with_empty_text` as NOT A DEFECT). A third
session re-diagnosed it as a compiler bug on 2026-08-17 and filed a duplicate;
that doc was deleted. If a spec fails on `.?`, fix the **spec**, and do not
change `.?` lowering.
