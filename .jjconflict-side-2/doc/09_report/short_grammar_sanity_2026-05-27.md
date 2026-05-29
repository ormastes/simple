# Short Grammar Sanity Report

Date: 2026-05-27

## Scope

Reviewed compact grammar forms from Python, Ruby, and TypeScript against Simple's documented and executable syntax. External references used:

- Python language reference, expressions: lambda, comprehensions, conditional expressions, and assignment expressions: https://docs.python.org/3/reference/expressions.html
- Ruby RDoc Proc numbered parameters: https://ruby-doc.org/3.1.6/Proc.html
- Ruby RDoc safe navigation: https://ruby-doc.org/2.7.7/syntax/calling_methods_rdoc.html
- Ruby RDoc Symbol/Proc conversion: https://ruby-doc.org/3.4/Proc.html
- TypeScript Handbook functions: https://www.typescriptlang.org/docs/handbook/functions
- TypeScript 3.7 release notes for optional chaining and nullish coalescing: https://www.typescriptlang.org/docs/handbook/release-notes/typescript-3-7

## Counterpart Matrix

| Source form | Source language | Simple counterpart | Status |
|-------------|-----------------|--------------------|--------|
| `lambda x: x * 2` | Python | `\x: x * 2` and `fn(x): x * 2` | Exists; interpreter covered. |
| `[x * x for x in xs if pred(x)]` | Python | `[for x in xs if pred(x): x * x]` | Exists; interpreter covered, native coverage added for non-piped use. |
| `x if cond else y` | Python | `if cond: x else: y` expression form | Exists in docs, needs focused runtime coverage beyond this report. |
| `name := expr` | Python | `name := expr` as val shorthand | Documented, but not currently executable; parser treats `:` as block syntax in at least one parser test TODO. |
| `{ _1 * 2 }` block shorthand | Ruby | `_1 * 2`, `_ * 2` placeholder lambdas | Exists; usage specs cover interpreter behavior. |
| `&:len` | Ruby | `&:len` method reference | Exists; usage specs cover interpreter behavior. |
| `obj&.name` | Ruby | `obj?.name` and `value.?` | Exists; optional chaining/exists-check coverage present. |
| `(x) => x * 2` | TypeScript | `\x: x * 2`, `fn(x): x * 2` | Exists; `=>` is intentionally not Simple syntax. |
| `obj?.name` | TypeScript | `obj?.name`, `value.?` | Exists. |
| `value ?? fallback` | TypeScript | `value ?? fallback` | Exists. |
| `items.map(x => x * 2)` | TypeScript | `items.map(_ * 2)` or `items.map(\x: x * 2)` | Exists; prefer placeholder only for single-expression transforms. |

## Sanity Findings

- Simple already has counterparts for the common compact expression families: lambdas, placeholder lambdas, numbered placeholders, method references, list comprehensions, optional access, nil coalescing, pipe, and composition.
- `:=` is the main mismatch: it is listed as a supported shorthand in coding guidance and has a feature spec, but executable tests currently avoid the actual token. Treat it as unavailable until parser/runtime tests prove otherwise.
- Native mode does not currently provide real evidence for pipe-forward short grammar. `test/unit/compiler_core/parser/short_grammar_combined_spec.spl --mode=native` can pass via codegen stub fallback after reporting `Pipe forward (|>) requires interpreter mode for function dispatch`.
- Short grammar tests should be split by runtime support: interpreter specs may cover pipe and dynamic dispatch forms; native specs should cover only forms that compile without fallback.

## Test Evidence Added

- `test/unit/compiler_core/parser/short_grammar_interpreter_spec.spl`: interpreter-focused combinations for placeholder lambda, numbered placeholder, method reference, comprehension, `??`, and pipe/compose.
- `test/unit/compiler_core/parser/short_grammar_native_spec.spl`: native-safe short forms without pipe-forward dispatch.

## Guidance

- Prefer short grammar when it removes local boilerplate and keeps the expression readable.
- Avoid compact forms when they hide errors, change runtime support, or force native fallback.
- Do not use `:=` in new Simple code until actual `:=` tests pass in both the intended parser path and target runtime.
