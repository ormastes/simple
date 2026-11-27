# Unit type spelling: `Nil` (type) / `nil` (value)

- Date: 2026-11-12
- Decision: **`Nil` is the unit type, `nil` is its single value** (Ruby/Crystal
  spelling). Absence stays `Option` / `None`. Raw null stays `unsafe:`-only.
- Applies to: `Result<Nil, E>`, `-> Nil`, `Ok(nil)`.
- Guide: `doc/07_guide/language/robust_semantic_absence.md` § Unit type.

## Question

What should "succeeded, nothing to return" be written as in a generic slot
(`Result<?, E>`) and a return type (`-> ?`)? The tree had two spellings:
`Result<(), E>` / `Ok(())` and `Result<Nil, E>` / `Ok(nil)`. The Rust seed
accepted both; the pure-Simple Phase 2 compiler rejected `Nil`
(`HIR lowering error ... unresolved type: Nil`), which blocked the MCP server.

## How other languages spell it

| Language | Unit type | Unit value | Absence value |
|---|---|---|---|
| Ruby | `NilClass` | `nil` | `nil` (same) |
| Crystal | `Nil` | `nil` | `nil` (same, via `T \| Nil`) |
| Python | `NoneType` | `None` | `None` (same) |
| Kotlin | `Unit` | `Unit` | `null` |
| Swift | `Void` (= `()`) | `()` | `nil` |
| Scala | `Unit` | `()` | `None` |
| OCaml / F# | `unit` | `()` | `None` |
| Rust / Haskell | `()` | `()` | `None` / `Nothing` |
| TypeScript | `void` | `undefined` | `undefined` / `null` |
| C, C++, Java, C# | `void` | (none) | `null` / `nullptr` |
| Zig | `void` | `{}` | `null` |

Every language separates the type name from the value. The real split is
whether the **unit value** and the **absence value** share a spelling: Ruby,
Crystal and Python share it (one `nil`/`None`), the Option-based languages
(Rust, ML family, Kotlin, Swift, Scala) keep them apart. `void` has no value, so
it cannot fill a generic slot such as `Result<void, E>`.

## Candidates in Simple

| Spelling | Existing meaning in Simple | As the unit type |
|---|---|---|
| `void` | none | no value for `Ok(...)` |
| `None` | empty `Option` (absence) | would merge "missing" with "succeeded" |
| `()` | unit (758 uses) | works; not a word |
| `Nil` / `nil` | 83 `Result<Nil, ...>` sites; `nil` = raw null in `unsafe:` | chosen, with the guard rules below |

## Decision and guard rules

`Nil` reads as a word and matches Ruby. Simple keeps `Option`/`None` for
absence, so `Nil` is **unit only**, never absence:

1. `Nil` is valid only as a type argument or return type (`Result<Nil, E>`,
   `-> Nil`). `Nil?` / `Option<Nil>` is rejected.
2. In safe code, `nil` is legal only where a `Nil` value is expected (for
   example `Ok(nil)` in a `Result<Nil, E>` function, `return nil` in `-> Nil`).
   Every other `nil` remains the raw null: `unsafe:` only (`NIL-UNSAFE-001`).
3. `()` remains accepted as the same unit type; new code prefers `Nil`.

## Consequences

- The pure-Simple compiler must resolve `Nil` as the unit type and the
  `nil_outside_unsafe` rule must admit `nil` at a `Nil`-typed position.
- No source rewrite of the 83 existing `Result<Nil, ...>` sites is needed.
- `Nil` enum variants (`Value.Nil`, `HirTypeKind.Nil`, `RedisReply.Nil`, ...)
  are qualified names and are unaffected.
