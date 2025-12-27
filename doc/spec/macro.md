Simple Language — Contract-First Macros (LL(1), One-Pass) Specification

**Status:** SPECIFICATION (Partially Implemented)
**Last Updated:** 2025-12-27
**Implementation Status:** See `doc/status/macros.md`

This macro system is designed so the parser/IDE can learn introduced symbols and insertion points from the macro header alone, while still keeping the grammar LL(1) and enabling single-pass parsing + immediate symbol-table updates.

It assumes Simple's existing layout model: indentation-based blocks, if x: / for i in 0..10: forms, etc.

## Implementation Notes

**Currently Working:**
- ✅ Macro definition syntax parsing
- ✅ User-defined macros with `const_eval:` and `emit` blocks
- ✅ Template substitution (`"{NAME}"` → const value)
- ✅ Contract processing infrastructure (intro/inject/returns)
- ✅ Const-eval engine (integers, arithmetic, conditions)

**Not Yet Integrated:**
- ⏳ LL(1) parser integration (currently interpreter-driven)
- ⏳ One-pass symbol registration
- ⏳ IDE autocomplete from contracts
- ⏳ Code injection at callsite

**See:** `doc/status/macros.md` for detailed implementation status

---

1) Design goals and non-goals

Goals

Contract-first: Introductions/injections are declared in the macro header (-> (...)).

IDE-first: Full signatures (names, params, return types) are available without macro expansion.

LL(1): No backtracking; production chosen by 1-token lookahead.

One-pass: As the parser encounters a macro call, it can const-evaluate contract inputs, apply intro to the symbol table, and continue.


Non-goals

Arbitrary AST inspection in the contract (kept const-only).

Hygienic renaming in the contract (can be added later; not required for LL(1)).



---

2) Lexical rules that make LL(1) practical

2.1 Layout tokens

The lexer emits: NEWLINE, INDENT, DEDENT (Python-style). 

2.2 Newlines inside parentheses

Inside (...), NEWLINE/INDENT/DEDENT are suppressed (like Python’s implicit line joining). This keeps the contract syntax flexible without impacting LL(1).

2.3 Macro invocation is explicitly marked

A macro call uses !:

define_counter!("User")

This makes macro calls unambiguous in LL(1) parsing.


---

3) Core syntax (informal)

macro define_counter(NAME: Str const) -> (
  returns result: (init: Int, step: Int),
  intro counter_fn: enclosing.class.fn "{NAME}Counter"(start: Int) -> Int
):
  const_eval:
    const init = 0
    const step = 1

  emit counter_fn:
    fn "{NAME}Counter"(start: Int) -> Int:
      return start + step

  emit result:
    (init: init, step: step)


---

4) Contract model

4.1 Contract items

returns <label?>: <Type> — the macro call’s expression type

intro <label>: <target>.<kind> <decl-stub> — introduced symbols (for symbol table)

inject <label>: callsite.block.<anchor>.<codekind> — code insertion at block head/tail/here


4.2 Targets and anchors (LL(1)-safe)

To keep LL(1), callsite.block always includes an anchor (head|tail|here). This avoids the classic ambiguity where . could mean either “anchor separator” or “kind separator”.

Scopes

enclosing.module | enclosing.class | enclosing.struct | enclosing.trait

callsite.block.<anchor>


Anchors

head | tail | here


Kinds

fn | field | type | let | const


Code kinds

stmt | block



---

5) Grammar (BNF, macro subsystem only)

Terminals are quoted. IDENT and QIDENT are token classes.

5.1 Macro declaration

MacroDecl
  -> "macro" IDENT "(" ParamListOpt ")" "->" "(" ContractItemsOpt ")" ":" NEWLINE INDENT MacroBodyLines DEDENT

ParamListOpt
  -> ParamList
  | ε

ParamList
  -> Param ParamListTail

ParamListTail
  -> "," Param ParamListTail
  | ε

Param
  -> IDENT ":" Type ConstQualOpt

ConstQualOpt
  -> "const"
  | ε

5.2 Contract

ContractItemsOpt
  -> ContractItemList
  | ε

ContractItemList
  -> ContractItem ContractItemTail

ContractItemTail
  -> "," ContractItem ContractItemTail
  | ε

ContractItem
  -> ReturnsItem
  | IntroItem
  | InjectItem

ReturnsItem
  -> "returns" LabelOpt ":" Type

LabelOpt
  -> IDENT
  | ε

IntroItem
  -> "intro" IDENT ":" IntroSpec

InjectItem
  -> "inject" IDENT ":" InjectSpec

5.3 Introductions

IntroSpec
  -> IntroDecl
  | ForIntro
  | IfIntro

IntroDecl
  -> Target "." "fn"    FnStub
  | Target "." "field" FieldStub
  | Target "." "type"  TypeStub
  | Target "." LetConst VarStub

LetConst
  -> "let"
  | "const"

Target
  -> EnclosingTarget
  | CallsiteTarget

EnclosingTarget
  -> "enclosing.module"
  | "enclosing.class"
  | "enclosing.struct"
  | "enclosing.trait"

CallsiteTarget
  -> "callsite.block" "." Anchor

Anchor
  -> "head"
  | "tail"
  | "here"

Declaration stubs (note: var requires explicit type)

FnStub
  -> QIDENT "(" ParamSigOpt ")" RetOpt

ParamSigOpt
  -> ParamSig
  | ε

RetOpt
  -> "->" Type
  | ε

FieldStub
  -> QIDENT ":" Type

VarStub
  -> QIDENT ":" Type

TypeStub
  -> QIDENT

Const-unrolled intro blocks

ForIntro
  -> "for" IDENT "in" ConstRange ":" NEWLINE INDENT IntroSpecLines DEDENT

IfIntro
  -> "if" ConstExpr ":" NEWLINE INDENT IntroSpecLines DEDENT ElseOpt

ElseOpt
  -> "else" ":" NEWLINE INDENT IntroSpecLines DEDENT
  | ε

IntroSpecLines
  -> IntroSpecLine IntroSpecLines
  | ε

IntroSpecLine
  -> IntroSpec NEWLINE

ConstRange
  -> ConstExpr ".." ConstExpr

5.4 Injections (block head/tail/here)

InjectSpec
  -> "callsite.block" "." Anchor "." CodeKind

CodeKind
  -> "stmt"
  | "block"

5.5 Macro body

MacroBodyLines
  -> MacroStmtLine MacroBodyLines
  | ε

MacroStmtLine
  -> MacroStmt NEWLINE

MacroStmt
  -> ConstEvalStmt
  | EmitStmt
  | SimpleStmt

ConstEvalStmt
  -> "const_eval" ":" NEWLINE INDENT SimpleStmtLines DEDENT

EmitStmt
  -> "emit" IDENT ":" NEWLINE INDENT TemplateStmtLines DEDENT

(Where SimpleStmt, Type, ConstExpr, ParamSig, Expr are defined by the base language grammar.)

5.6 Macro invocation (LL(1) disambiguation)

MacroCallExpr
  -> IDENT "!" "(" ArgListOpt ")"

ArgListOpt
  -> ArgList
  | ε

ArgList
  -> Expr ArgListTail

ArgListTail
  -> "," Expr ArgListTail
  | ε


---

6) FIRST and FOLLOW sets (macro subsystem)

Below are FIRST/FOLLOW for the macro subsystem nonterminals. For Type, ConstExpr, Expr, etc., treat them as opaque with their own FIRST sets.

6.1 FIRST sets

FIRST(MacroDecl) = { "macro" }

FIRST(ParamListOpt) = { IDENT, ε }

FIRST(ParamListTail) = { ",", ε }

FIRST(ConstQualOpt) = { "const", ε }

FIRST(ContractItemsOpt) = { "returns", "intro", "inject", ε }

FIRST(ContractItem) = { "returns", "intro", "inject" }

FIRST(ContractItemTail) = { ",", ε }

FIRST(ReturnsItem) = { "returns" }

FIRST(LabelOpt) = { IDENT, ε }

FIRST(IntroItem) = { "intro" }

FIRST(InjectItem) = { "inject" }

FIRST(IntroSpec) = { enclosing.module, enclosing.class, enclosing.struct, enclosing.trait, callsite.block, "for", "if" }

FIRST(Target) = { enclosing.module, enclosing.class, enclosing.struct, enclosing.trait, callsite.block }

FIRST(EnclosingTarget) = { enclosing.module, enclosing.class, enclosing.struct, enclosing.trait }

FIRST(CallsiteTarget) = { callsite.block }

FIRST(Anchor) = { "head", "tail", "here" }

FIRST(LetConst) = { "let", "const" }

FIRST(ForIntro) = { "for" }

FIRST(IfIntro) = { "if" }

FIRST(ElseOpt) = { "else", ε }

FIRST(IntroSpecLines) = FIRST(IntroSpecLine) ∪ {ε}

FIRST(IntroSpecLine) = FIRST(IntroSpec)

FIRST(InjectSpec) = { callsite.block }

FIRST(CodeKind) = { "stmt", "block" }

FIRST(MacroStmt) includes { "const_eval", "emit" } ∪ FIRST(SimpleStmt) (LL(1) requires "const_eval" and "emit" be reserved keywords.)


6.2 FOLLOW sets

FOLLOW(ParamListOpt) = { ")" }

FOLLOW(ParamListTail) = { ")" }

FOLLOW(Param) = { ",", ")" }

FOLLOW(ConstQualOpt) = { ",", ")" }

FOLLOW(ContractItemsOpt) = { ")" }

FOLLOW(ContractItem) = { ",", ")" }

FOLLOW(ContractItemTail) = { ")" }

FOLLOW(LabelOpt) = { ":" }

FOLLOW(IntroSpec) = { NEWLINE, ",", ")" }

NEWLINE when used in IntroSpecLine

"," / ")" when used in the contract list


FOLLOW(Target) = { "." }

FOLLOW(EnclosingTarget) = { "." }

FOLLOW(CallsiteTarget) = { "." }

FOLLOW(Anchor) = { "." }

FOLLOW(IntroSpecLines) = { DEDENT }

FOLLOW(IntroSpecLine) includes FIRST(IntroSpecLine) ∪ { DEDENT } (standard list recursion)

FOLLOW(ElseOpt) = FOLLOW(IfIntro) = FOLLOW(IntroSpec) = { NEWLINE, ",", ")" }

FOLLOW(InjectSpec) = { ",", ")" }

FOLLOW(CodeKind) = FOLLOW(InjectSpec) = { ",", ")" }

FOLLOW(MacroBodyLines) = { DEDENT }



---

7) LL(1) parse table (macro subsystem)

I’m providing a sparse LL(1) parse table: entries are shown only where they are defined (all other combinations are “error”).

Notation: M[Nonterminal, lookahead] = Production.

7.1 Macro header

MacroDecl

M[MacroDecl, "macro"] = MacroDecl -> "macro" IDENT "(" ParamListOpt ")" "->" "(" ContractItemsOpt ")" ":" NEWLINE INDENT MacroBodyLines DEDENT


ParamListOpt

M[ParamListOpt, IDENT] = ParamListOpt -> ParamList

M[ParamListOpt, ")"] = ParamListOpt -> ε


ParamListTail

M[ParamListTail, ","] = ParamListTail -> "," Param ParamListTail

M[ParamListTail, ")"] = ParamListTail -> ε


ConstQualOpt

M[ConstQualOpt, "const"] = ConstQualOpt -> "const"

M[ConstQualOpt, ","] = ConstQualOpt -> ε

M[ConstQualOpt, ")"] = ConstQualOpt -> ε



---

7.2 Contract list

ContractItemsOpt

M[ContractItemsOpt, "returns"] = ContractItemsOpt -> ContractItemList

M[ContractItemsOpt, "intro"]   = ContractItemsOpt -> ContractItemList

M[ContractItemsOpt, "inject"]  = ContractItemsOpt -> ContractItemList

M[ContractItemsOpt, ")"]       = ContractItemsOpt -> ε


ContractItem

M[ContractItem, "returns"] = ContractItem -> ReturnsItem

M[ContractItem, "intro"]   = ContractItem -> IntroItem

M[ContractItem, "inject"]  = ContractItem -> InjectItem


ContractItemTail

M[ContractItemTail, ","] = ContractItemTail -> "," ContractItem ContractItemTail

M[ContractItemTail, ")"] = ContractItemTail -> ε


ReturnsItem

M[ReturnsItem, "returns"] = ReturnsItem -> "returns" LabelOpt ":" Type


LabelOpt

M[LabelOpt, IDENT] = LabelOpt -> IDENT

M[LabelOpt, ":"]   = LabelOpt -> ε


IntroItem

M[IntroItem, "intro"] = IntroItem -> "intro" IDENT ":" IntroSpec


InjectItem

M[InjectItem, "inject"] = InjectItem -> "inject" IDENT ":" InjectSpec



---

7.3 IntroSpec

IntroSpec

M[IntroSpec, "for"] = IntroSpec -> ForIntro

M[IntroSpec, "if"]  = IntroSpec -> IfIntro

M[IntroSpec, enclosing.module] = IntroSpec -> IntroDecl

M[IntroSpec, enclosing.class]  = IntroSpec -> IntroDecl

M[IntroSpec, enclosing.struct] = IntroSpec -> IntroDecl

M[IntroSpec, enclosing.trait]  = IntroSpec -> IntroDecl

M[IntroSpec, callsite.block]   = IntroSpec -> IntroDecl


Target

M[Target, enclosing.module] = Target -> EnclosingTarget

M[Target, enclosing.class]  = Target -> EnclosingTarget

M[Target, enclosing.struct] = Target -> EnclosingTarget

M[Target, enclosing.trait]  = Target -> EnclosingTarget

M[Target, callsite.block]   = Target -> CallsiteTarget


EnclosingTarget

M[EnclosingTarget, enclosing.module] = EnclosingTarget -> "enclosing.module"

M[EnclosingTarget, enclosing.class]  = EnclosingTarget -> "enclosing.class"

M[EnclosingTarget, enclosing.struct] = EnclosingTarget -> "enclosing.struct"

M[EnclosingTarget, enclosing.trait]  = EnclosingTarget -> "enclosing.trait"


CallsiteTarget

M[CallsiteTarget, callsite.block] = CallsiteTarget -> "callsite.block" "." Anchor


Anchor

M[Anchor, "head"] = Anchor -> "head"

M[Anchor, "tail"] = Anchor -> "tail"

M[Anchor, "here"] = Anchor -> "here"


LetConst

M[LetConst, "let"]   = LetConst -> "let"

M[LetConst, "const"] = LetConst -> "const"


ElseOpt

M[ElseOpt, "else"]    = ElseOpt -> "else" ":" NEWLINE INDENT IntroSpecLines DEDENT

M[ElseOpt, NEWLINE]   = ElseOpt -> ε

M[ElseOpt, ","]       = ElseOpt -> ε

M[ElseOpt, ")"]       = ElseOpt -> ε


IntroSpecLines

For any lookahead in FIRST(IntroSpecLine):
M[IntroSpecLines, lookahead] = IntroSpecLines -> IntroSpecLine IntroSpecLines

M[IntroSpecLines, DEDENT] = IntroSpecLines -> ε



---

7.4 InjectSpec

InjectSpec

M[InjectSpec, callsite.block] = InjectSpec -> "callsite.block" "." Anchor "." CodeKind


CodeKind

M[CodeKind, "stmt"]  = CodeKind -> "stmt"

M[CodeKind, "block"] = CodeKind -> "block"



---

7.5 Macro body lines (macro-specific disambiguation)

To keep this LL(1), "const_eval" and "emit" must be reserved and not usable as identifiers.

MacroBodyLines

If lookahead is DEDENT: MacroBodyLines -> ε

Otherwise: MacroBodyLines -> MacroStmtLine MacroBodyLines


MacroStmt

M[MacroStmt, "const_eval"] = MacroStmt -> ConstEvalStmt

M[MacroStmt, "emit"]       = MacroStmt -> EmitStmt

Otherwise: MacroStmt -> SimpleStmt (delegated to the base grammar)



---

8) One-pass compilation model (what “one pass” means here)

Single left-to-right parse with immediate symbol updates:

1. Parse macro declarations as encountered; store:

contract AST

body AST



2. When encountering a macro call IDENT!("..."):

look up macro (must be defined earlier in the file/module)

parse args

const-evaluate only what the contract needs (template substitutions; for bounds; if conditions)

apply intro stubs immediately to the symbol table at the declared target scope

register inject effects on the current block (head/tail/here buckets)



3. Continue parsing subsequent code with the updated symbol table available for name resolution and IDE completion.



Required constraints for true one-pass

Macros must be declared before use in the same module/file.

All identifiers used in QIDENT templates inside the contract must be const arguments or const loop indices.

All intro let/const stubs must include : Type (no untyped locals in the contract).

callsite.block.head macros: must appear before any non-macro statement in the block (enforced as a structural rule).

callsite.block.tail macros: must appear after all non-macro statements in the block.

Introduced names must not shadow existing symbols in the target scope; conflicting intros are compile-time errors.



---

9) Body examples (complete)

9.1 Member function introduction + returns

macro define_counter(NAME: Str const) -> (
  returns result: (init: Int, step: Int),
  intro counter_fn: enclosing.class.fn "{NAME}Counter"(start: Int) -> Int
):
  const_eval:
    const init = 0
    const step = 1

  emit counter_fn:
    fn "{NAME}Counter"(start: Int) -> Int:
      return start + step

  emit result:
    (init: init, step: step)

Use:

class Demo:
  define_counter!("User")

  fn run(self) -> Int:
    return self.UserCounter(10)

9.2 Const-unrolled declarations (axes)

macro gen_axes(BASE: Str const, N: Int const) -> (
  intro axes:
    for i in 0 .. N:
      enclosing.class.fn "{BASE}{i}"(v: Vec[N]) -> Int
):
  emit axes:
    for i in 0 .. N:
      fn "{BASE}{i}"(v: Vec[N]) -> Int:
        return v[i]


---

## Implementation Status

This specification describes the **target design** for Simple's macro system. Current implementation status:

### Implemented Components
1. **AST Types** (`src/parser/src/ast.rs`)
   - `MacroDef`, `MacroContractItem`, `MacroIntro`, `MacroInject`, `MacroReturns`
   - All target/anchor/kind enums

2. **Contract Processing** (`src/compiler/src/macro_contracts.rs` - 390 lines)
   - `process_macro_contract()` - Processes all contract items
   - Const-eval engine for `For` and `If` const-time unrolling
   - Template substitution engine
   - Shadow detection and validation

3. **Macro Expansion** (`src/compiler/src/interpreter_macro.rs` - 1270 lines)
   - User-defined macro expansion
   - `const_eval:` and `emit` blocks
   - Hygiene system (gensym-based)
   - Template substitution in strings

4. **Built-in Macros**
   - `println!`, `print!`, `vec!`, `assert!`, `assert_eq!`, `panic!`, `format!`, `dbg!`

### Pending Integration
1. **Symbol Table Mutation**
   - Contract processing works but doesn't register symbols yet
   - Need mutable symbol tables during expansion

2. **LL(1) Parser Integration**
   - Currently interpreter-driven expansion
   - Parser has macro AST but doesn't invoke contracts

3. **IDE Protocol**
   - Infrastructure ready but not exposed to LSP
   - Would enable autocomplete for introduced symbols

4. **Code Injection**
   - Injection points tracked but code not spliced

### Next Steps
See `doc/contracts/macro_contracts.md` for detailed integration plan.

### Test Coverage
- 13 tests in `src/driver/tests/interpreter_macros.rs`
- Basic macro expansion fully tested
- Contract integration tests pending

---

If you want the parse table expanded to include the exact FIRST(Type) and FIRST(ConstExpr) (instead of treating them as opaque), paste your current type-expression and const-expression grammar (or point me at doc/spec/syntax.md / the parser module), and I will integrate them into the same LL(1) table without changing the macro contract surface.
