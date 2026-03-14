# Simple Language — Unified Grammar Proposal (Consistency & Improvements)

Date: 2025-12-23

Goals:
- Unify grammar across statements, expressions, AOP predicates, contracts, and SDN embedding.
- Preserve LL(1) for statements with single-token lookahead, use Pratt for expressions.
- Eliminate local ambiguities (paren-less calls, syntactic islands) and align docs with the implemented Rust parser.

Principles:
- Statements introduce blocks with ":" followed by INDENT/DEDENT tokens from the lexer.
- Expressions use Pratt (precedence climbing). Parenthesis-less calls are allowed only at the top-level statement position.
- Syntactic islands are tokenized by the lexer as single tokens: pc{...} for predicates, sdn{...} for inline SDN.

Tokens (simplified):
- IDENT, SYMBOL (interned), NUMBER, STRING, TRUE, FALSE, NIL
- COLON (":"), INDENT, DEDENT, NEWLINE, LPAREN, RPAREN, LBRACK, RBRACK, LBRACE, RBRACE, COMMA, DOT, ARROW ("->")
- Operators: "+" "-" "*" "/" "%" "==" "!=" "<" ">" "<=" ">=" "||" "&&" "!"

Module:
- Module := { Item }
- Item := Import | Use | LetDecl | ConstDecl | FnDecl | ClassDecl | StructDecl | EnumDecl | TraitDecl | ImplDecl | AopStmt | ContractBlock

Imports/Uses:
- Import := "import" Path [ "as" IDENT ] NEWLINE
- Use    := "use" Path NEWLINE
- Path   := IDENT { "." IDENT }

Declarations:
- LetDecl   := "let" Bindings ":" Type [ "=" Expr ] NEWLINE
- ConstDecl := "const" Bindings ":" Type [ "=" Expr ] NEWLINE
- Bindings  := IDENT { "," IDENT }

Functions:
- FnDecl := "fn" IDENT "(" ParamList? ")" [ "->" Type ] ":" INDENT Block DEDENT
- ParamList := Param { "," Param }
- Param := IDENT [ ":" Type ] [ Decorators? ]
- Decorators := { "@" IDENT [ "(" ArgList? ")" ] }

Classes/Structs/Enums/Traits (shape-only):
- ClassDecl  := "class" IDENT ":" INDENT ClassBody DEDENT
- StructDecl := "struct" IDENT ":" INDENT StructBody DEDENT
- EnumDecl   := "enum" IDENT ":" INDENT EnumBody DEDENT
- TraitDecl  := "trait" IDENT ":" INDENT TraitBody DEDENT
- ImplDecl   := "impl" Trait "for" Type ":" INDENT ImplBody DEDENT

Blocks:
- Block := { Statement }
- Statement := SimpleStmt | IfStmt | WhileStmt | ForStmt | MatchStmt | ReturnStmt | AssignStmt | ExprStmt | AopStmt | ContractBlock

Control:
- IfStmt    := "if" Expr ":" INDENT Block DEDENT { "elif" Expr ":" INDENT Block DEDENT } [ "else:" INDENT Block DEDENT ]
- WhileStmt := "while" Expr ":" INDENT Block DEDENT
- ForStmt   := "for" IDENT "in" Expr ":" INDENT Block DEDENT
- MatchStmt := "match" Expr ":" INDENT { "case" Pattern ":" INDENT Block DEDENT } DEDENT

Assignments/Returns:
- AssignStmt := LValue AssignOp Expr NEWLINE
- LValue := IDENT | MemberAccess | Index
- AssignOp := "=" | "+=" | "-=" | "*=" | "/=" | "%="
- ReturnStmt := "return" Expr? NEWLINE

Expressions (Pratt skeleton):
- Expr := Assignment
- Assignment := OrExpr { AssignOp OrExpr }
- OrExpr := AndExpr { "||" AndExpr }
- AndExpr := Comparison { "&&" Comparison }
- Comparison := Sum { ("==" | "!=" | "<" | ">" | "<=" | ">=") Sum }
- Sum := Product { ("+" | "-") Product }
- Product := Unary { ("*" | "/" | "%") Unary }
- Unary := [ "!" | "-" ] Primary
- Primary := Literal | IDENT | Group | Call | MemberAccess | Index | Lambda
- Group := "(" Expr ")"
- MemberAccess := Primary "." IDENT
- Index := Primary "[" Expr "]"
- Call := Primary "(" ArgList? ")"
- Lambda := "|" ParamList? "|" Expr
- Literal := NUMBER | STRING | TRUE | FALSE | NIL
- ArgList := Arg { "," Arg }
- Arg := Expr | NamedArg
- NamedArg := IDENT ":" Expr

Statement-Level Calls (paren-less):
- ExprStmt := StmtCall NEWLINE | Expr NEWLINE
- StmtCall := IDENT StmtArgList
- StmtArgList := StmtArg { "," StmtArg }
- StmtArg := Expr | NamedArg
- Rule: StmtCall is only recognized when the parser is at statement position (top-level in Block). Nested calls require parentheses → avoids ambiguity.

Patterns (match/case):
- Pattern := Wild | Literal | TuplePat | EnumPat | RangePat | BindPat | OrPat | GuardedPat
- Wild := "_" | "*" | "**" | PrefixWild | SuffixWild
- PrefixWild := IDENT "*"     // e.g., name*
- SuffixWild := "*" IDENT     // e.g., *suffix
- TuplePat := "(" Pattern { "," Pattern } ")"
- EnumPat := IDENT "::" IDENT [ "(" Pattern { "," Pattern } ")" ]
- RangePat := Expr ".." Expr | Expr "..=" Expr
- BindPat := IDENT
- OrPat := Pattern "|" Pattern
- GuardedPat := Pattern "if" Expr

Contracts:
- ContractBlock := InBlock | OutBlock | OutErrBlock | InvariantBlock
- InBlock := "in:" INDENT { ExprStmt } DEDENT
- OutBlock := "out(" "ret" "):" INDENT { ExprStmt } DEDENT
- OutErrBlock := "out_err(" "err" "):" INDENT { ExprStmt } DEDENT
- InvariantBlock := "invariant:" INDENT { ExprStmt } DEDENT

AOP Predicates (Unified):
- PcBlock := "pc" "{" PredExpr "}"
- PredExpr := Disj
- Disj := Conj { "|" Conj }
- Conj := Neg { "&" Neg }
- Neg := [ "!" ] Atom
- Atom := SignatureSel | Selector | GroupPred | PatternSel
- GroupPred := "(" PredExpr ")"
- SignatureSel := RetPat? QNamePat "(" ArgPats? ")"
- RetPat := Type | "*"
- QNamePat := PathPat
- PathPat := IDENT { "." IDENT | "." "*" | "." "**" }
- ArgPats := ArgPat { "," ArgPat } | ".."
- ArgPat := Type | PatternSel | ".."
- Selector := ExecutionSel | WithinSel | AttrSel | EffectSel | TestSel | DecisionSel | ConditionSel | CallSel | InitSel
- ExecutionSel := "execution(" SignatureSel ")"
- WithinSel := "within(" PatternSel ")"
- AttrSel := "attr(" IDENT ")"
- EffectSel := "effect(" EffectSet ")"
- TestSel := "test(" IDENT ")"
- DecisionSel := "decision()"
- ConditionSel := "condition()"
- CallSel := "call(" SignatureSel ")"
- InitSel := "init()"
- PatternSel := PathPat | Wild
- EffectSet := IDENT { "," IDENT }

AOP Statements:
- AopStmt := BindStmt | OnStmt | ArchRulesStmt | ForbidStmt | AllowStmt | MockStmt
- BindStmt := "bind" "on" PcBlock "->" Type [ ScopePrio ] ":" INDENT AdviceBlock DEDENT
- OnStmt := "on" PcBlock ":" INDENT AdviceBlock DEDENT
- ScopePrio := "scope" NUMBER | "priority" NUMBER
- AdviceBlock := { AdviceDecl }
- AdviceDecl := Before | AfterSuccess | AfterError | Around
- Before := "before" ":" INDENT Block DEDENT
- AfterSuccess := "after_success" ":" INDENT Block DEDENT
- AfterError := "after_error" ":" INDENT Block DEDENT
- Around := "around" ":" INDENT Block DEDENT // runtime proceed() enforcement
- ForbidStmt := "forbid" PcBlock NEWLINE
- AllowStmt := "allow" PcBlock NEWLINE
- ArchRulesStmt := "arch_rules:" ":" INDENT { ArchRule } DEDENT
- ArchRule := "import(" PatternSel "," PatternSel ")" NEWLINE
            | "depend(" PatternSel "," PatternSel ")" NEWLINE
            | "use(" PatternSel ")" NEWLINE
            | "export(" PatternSel ")" NEWLINE
            | "config(" STRING ")" NEWLINE
- MockStmt := "mock" IDENT "implements" Trait ":" INDENT MockBody DEDENT

SDN Embedding:
- SdnInline := "sdn" "{" SdnText "}"
- SdnLoad := "sdn::load(" STRING ")"
- Note: The lexer treats SdnInline as a single token with balanced braces; parser consumes it without internal parse.

Ambiguity & Consistency Rules:
- Paren-less calls only at statement position; nested calls must use parentheses.
- pc{...} and sdn{...} are syntactic islands (lexer-level), preventing collisions with normal operators and blocks.
- Named arguments use IDENT ":" Expr consistently in both paren and paren-less forms.
- Range patterns use ".." and "..="; expression ranges use the same tokens only where enabled (feature-gated if needed).

Alignment with Implementation:
- Rust parser: recursive descent for statements, Pratt for expressions — this proposal matches current architecture.
- AOP predicate parsing is centralized (compiler/predicate_parser.rs). The PcBlock island defers predicate expression to that parser.
- SDN remains a separate crate; inline SDN is treated as an opaque value in the language grammar.

Migration & Docs:
- Mark Tree-sitter grammar docs as design references; the authoritative grammar is this LL(1)+Pratt specification aligned with src/parser/*.
- Update doc/spec/syntax.md and lexer_parser.md to reference this proposal and note island tokens.
- Provide editor integration via a forthcoming tree-sitter-simple that mirrors this grammar, excluding islands’ internals.

Rationale (Improvements):
- Formalizes statement-level paren-less call constraints to avoid ambiguity.
- Unifies named-argument syntax, predicate selector sets, and pattern wildcards.
- Clarifies island boundaries for predicates and SDN to prevent grammar collisions.
- Keeps one-pass parsing feasible with minimal lookahead and consistent INDENT/DEDENT handling.

Appendix: Precedence Order (highest → lowest):
1. Group, Call, MemberAccess, Index, Lambda
2. Unary (!, -)
3. Product (*, /, %)
4. Sum (+, -)
5. Comparison (==, !=, <, >, <=, >=)
6. And (&&)
7. Or (||)
8. Assignment (=, +=, -=, *=, /=, %=)
