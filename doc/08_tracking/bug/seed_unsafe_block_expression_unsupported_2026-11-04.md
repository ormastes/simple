# Seed: `unsafe:` block expression unsupported (2026-11-04)

`val x = unsafe:` / `lhs = unsafe:` followed by an indented block failed in the
Rust seed with `semantic: function 'unsafe' not found`: bare `unsafe:` was only a
statement (parser_impl/core.rs); in expression position it became an identifier.
It was deliberately not accepted in general expression position because
`for e in unsafe:` would swallow the header colon.

Fix: `Parser::parse_rhs_expression` (parser/src/expressions/no_paren.rs) accepts
`unsafe:`/`danger:` only as a `val`/`var` initializer or assignment RHS and builds
the existing `Expr::UnsafeBlock` (value = last expression). Interpreter eval was
already in place. JIT lowering was not exercised.

Specs: test/01_unit/compiler/interpreter/unsafe_block_expression_spec.spl;
mir_verify_types_casts_spec (18/20 -> 20/20), mir_verify_driver_route_spec (9/11 -> 11/11).
Not covered: bare `unsafe:` as a call argument or `return` operand.
