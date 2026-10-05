# Phase4 loader helper owners

Status: source repair prepared; native validation pending.

The completed Windows full-CLI HIR pass reports unresolved `bytes_len`,
`code_bytes_len`, and `type_args_is_empty` in module_loader, plus
`ObjTaker__with_compiler_context` in object_provider. The three array helpers
exist only on `compiler.loader.compiler_sffi`, whereas module_loader imports
the inner `compiler.loader.loader.compiler_sffi` implementation. Import the
three existing compatibility helpers explicitly; preserve the shared TypeInfo
owner and executable byte-size calculations.

ObjectProvider now imports and calls the existing
`objtaker_with_compiler_context` wrapper instead of spelling an undeclared
generated static-method symbol. The wrapper delegates to the real ObjTaker
constructor and preserves the supplied CompilerContext and configuration.

Three actual loader name-mangling cases cover no type arguments, one integer
type, and ordered heterogeneous arguments. They remain UNRUN. Both production
modules still require native compilation and the loader binary suite before
claiming that symbol sizing, JIT execution, or context lifetime is verified.
