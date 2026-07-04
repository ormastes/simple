# parser_/_`src/compiler/`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-COMPILER-012-2"></a>FR-COMPILER-012-2 | FR-COMPILER-012 — Fix `expect (expr) == val` parser precedence | `expect (true and true) == true` is currently parsed as `(expect(true and true)) == true` — i.e., `expect` consumes the parenthesized sub-expression as its argument and the trailing `== true` is evaluated against the return value of `expect | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
