#!/usr/bin/env python3
"""
Refactor lowering.rs by extracting match arms into helper methods.
This keeps the code in one file but makes the main dispatch method clean.
"""

# The new lower_expr dispatch method (around 40 lines)
DISPATCH = '''    pub(in crate::hir::lower) fn lower_expr(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        match expr {
            Expr::Integer(_) | Expr::Float(_) | Expr::String(_) | Expr::Bool(_) | Expr::Nil => {
                self.lower_literal(expr)
            }
            Expr::FString(parts) => self.lower_fstring(parts),
            Expr::Identifier(name) => self.lower_identifier(name, ctx),
            Expr::Binary { op, left, right } => self.lower_binary(op, left, right, ctx),
            Expr::Unary { op, operand } => self.lower_unary(op, operand, ctx),
            Expr::Call { callee, args } => self.lower_call(callee, args, ctx),
            Expr::FieldAccess { receiver, field } => self.lower_field_access(receiver, field, ctx),
            Expr::Index { receiver, index } => self.lower_index(receiver, index, ctx),
            Expr::Tuple(exprs) => self.lower_tuple(exprs, ctx),
            Expr::Array(exprs) => self.lower_array(exprs, ctx),
            Expr::VecLiteral(exprs) => self.lower_vec_literal(exprs, ctx),
            Expr::If { condition, then_branch, else_branch } => {
                self.lower_if(condition, then_branch, else_branch.as_deref(), ctx)
            }
            Expr::Lambda { params, body, .. } => self.lower_lambda(params, body, ctx),
            Expr::Yield(value) => self.lower_yield(value.as_deref(), ctx),
            Expr::ContractResult => self.lower_contract_result(ctx),
            Expr::ContractOld(inner) => self.lower_contract_old(inner, ctx),
            Expr::New { kind, expr } => self.lower_new(kind, expr, ctx),
            Expr::MethodCall { receiver, method, args } => {
                self.lower_method_call(receiver, method, args, ctx)
            }
            Expr::StructInit { name, fields } => self.lower_struct_init(name, fields, ctx),
            _ => Err(LowerError::Unsupported(format!("{:?}", expr))),
        }
    }
'''

# Read the original file
with open('/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/expr/lowering.rs', 'r') as f:
    content = f.read()

# Extract the impl block body (everything after "impl Lowerer {" and before the final "}")
impl_start = content.find('impl Lowerer {')
if impl_start == -1:
    print("ERROR: Could not find 'impl Lowerer {'")
    exit(1)

header = content[:impl_start + len('impl Lowerer {')]
impl_body_start = impl_start + len('impl Lowerer {\n')

# Find the closing brace of impl
brace_count = 1
i = impl_body_start
while i < len(content) and brace_count > 0:
    if content[i] == '{':
        brace_count += 1
    elif content[i] == '}':
        brace_count -= 1
    i += 1

impl_end = i - 1
impl_body = content[impl_body_start:impl_end]

# Write the new file
output = header + '\n' + DISPATCH + '\n'

# Now add all the helper methods
output += '''
    // ============================================================================
    // Literal expressions
    // ============================================================================

    fn lower_literal(&self, expr: &Expr) -> LowerResult<HirExpr> {
        match expr {
            Expr::Integer(n) => Ok(HirExpr {
                kind: HirExprKind::Integer(*n),
                ty: TypeId::I64,
            }),
            Expr::Float(f) => Ok(HirExpr {
                kind: HirExprKind::Float(*f),
                ty: TypeId::F64,
            }),
            Expr::String(s) => Ok(HirExpr {
                kind: HirExprKind::String(s.clone()),
                ty: TypeId::STRING,
            }),
            Expr::Bool(b) => Ok(HirExpr {
                kind: HirExprKind::Bool(*b),
                ty: TypeId::BOOL,
            }),
            Expr::Nil => Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            }),
            _ => unreachable!("lower_literal called with non-literal"),
        }
    }

    fn lower_fstring(&self, parts: &[ast::FStringPart]) -> LowerResult<HirExpr> {
        // Check if the FString is a simple literal (no interpolation)
        // If so, convert it to a plain string
        let mut result = String::new();
        let mut all_literal = true;
        for part in parts {
            match part {
                ast::FStringPart::Literal(s) => {
                    result.push_str(s);
                }
                ast::FStringPart::Expr(_) => {
                    all_literal = false;
                    break;
                }
            }
        }
        if all_literal {
            Ok(HirExpr {
                kind: HirExprKind::String(result),
                ty: TypeId::STRING,
            })
        } else {
            Err(LowerError::Unsupported(
                "FString with interpolation not yet supported in native compilation".to_string()
            ))
        }
    }

    // ============================================================================
    // Identifier expressions
    // ============================================================================

    fn lower_identifier(&self, name: &str, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        // Check if this is a contract binding (ret, err, result in postconditions)
        if ctx.is_postcondition_binding(name) {
            return Ok(HirExpr {
                kind: HirExprKind::ContractResult,
                ty: ctx.return_type,
            });
        }
        if ctx.is_error_binding(name) {
            // Error binding also refers to the return value (the error part)
            return Ok(HirExpr {
                kind: HirExprKind::ContractResult,
                ty: ctx.return_type,
            });
        }

        if let Some(idx) = ctx.lookup(name) {
            let ty = ctx.locals[idx].ty;
            Ok(HirExpr {
                kind: HirExprKind::Local(idx),
                ty,
            })
        } else if let Some(ty) = self.globals.get(name).copied() {
            Ok(HirExpr {
                kind: HirExprKind::Global(name.to_string()),
                ty,
            })
        } else {
            Err(LowerError::UnknownVariable(name.to_string()))
        }
    }
'''

# Extract rest of the original implementation for the remaining methods
# We need to extract individual match arms and convert them to methods

print("Refactoring complete! New file will be written.")
print(f"Original file size: {len(content)} chars")
print(f"New dispatch method: ~40 lines")

# For now, let's just write the partial result to see if this approach works
with open('/tmp/lowering_new.rs', 'w') as f:
    f.write(output)
    f.write('\n    // TODO: Add remaining helper methods\n')
    f.write('}\n')

print("Partial output written to /tmp/lowering_new.rs")
print("Full refactoring requires extracting all match arms - doing this manually for safety")
