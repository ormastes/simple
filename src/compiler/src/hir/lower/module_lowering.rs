use simple_parser::{self as ast, Module, Node};

use super::context::FunctionContext;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use super::super::types::*;

impl Lowerer {
    pub fn lower_module(mut self, ast_module: &Module) -> LowerResult<HirModule> {
        self.module.name = ast_module.name.clone();

        // First pass: collect type and function declarations
        for item in &ast_module.items {
            match item {
                Node::Struct(s) => {
                    self.register_struct(s)?;
                }
                Node::Function(f) => {
                    let ret_ty = self.resolve_type_opt(&f.return_type)?;
                    self.globals.insert(f.name.clone(), ret_ty);
                }
                Node::Class(c) => {
                    let fields: Vec<_> = c
                        .fields
                        .iter()
                        .map(|f| {
                            (
                                f.name.clone(),
                                self.resolve_type(&f.ty).unwrap_or(TypeId::VOID),
                            )
                        })
                        .collect();
                    self.module.types.register_named(
                        c.name.clone(),
                        HirType::Struct {
                            name: c.name.clone(),
                            fields,
                        },
                    );
                }
                Node::Enum(e) => {
                    let variants = e
                        .variants
                        .iter()
                        .map(|v| {
                            let fields = v.fields.as_ref().map(|types| {
                                types
                                    .iter()
                                    .map(|t| self.resolve_type(t).unwrap_or(TypeId::VOID))
                                    .collect()
                            });
                            (v.name.clone(), fields)
                        })
                        .collect();
                    self.module.types.register_named(
                        e.name.clone(),
                        HirType::Enum {
                            name: e.name.clone(),
                            variants,
                        },
                    );
                }
                Node::Trait(_)
                | Node::Actor(_)
                | Node::TypeAlias(_)
                | Node::Impl(_)
                | Node::Extern(_)
                | Node::Macro(_)
                | Node::Unit(_)
                | Node::UnitFamily(_) => {}
                Node::Let(_)
                | Node::Const(_)
                | Node::Static(_)
                | Node::Assignment(_)
                | Node::Return(_)
                | Node::If(_)
                | Node::Match(_)
                | Node::For(_)
                | Node::While(_)
                | Node::Loop(_)
                | Node::Break(_)
                | Node::Continue(_)
                | Node::Context(_)
                | Node::With(_)
                | Node::Expression(_) => {}
                Node::ModDecl(_)
                | Node::UseStmt(_)
                | Node::CommonUseStmt(_)
                | Node::ExportUseStmt(_)
                | Node::AutoImportStmt(_) => {}
            }
        }

        // Second pass: lower function bodies
        for item in &ast_module.items {
            if let Node::Function(f) = item {
                let hir_func = self.lower_function(f)?;
                self.module.functions.push(hir_func);
            }
        }

        Ok(self.module)
    }

    fn register_struct(&mut self, s: &ast::StructDef) -> LowerResult<TypeId> {
        let mut fields = Vec::new();
        for field in &s.fields {
            let ty = self.resolve_type(&field.ty)?;
            fields.push((field.name.clone(), ty));
        }

        let hir_type = HirType::Struct {
            name: s.name.clone(),
            fields,
        };

        Ok(self.module.types.register_named(s.name.clone(), hir_type))
    }

    fn lower_function(&mut self, f: &ast::FunctionDef) -> LowerResult<HirFunction> {
        let return_type = self.resolve_type_opt(&f.return_type)?;
        let mut ctx = FunctionContext::new(return_type);

        // Add parameters as locals
        for param in &f.params {
            let ty = if let Some(t) = &param.ty {
                self.resolve_type(t)?
            } else {
                return Err(LowerError::MissingParameterType(param.name.clone()));
            };
            ctx.add_local(param.name.clone(), ty, param.mutability);
        }

        let params: Vec<LocalVar> = ctx.locals.clone();
        let params_len = params.len();

        let body = self.lower_block(&f.body, &mut ctx)?;

        Ok(HirFunction {
            name: f.name.clone(),
            params,
            locals: ctx.locals[params_len..].to_vec(),
            return_type,
            body,
            visibility: f.visibility,
        })
    }
}
