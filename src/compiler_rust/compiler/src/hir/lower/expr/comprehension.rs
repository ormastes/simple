//! List comprehensions use the same typed loop and array append as statements.
use simple_parser::{ast::Mutability, Expr, Pattern};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

type SavedBinding = (String, Option<usize>, Option<String>);

impl Lowerer {
    pub(super) fn lower_list_comprehension(
        &mut self,
        expression: &Expr,
        pattern: &Pattern,
        iterable: &Expr,
        condition: Option<&Expr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Resolve the iterable in the enclosing scope, before shadowing names.
        // HirStmt::For evaluates it once, including for an empty input.
        let iterable = self.lower_expr(iterable, ctx)?;
        let element_ty = match self.module.types.get(iterable.ty) {
            Some(HirType::Array { element, .. }) => Some(*element),
            Some(HirType::String) => Some(TypeId::STRING),
            _ => None,
        }
        .or_else(|| match &iterable.kind {
            HirExprKind::BuiltinCall { name, args } if name == "rt_range" || name == "rt_range_inclusive" => {
                let integer_bound = |ty| {
                    matches!(
                        ty,
                        TypeId::I8
                            | TypeId::I16
                            | TypeId::I32
                            | TypeId::I64
                            | TypeId::U8
                            | TypeId::U16
                            | TypeId::U32
                            | TypeId::U64
                            | TypeId::ANY
                    )
                };
                if args.len() != 2 || !args.iter().all(|arg| integer_bound(arg.ty)) {
                    return None;
                }
                // Match MIR range_counter_type: a typed end bound wins,
                // then a typed start, then the generic integer counter.
                Some(if args[1].ty != TypeId::ANY {
                    args[1].ty
                } else if args[0].ty != TypeId::ANY {
                    args[0].ty
                } else {
                    TypeId::I64
                })
            }
            _ if iterable.ty == TypeId::ANY => Some(TypeId::ANY),
            _ => None,
        })
        .ok_or_else(|| LowerError::Unsupported("list comprehension requires an iterable value".to_string()))?;

        let item_name = format!("$comprehension_item_{}", ctx.locals.len());
        let item = ctx.add_local(item_name.clone(), element_ty, Mutability::Immutable);
        let mut bindings = vec![(item_name.clone(), None, None)];
        // Restore every binding even when pattern/filter/body lowering fails.
        // Keep allocated slots: the lowered expressions reference their indices.
        let result = (|| {
            let mut body = Vec::new();
            self.bind_comprehension_pattern(
                pattern,
                HirExpr {
                    kind: HirExprKind::Local(item),
                    ty: element_ty,
                },
                ctx,
                &mut bindings,
                &mut body,
            )?;
            let filter = condition.map(|value| self.lower_condition(value, ctx)).transpose()?;
            if let Some(filter) = &filter {
                if filter.ty != TypeId::BOOL && filter.ty != TypeId::ANY {
                    return Err(LowerError::Unsupported(
                        "list comprehension filter must be Boolean".to_string(),
                    ));
                }
            }
            let value = self.lower_expr(expression, ctx)?;
            let projected_ty = match &value.kind {
                HirExprKind::Lambda { params, body, .. } => self.module.types.register(HirType::Function {
                    params: params.iter().map(|(_, ty)| *ty).collect(),
                    ret: body.ty,
                }),
                _ => value.ty,
            };
            let result_ty = self.module.types.register(HirType::Array {
                element: projected_ty,
                size: None,
            });
            let result_name = format!("$comprehension_result_{}", ctx.locals.len());
            let result = ctx.add_local(result_name.clone(), result_ty, Mutability::Mutable);
            bindings.push((result_name, None, None));
            let result_ref = HirExpr {
                kind: HirExprKind::Local(result),
                ty: result_ty,
            };
            let append = HirStmt::Expr(HirExpr {
                kind: HirExprKind::MethodCall {
                    receiver: Box::new(result_ref.clone()),
                    method: "push".to_string(),
                    args: vec![value],
                    dispatch: DispatchMode::Dynamic,
                },
                ty: result_ty,
            });
            body.push(match filter {
                Some(condition) => HirStmt::If {
                    condition,
                    then_block: vec![append],
                    else_block: None,
                    span: None,
                },
                None => append,
            });
            Ok(HirExpr {
                kind: HirExprKind::Block(vec![
                    HirStmt::Let {
                        local_index: result,
                        ty: result_ty,
                        value: Some(HirExpr {
                            kind: HirExprKind::Array(vec![]),
                            ty: result_ty,
                        }),
                    },
                    HirStmt::For {
                        pattern: item_name,
                        pattern_local: Some(item),
                        iterable,
                        body,
                        simd_requested: false,
                        invariants: vec![],
                    },
                    HirStmt::Expr(result_ref),
                ]),
                ty: result_ty,
            })
        })();
        for (name, previous, hint) in bindings.into_iter().rev() {
            ctx.restore_name_binding(&name, previous);
            ctx.static_call_type_hints.remove(&name);
            if let Some(hint) = hint {
                ctx.static_call_type_hints.insert(name, hint);
            }
        }
        result
    }

    fn bind_comprehension_pattern(
        &mut self,
        pattern: &Pattern,
        value: HirExpr,
        ctx: &mut FunctionContext,
        bindings: &mut Vec<SavedBinding>,
        statements: &mut Vec<HirStmt>,
    ) -> LowerResult<()> {
        match pattern {
            Pattern::Identifier(name) | Pattern::MutIdentifier(name) => {
                if bindings.iter().any(|(bound, _, _)| bound == name) {
                    return Err(LowerError::Unsupported(format!(
                        "duplicate list comprehension binding: {name}",
                    )));
                }
                bindings.push((name.clone(), ctx.lookup(name), ctx.static_call_type_hints.remove(name)));
                let mutability = if matches!(pattern, Pattern::MutIdentifier(_)) {
                    Mutability::Mutable
                } else {
                    Mutability::Immutable
                };
                let local = ctx.add_local(name.clone(), value.ty, mutability);
                statements.push(HirStmt::Let {
                    local_index: local,
                    ty: value.ty,
                    value: Some(value),
                });
            }
            Pattern::Wildcard => {}
            Pattern::Tuple(patterns) => {
                let types = match self.module.types.get(value.ty) {
                    Some(HirType::Tuple(types)) if types.len() == patterns.len() => types.clone(),
                    Some(HirType::LabeledTuple(fields)) if fields.len() == patterns.len() => {
                        fields.iter().map(|(_, ty)| *ty).collect()
                    }
                    _ if value.ty == TypeId::ANY => vec![TypeId::ANY; patterns.len()],
                    _ => {
                        return Err(LowerError::Unsupported(
                            "list comprehension tuple pattern must match the iterable element type".to_string(),
                        ))
                    }
                };
                for (index, (pattern, ty)) in patterns.iter().zip(types).enumerate() {
                    self.bind_comprehension_pattern(
                        pattern,
                        HirExpr {
                            kind: HirExprKind::Index {
                                receiver: Box::new(value.clone()),
                                index: Box::new(HirExpr {
                                    kind: HirExprKind::Integer(index as i64),
                                    ty: TypeId::I64,
                                }),
                            },
                            ty,
                        },
                        ctx,
                        bindings,
                        statements,
                    )?;
                }
            }
            _ => {
                return Err(LowerError::Unsupported(
                    "list comprehension supports identifier, wildcard, and tuple bindings".to_string(),
                ))
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower::tests::parse_and_lower;

    fn returned(module: &HirModule) -> &HirExpr {
        module.functions[0]
            .body
            .iter()
            .find_map(|statement| match statement {
                HirStmt::Return(Some(value)) => Some(value),
                _ => None,
            })
            .expect("return expression")
    }

    #[test]
    fn list_comprehension_has_typed_array_loop_and_result() {
        let module = parse_and_lower("fn projected():\n    return [for x in [1, 2]: x.to_text()]\n").unwrap();
        let result = returned(&module);
        assert!(matches!(
            module.types.get(result.ty),
            Some(HirType::Array {
                element: TypeId::STRING,
                size: None
            })
        ));
        let HirExprKind::Block(statements) = &result.kind else {
            panic!("not a comprehension block")
        };
        assert_eq!(statements.len(), 3);
        let HirStmt::Let {
            local_index,
            value: Some(empty),
            ..
        } = &statements[0]
        else {
            panic!("result initializer")
        };
        assert!(matches!(&empty.kind, HirExprKind::Array(values) if values.is_empty()));
        let HirStmt::For {
            pattern_local: Some(item),
            body,
            ..
        } = &statements[1]
        else {
            panic!("generator loop")
        };
        assert_eq!(module.functions[0].locals[*item].ty, TypeId::I64);
        assert!(
            matches!(&body[1], HirStmt::Expr(HirExpr { kind: HirExprKind::MethodCall { method, .. }, .. }) if method == "push")
        );
        assert!(
            matches!(&statements[2], HirStmt::Expr(HirExpr { kind: HirExprKind::Local(index), .. }) if index == local_index)
        );
    }

    #[test]
    fn list_comprehension_filter_guards_projection() {
        let module = parse_and_lower("fn filtered():\n    return [for x in [1, 2] if x > 1: x * 2]\n").unwrap();
        let HirExprKind::Block(statements) = &returned(&module).kind else {
            panic!("block")
        };
        let HirStmt::For { body, .. } = &statements[1] else {
            panic!("loop")
        };
        let HirStmt::If {
            condition,
            then_block,
            else_block,
            ..
        } = &body[1]
        else {
            panic!("filter")
        };
        assert_eq!(condition.ty, TypeId::BOOL);
        assert_eq!(then_block.len(), 1);
        assert!(else_block.is_none());
        assert!(
            matches!(&then_block[0], HirStmt::Expr(HirExpr { kind: HirExprKind::MethodCall { args, .. }, .. }) if matches!(args[0].kind, HirExprKind::Binary { .. }))
        );
    }

    #[test]
    fn list_comprehension_restores_outer_binding_and_resolves_iterable_first() {
        let module = parse_and_lower(
            "fn scoped():\n    val xs = [1, 2]\n    val result = [for xs in xs: xs + 1]\n    return xs\n",
        )
        .unwrap();
        assert!(matches!(returned(&module).kind, HirExprKind::Local(0)));
        let HirStmt::Let { value: Some(value), .. } = &module.functions[0].body[1] else {
            panic!("binding")
        };
        let HirExprKind::Block(statements) = &value.kind else {
            panic!("block")
        };
        let HirStmt::For { iterable, .. } = &statements[1] else {
            panic!("loop")
        };
        assert!(matches!(iterable.kind, HirExprKind::Local(0)));
    }

    #[test]
    fn list_comprehension_nested_projection_retains_array_element_type() {
        let module =
            parse_and_lower("fn nested():\n    return [for x in [1, 2]: [for x in [3, 4]: x.to_text()]]\n").unwrap();
        let Some(HirType::Array { element, .. }) = module.types.get(returned(&module).ty) else {
            panic!("outer array")
        };
        assert!(matches!(
            module.types.get(*element),
            Some(HirType::Array {
                element: TypeId::STRING,
                ..
            })
        ));
    }

    #[test]
    fn list_comprehension_range_and_string_element_types() {
        for (source, expected) in [
            ("fn result():\n    return [for x in 1..4: x + 1]\n", TypeId::I64),
            (
                "fn result():\n    return [for x in \"ab\": x + \"!\"]\n",
                TypeId::STRING,
            ),
        ] {
            let module = parse_and_lower(source).unwrap();
            assert!(
                matches!(module.types.get(returned(&module).ty), Some(HirType::Array { element, .. }) if *element == expected)
            );
        }
    }

    #[test]
    fn list_comprehension_tuple_and_wildcard_patterns() {
        for source in [
            "fn result():\n    return [for (x, _) in [(1, 2), (3, 4)]: x + 1]\n",
            "fn result():\n    return [for _ in [1, 2]: 7]\n",
        ] {
            let module = parse_and_lower(source).unwrap();
            assert!(matches!(
                module.types.get(returned(&module).ty),
                Some(HirType::Array {
                    element: TypeId::I64,
                    ..
                })
            ));
        }
    }

    #[test]
    fn list_comprehension_mixed_range_bounds_follow_mir_counter_type() {
        let module = parse_and_lower("fn result(limit: u32):\n    return [for x in 0..limit: x]\n").unwrap();
        assert!(matches!(
            module.types.get(returned(&module).ty),
            Some(HirType::Array {
                element: TypeId::U32,
                ..
            })
        ));
        for local in &module.functions[0].locals {
            if local.name == "x" || local.name.starts_with("$comprehension_item_") {
                assert_eq!(local.ty, TypeId::U32);
            }
        }
    }

    #[test]
    fn list_comprehension_array_join_ignores_unrelated_optional_join() {
        let module = parse_and_lower("class ThreadHandle:\n    handle: i64\n    me fn join() -> i64?:\n        nil\n\nfn result():\n    return \"prefix\" + [for value in [\"a\", \"b\"]: value].join(\",\")\n").unwrap();
        let function = module
            .functions
            .iter()
            .find(|function| function.name == "result")
            .unwrap();
        let value = function
            .body
            .iter()
            .find_map(|statement| match statement {
                HirStmt::Return(Some(value)) => Some(value),
                _ => None,
            })
            .unwrap();
        assert_eq!(value.ty, TypeId::STRING);
        let HirExprKind::Binary { right, .. } = &value.kind else {
            panic!("text concatenation")
        };
        assert_eq!(right.ty, TypeId::STRING);
    }

    #[test]
    fn list_comprehension_does_not_leak_generator_binding() {
        assert!(parse_and_lower(
            "fn invalid():\n    val result = [for private_name in [1]: private_name]\n    return private_name\n"
        )
        .is_err());
    }

    #[test]
    fn list_comprehension_rejects_invalid_filter_iterable_and_names() {
        for source in [
            "fn invalid():\n    return [for x in 5: x]\n",
            "fn invalid():\n    return [for x in (1, 2): x]\n",
            "fn invalid():\n    return [for x in 1.0..3.0: x]\n",
            "fn invalid():\n    return [for x in \"a\"..\"z\": x]\n",
            "fn invalid():\n    return [for x in [1] if 7: x]\n",
            "fn invalid():\n    return [for x in [1]: missing]\n",
            "fn invalid():\n    return [for (x, x) in [(1, 2)]: x]\n",
            "fn invalid():\n    return [for (x, y) in [1, 2]: x]\n",
        ] {
            assert!(parse_and_lower(source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn list_comprehension_restores_context_on_error_even_when_lenient() {
        let mut lowerer = Lowerer::new();
        lowerer.set_lenient_types(true);
        let mut ctx = FunctionContext::new(TypeId::ANY);
        let original = ctx.add_local("x".to_string(), TypeId::STRING, Mutability::Immutable);
        ctx.static_call_type_hints
            .insert("x".to_string(), "OriginalType".to_string());
        let result = lowerer.lower_list_comprehension(
            &Expr::Integer(0),
            &Pattern::Tuple(vec![
                Pattern::Identifier("x".to_string()),
                Pattern::Literal(Box::new(Expr::Integer(0))),
            ]),
            &Expr::Array(vec![Expr::Tuple(vec![Expr::Integer(1), Expr::Integer(2)])]),
            None,
            &mut ctx,
        );
        assert!(result.is_err());
        assert_eq!(ctx.lookup("x"), Some(original));
        assert_eq!(ctx.local_map.len(), 1);
        assert_eq!(
            ctx.static_call_type_hints.get("x").map(String::as_str),
            Some("OriginalType")
        );
    }

    #[test]
    #[ignore = "requires an explicitly selected runtime capsule and native toolchain"]
    fn native_list_comprehension_fixtures() {
        use crate::pipeline::native_project::{NativeBuildConfig, NativeProjectBuilder};
        use std::{path::PathBuf, process::Command, time::Instant};

        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../..")
            .canonicalize()
            .unwrap();
        let runtime = PathBuf::from(std::env::var("SIMPLE_RUNTIME_PATH").expect("explicit runtime capsule"));
        assert!(runtime.is_dir(), "runtime capsule must exist");
        let evidence = root.join("build/native_probe/list-comprehension/provider-native");
        std::fs::create_dir_all(&evidence).unwrap();
        for name in [
            "list_comprehension_semantics",
            "version_manifest_optional",
            "list_comprehension_join_context",
        ] {
            let output = evidence.join(name);
            let config = NativeBuildConfig {
                entry_closure: true,
                parallel: false,
                num_threads: Some(1),
                cache_dir: Some(evidence.join(format!("{name}-cache"))),
                runtime_bundle: "core-c-bootstrap".to_string(),
                runtime_path: Some(runtime.clone()),
                backend: "cranelift".to_string(),
                ..Default::default()
            };
            let start = Instant::now();
            let built = NativeProjectBuilder::new(root.clone(), output.clone())
                .source_dir(root.join("src/app"))
                .source_dir(root.join("src/lib"))
                .entry_file(root.join(format!("test/fixtures/native/{name}.spl")))
                .config(config)
                .build()
                .expect("native comprehension fixture must compile");
            eprintln!(
                "fixture={name} compiled={} cached={} failed={} build_ms={}",
                built.compiled,
                built.cached,
                built.failed,
                start.elapsed().as_millis()
            );
            assert_eq!(built.failed, 0);
            let run_start = Instant::now();
            let executed = Command::new(&output).current_dir(&root).output().unwrap();
            eprintln!(
                "fixture={name} run_ms={} status={}",
                run_start.elapsed().as_millis(),
                executed.status
            );
            std::fs::write(evidence.join(format!("{name}.stdout")), &executed.stdout).unwrap();
            std::fs::write(evidence.join(format!("{name}.stderr")), &executed.stderr).unwrap();
            assert!(
                executed.status.success(),
                "{name}: {}",
                String::from_utf8_lossy(&executed.stderr)
            );
            let expected = std::fs::read(root.join(format!("test/fixtures/native/{name}.expected"))).unwrap();
            assert_eq!(executed.stdout, expected, "exact side-effect/value oracle: {name}");
        }
    }
}
