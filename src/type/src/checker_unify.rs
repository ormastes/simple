impl TypeChecker {
    /// Unify two types, updating the substitution
    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), TypeError> {
        let t1 = t1.apply_subst(&self.subst);
        let t2 = t2.apply_subst(&self.subst);

        match (&t1, &t2) {
            // Same types unify
            (Type::Int, Type::Int) => Ok(()),
            (Type::Float, Type::Float) => Ok(()),
            (Type::Bool, Type::Bool) => Ok(()),
            (Type::Str, Type::Str) => Ok(()),
            (Type::Nil, Type::Nil) => Ok(()),

            // Type variable unification
            (Type::Var(id1), Type::Var(id2)) if id1 == id2 => Ok(()),
            (Type::Var(id), ty) | (ty, Type::Var(id)) => {
                // Occurs check: prevent infinite types
                if ty.contains_var(*id) {
                    return Err(TypeError::OccursCheck {
                        var_id: *id,
                        ty: ty.clone(),
                    });
                }
                self.subst.insert(*id, ty.clone());
                Ok(())
            }

            // Named types match by name
            (Type::Named(n1), Type::Named(n2)) if n1 == n2 => Ok(()),

            // Arrays unify if elements unify
            (Type::Array(e1), Type::Array(e2)) => self.unify(e1, e2),

            // Tuples unify if all elements unify
            (Type::Tuple(ts1), Type::Tuple(ts2)) if ts1.len() == ts2.len() => {
                for (a, b) in ts1.iter().zip(ts2.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }

            // Functions unify if params and return types unify
            (
                Type::Function {
                    params: p1,
                    ret: r1,
                },
                Type::Function {
                    params: p2,
                    ret: r2,
                },
            ) if p1.len() == p2.len() => {
                for (a, b) in p1.iter().zip(p2.iter()) {
                    self.unify(a, b)?;
                }
                self.unify(r1, r2)
            }

            // Generic types unify if name and args match
            (Type::Generic { name: n1, args: a1 }, Type::Generic { name: n2, args: a2 })
                if n1 == n2 && a1.len() == a2.len() =>
            {
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }

            // Optional types
            (Type::Optional(i1), Type::Optional(i2)) => self.unify(i1, i2),

            // Dict types
            (Type::Dict { key: k1, value: v1 }, Type::Dict { key: k2, value: v2 }) => {
                self.unify(k1, k2)?;
                self.unify(v1, v2)
            }

            // Type parameters
            (Type::TypeParam(n1), Type::TypeParam(n2)) if n1 == n2 => Ok(()),

            // Union types are compatible if one is a member of the other
            (Type::Union(members), other) | (other, Type::Union(members)) => {
                // Check if other matches any member
                for member in members {
                    if self.types_compatible(other, member) {
                        return Ok(());
                    }
                }
                Err(TypeError::Mismatch {
                    expected: t1.clone(),
                    found: t2.clone(),
                })
            }

            // Borrow types unify if inner types unify
            (Type::Borrow(i1), Type::Borrow(i2)) => self.unify(i1, i2),
            (Type::BorrowMut(i1), Type::BorrowMut(i2)) => self.unify(i1, i2),

            // &mut T can coerce to &T (mutable borrow is subtype of immutable borrow)
            (Type::Borrow(i1), Type::BorrowMut(i2)) => self.unify(i1, i2),

            // Mismatch
            _ => Err(TypeError::Mismatch {
                expected: t1.clone(),
                found: t2.clone(),
            }),
        }
    }

    /// Get the resolved type (applying all substitutions)
    pub fn resolve(&self, ty: &Type) -> Type {
        ty.apply_subst(&self.subst)
    }

    /// Convert an AST type annotation to a type checker Type
    pub fn ast_type_to_type(&mut self, ast_ty: &AstType) -> Type {
        match ast_ty {
            AstType::Simple(name) => {
                // Check if it's a type parameter first
                if let Some(ty) = self.type_params.get(name) {
                    return ty.clone();
                }
                // Map common type names
                match name.as_str() {
                    "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "int" | "Int" => {
                        Type::Int
                    }
                    "f32" | "f64" | "float" | "Float" => Type::Float,
                    "bool" | "Bool" => Type::Bool,
                    "str" | "String" | "Str" => Type::Str,
                    "nil" | "Nil" | "None" => Type::Nil,
                    _ => Type::Named(name.clone()),
                }
            }
            AstType::Generic { name, args } => {
                let converted_args: Vec<Type> =
                    args.iter().map(|a| self.ast_type_to_type(a)).collect();
                Type::Generic {
                    name: name.clone(),
                    args: converted_args,
                }
            }
            AstType::Union(types) => {
                let converted: Vec<Type> = types.iter().map(|t| self.ast_type_to_type(t)).collect();
                Type::Union(converted)
            }
            AstType::Tuple(types) => {
                let converted: Vec<Type> = types.iter().map(|t| self.ast_type_to_type(t)).collect();
                Type::Tuple(converted)
            }
            AstType::Array { element, .. } => Type::Array(Box::new(self.ast_type_to_type(element))),
            AstType::Function { params, ret } => {
                let param_types: Vec<Type> =
                    params.iter().map(|p| self.ast_type_to_type(p)).collect();
                let ret_type = ret
                    .as_ref()
                    .map(|r| self.ast_type_to_type(r))
                    .unwrap_or(Type::Nil);
                Type::Function {
                    params: param_types,
                    ret: Box::new(ret_type),
                }
            }
            AstType::Optional(inner) => Type::Optional(Box::new(self.ast_type_to_type(inner))),
            AstType::Pointer { inner, kind } => {
                let inner_type = self.ast_type_to_type(inner);
                match kind {
                    PointerKind::Borrow => Type::Borrow(Box::new(inner_type)),
                    PointerKind::BorrowMut => Type::BorrowMut(Box::new(inner_type)),
                    // For other pointer types, treat as their inner type for now
                    _ => inner_type,
                }
            }
            AstType::Constructor { target, args } => {
                let target_type = self.ast_type_to_type(target);
                let args_types = args
                    .as_ref()
                    .map(|a| a.iter().map(|t| self.ast_type_to_type(t)).collect());
                Type::Constructor {
                    target: Box::new(target_type),
                    args: args_types,
                }
            }
            AstType::Simd { lanes, element } => {
                let elem_type = self.ast_type_to_type(element);
                Type::Simd {
                    lanes: *lanes,
                    element: Box::new(elem_type),
                }
            }
        }
    }

    /// Check if a type is compatible with a union type
    pub fn type_matches_union(&self, ty: &Type, union_members: &[Type]) -> bool {
        for member in union_members {
            if self.types_compatible(ty, member) {
                return true;
            }
        }
        false
    }

    /// Check if two types are compatible (for union type checking)
    pub fn types_compatible(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            // Same primitive types
            (Type::Int, Type::Int) => true,
            (Type::Float, Type::Float) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Str, Type::Str) => true,
            (Type::Nil, Type::Nil) => true,
            // Type variables are compatible with anything
            (Type::Var(_), _) | (_, Type::Var(_)) => true,
            // Named types match by name
            (Type::Named(n1), Type::Named(n2)) => n1 == n2,
            // Arrays match if elements match
            (Type::Array(e1), Type::Array(e2)) => self.types_compatible(e1, e2),
            // Tuples match if all elements match
            (Type::Tuple(t1), Type::Tuple(t2)) => {
                t1.len() == t2.len()
                    && t1
                        .iter()
                        .zip(t2.iter())
                        .all(|(a, b)| self.types_compatible(a, b))
            }
            // Union types: check if either is a subset
            (Type::Union(members), other) | (other, Type::Union(members)) => {
                self.type_matches_union(other, members)
            }
            // Generic types match if name and all args match
            (Type::Generic { name: n1, args: a1 }, Type::Generic { name: n2, args: a2 }) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1
                        .iter()
                        .zip(a2.iter())
                        .all(|(x, y)| self.types_compatible(x, y))
            }
            // Functions match if params and return types match
            (
                Type::Function {
                    params: p1,
                    ret: r1,
                },
                Type::Function {
                    params: p2,
                    ret: r2,
                },
            ) => {
                p1.len() == p2.len()
                    && p1
                        .iter()
                        .zip(p2.iter())
                        .all(|(a, b)| self.types_compatible(a, b))
                    && self.types_compatible(r1, r2)
            }
            // Optional types
            (Type::Optional(inner1), Type::Optional(inner2)) => {
                self.types_compatible(inner1, inner2)
            }
            // Dict types
            (Type::Dict { key: k1, value: v1 }, Type::Dict { key: k2, value: v2 }) => {
                self.types_compatible(k1, k2) && self.types_compatible(v1, v2)
            }
            // Type parameters
            (Type::TypeParam(n1), Type::TypeParam(n2)) => n1 == n2,
            // Borrow types
            (Type::Borrow(inner1), Type::Borrow(inner2)) => self.types_compatible(inner1, inner2),
            (Type::BorrowMut(inner1), Type::BorrowMut(inner2)) => {
                self.types_compatible(inner1, inner2)
            }
            // &mut T is compatible with &T (mutable borrow can be used where immutable is expected)
            (Type::Borrow(inner1), Type::BorrowMut(inner2)) => {
                self.types_compatible(inner1, inner2)
            }
            _ => false,
        }
    }
}
