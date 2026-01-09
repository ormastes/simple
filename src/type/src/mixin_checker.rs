// Mixin type checking and composition (Feature #2200, #2201)
//
// This module handles:
// - Field conflict detection between mixins and target types
// - Combining fields from multiple mixins
// - Applying mixins to classes/structs
// - Field resolution including mixin fields

impl TypeChecker {
    /// Check for field name conflicts between mixin and class/struct (Feature #2201)
    pub fn check_mixin_field_conflicts(
        &self,
        mixin_fields: &[(String, Type)],
        target_fields: &[(String, Type)],
    ) -> Vec<String> {
        let mut conflicts = Vec::new();
        for (mixin_name, _mixin_ty) in mixin_fields {
            if target_fields.iter().any(|(target_name, _)| target_name == mixin_name) {
                conflicts.push(mixin_name.clone());
            }
        }
        conflicts
    }

    /// Combine fields from multiple mixins, checking for conflicts (Feature #2201)
    pub fn combine_mixin_fields(
        &self,
        mixins: &[MixinInfo],
    ) -> Result<Vec<(String, Type)>, TypeError> {
        let mut combined = Vec::new();
        let mut seen_names = std::collections::HashSet::new();

        for mixin in mixins {
            for (name, ty) in &mixin.fields {
                if !seen_names.insert(name.clone()) {
                    return Err(TypeError::Other(format!(
                        "Field '{}' defined in multiple mixins",
                        name
                    )));
                }
                combined.push((name.clone(), ty.clone()));
            }
        }
        Ok(combined)
    }

    /// Apply mixin to a class/struct, merging fields and methods (Feature #2201)
    pub fn apply_mixin_to_type(
        &self,
        mixin: &MixinInfo,
        target_name: &str,
        target_fields: &[(String, Type)],
    ) -> Result<Vec<(String, Type)>, TypeError> {
        // Check for conflicts
        let conflicts = self.check_mixin_field_conflicts(&mixin.fields, target_fields);
        if !conflicts.is_empty() {
            return Err(TypeError::Other(format!(
                "Mixin '{}' conflicts with {} on fields: {}",
                mixin.name,
                target_name,
                conflicts.join(", ")
            )));
        }

        // Merge fields
        let mut merged = target_fields.to_vec();
        merged.extend(mixin.fields.clone());
        Ok(merged)
    }

    /// Get all fields for a type including mixin fields (Feature #2201)
    pub fn get_all_fields(&mut self, type_name: &str) -> Vec<(String, Type)> {
        // Check if type has mixin compositions
        if let Some(mixin_refs) = self.compositions.get(type_name).cloned() {
            let mut all_fields = Vec::new();

            // Add mixin fields
            for mixin_ref in &mixin_refs {
                if let Some(mixin_info) = self.mixins.get(&mixin_ref.name).cloned() {
                    // Instantiate if generic
                    if !mixin_ref.type_args.is_empty() {
                        // Convert AST types to Type
                        let type_args: Vec<Type> = mixin_ref
                            .type_args
                            .iter()
                            .map(|ast_ty| self.ast_type_to_type(ast_ty))
                            .collect();

                        if let Ok(instantiated) = mixin_info.instantiate(&type_args) {
                            all_fields.extend(instantiated.fields);
                        }
                    } else {
                        all_fields.extend(mixin_info.fields.clone());
                    }
                }
            }

            // TODO: [type][P3] Add class/struct own fields when they're registered
            all_fields
        } else {
            Vec::new()
        }
    }

    /// Resolve field access on a type, including mixin fields (Feature #2201)
    pub fn resolve_field(&mut self, type_name: &str, field_name: &str) -> Option<Type> {
        let all_fields = self.get_all_fields(type_name);
        all_fields
            .iter()
            .find(|(name, _)| name == field_name)
            .map(|(_, ty)| ty.clone())
    }
}
