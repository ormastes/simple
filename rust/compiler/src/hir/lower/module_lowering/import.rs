use simple_parser as ast;

use crate::hir::lower::lowerer::Lowerer;

impl Lowerer {
    /// Convert an import statement to HIR representation.
    pub(super) fn lower_import(
        &self,
        path: &ast::ModulePath,
        target: &ast::ImportTarget,
        is_type_only: bool,
    ) -> crate::hir::HirImport {
        let from_path = path.segments.clone();
        let (items, is_glob) = self.flatten_import_target(target);

        crate::hir::HirImport {
            from_path,
            items,
            is_glob,
            is_type_only,
        }
    }

    /// Flatten an ImportTarget into a list of (name, alias) pairs.
    pub(super) fn flatten_import_target(&self, target: &ast::ImportTarget) -> (Vec<(String, Option<String>)>, bool) {
        match target {
            ast::ImportTarget::Single(name) => (vec![(name.clone(), None)], false),
            ast::ImportTarget::Aliased { name, alias } => (vec![(name.clone(), Some(alias.clone()))], false),
            ast::ImportTarget::Group(targets) => {
                let mut items = Vec::new();
                for t in targets {
                    let (mut nested_items, _) = self.flatten_import_target(t);
                    items.append(&mut nested_items);
                }
                (items, false)
            }
            ast::ImportTarget::Glob => (Vec::new(), true),
        }
    }
}
