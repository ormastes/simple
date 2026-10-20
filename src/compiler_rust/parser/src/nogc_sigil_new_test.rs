//! No-GC pointer-sigil constructors (doc/05_design/language/misc/memory.md).
//!
//! memory.md spells the constructors `new(&) X` / `new(*) X` (canonical); the
//! sugar forms `new& X` / `new* X` must parse to the same pointer kind. Before
//! this lane `new(&) X` was a parse error ("expected expression, found RParen")
//! because the paren branch only knew `new()` and `new(allocator_expr)`.

#[cfg(test)]
mod nogc_sigil_new {
    use crate::ast::{Expr, Node, PointerKind, Type};

    fn parse_let_value(src: &str) -> Expr {
        let module = crate::Parser::new(src)
            .parse()
            .unwrap_or_else(|e| panic!("expected `{src}` to parse, got error: {e:?}"));
        match module.items.into_iter().next() {
            Some(Node::Let(l)) => l.value.unwrap_or_else(|| panic!("no value in `{src}`")),
            Some(Node::Expression(e)) => e,
            other => panic!("expected let/expression in `{src}`, got {other:?}"),
        }
    }

    fn new_kind(src: &str) -> PointerKind {
        match parse_let_value(src) {
            Expr::New { kind, .. } => kind,
            other => panic!("expected Expr::New for `{src}`, got {other:?}"),
        }
    }

    #[test]
    fn paren_amp_is_unique() {
        assert_eq!(new_kind("val u = new(&) Node(1)"), PointerKind::Unique);
    }

    #[test]
    fn paren_star_is_shared() {
        assert_eq!(new_kind("val s = new(*) Node(1)"), PointerKind::Shared);
    }

    #[test]
    fn sugar_matches_canonical() {
        assert_eq!(new_kind("val u = new& Node(1)"), PointerKind::Unique);
        assert_eq!(new_kind("val s = new* Node(1)"), PointerKind::Shared);
    }

    #[test]
    fn allocator_forms_unchanged() {
        assert_eq!(new_kind("val p = new() Node(1)"), PointerKind::Unique);
        assert_eq!(new_kind("val h = new(pool) Node(1)"), PointerKind::Handle);
    }

    fn annotated_type(src: &str) -> Type {
        let module = crate::Parser::new(src)
            .parse()
            .unwrap_or_else(|e| panic!("expected `{src}` to parse, got error: {e:?}"));
        match module.items.into_iter().next() {
            Some(Node::Let(l)) => match (l.ty, l.pattern) {
                (Some(t), _) => t,
                (None, crate::ast::Pattern::Typed { ty, .. }) => ty,
                other => panic!("no annotation in `{src}`: {other:?}"),
            },
            other => panic!("expected let in `{src}`, got {other:?}"),
        }
    }

    #[test]
    fn type_sigils_keep_their_kind() {
        let kind_of = |src: &str| match annotated_type(src) {
            Type::Pointer { kind, .. } => kind,
            other => panic!("expected pointer type for `{src}`, got {other:?}"),
        };
        assert_eq!(kind_of("val u: &Node = x"), PointerKind::Unique);
        assert_eq!(kind_of("val s: *Node = x"), PointerKind::Shared);
        assert_eq!(kind_of("val w: -Node = x"), PointerKind::Weak);
        assert_eq!(kind_of("val m: &mut Node = x"), PointerKind::BorrowMut);
    }
}
