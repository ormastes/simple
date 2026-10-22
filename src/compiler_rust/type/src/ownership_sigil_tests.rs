// No-GC pointer sigils in the seed HM checker (doc/05_design/language/misc/memory.md).
//
// `&T` unique owner, `*T` shared (Rc), `-T` weak. Before this lane
// `ast_type_to_type` erased all three to the inner type, so `*Node` and
// `&Node` unified with each other and with a plain `Node`. Checks that change
// what a program may do run only in the opt-in no-GC strict mode
// (`@no_gc(strict)` / `SIMPLE_NOGC_STRICT=1`); the default mode keeps the
// legacy pointer-to-inner compatibility so existing code is unaffected.

#[cfg(test)]
mod ownership_sigil_unit_tests {
    use crate::{check_with_nogc_strict, Type, TypeChecker, TypeError};

    fn named(n: &str) -> Type {
        Type::Named(n.into())
    }

    fn parse(src: &str) -> Vec<simple_parser::ast::Node> {
        simple_parser::Parser::new(src)
            .parse()
            .unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"))
            .items
    }

    fn strict(src: &str) -> Result<(), TypeError> {
        check_with_nogc_strict(&parse(src), true)
    }

    fn lenient(src: &str) -> Result<(), TypeError> {
        check_with_nogc_strict(&parse(src), false)
    }

    fn is_ownership(r: &Result<(), TypeError>) -> bool {
        matches!(r, Err(TypeError::Ownership(_)))
    }

    const NODE: &str = "class Node:\n    v: i64\n";

    // ---- distinct types -------------------------------------------------

    #[test]
    fn same_kind_unifies() {
        let mut c = TypeChecker::new();
        assert!(c.unify(&Type::Unique(Box::new(named("Node"))), &Type::Unique(Box::new(named("Node")))).is_ok());
        assert!(c.unify(&Type::Shared(Box::new(named("Node"))), &Type::Shared(Box::new(named("Node")))).is_ok());
        assert!(c.unify(&Type::Weak(Box::new(named("Node"))), &Type::Weak(Box::new(named("Node")))).is_ok());
    }

    #[test]
    fn cross_kind_never_unifies_in_strict_mode() {
        let mut c = TypeChecker::new();
        c.nogc_strict = true;
        let u = Type::Unique(Box::new(named("Node")));
        let s = Type::Shared(Box::new(named("Node")));
        let w = Type::Weak(Box::new(named("Node")));
        assert!(c.unify(&u, &s).is_err());
        assert!(c.unify(&s, &u).is_err());
        assert!(c.unify(&w, &s).is_err());
        assert!(c.unify(&s, &w).is_err());
        assert!(c.unify(&u, &w).is_err());
    }

    #[test]
    fn default_mode_keeps_legacy_erased_unification() {
        // Before this lane the kinds were erased; default mode must not start
        // failing `?`-propagated unifications in existing code.
        let mut c = TypeChecker::new();
        let u = Type::Unique(Box::new(named("Node")));
        let s = Type::Shared(Box::new(named("Node")));
        assert!(c.unify(&u, &s).is_ok());
        assert!(c.unify(&u, &named("Node")).is_ok());
        assert!(c.unify(&s, &named("Other")).is_err());
    }

    #[test]
    fn inner_mismatch_is_still_a_mismatch() {
        let mut c = TypeChecker::new();
        assert!(c
            .unify(&Type::Shared(Box::new(named("A"))), &Type::Shared(Box::new(named("B"))))
            .is_err());
    }

    // ---- constructors ---------------------------------------------------

    #[test]
    fn canonical_and_sugar_constructors_type_the_same() {
        for src in [
            "val a: &Node = new(&) Node(v: 1)",
            "val a: &Node = new& Node(v: 1)",
            "val a: *Node = new(*) Node(v: 1)",
            "val a: *Node = new* Node(v: 1)",
        ] {
            let r = strict(&format!("{NODE}{src}\n"));
            assert!(r.is_ok(), "`{src}` should typecheck in strict mode: {r:?}");
        }
    }

    #[test]
    fn unique_into_shared_slot_rejected() {
        let r = strict(&format!("{NODE}val a: *Node = new(&) Node(v: 1)\n"));
        assert!(is_ownership(&r), "expected ownership error, got {r:?}");
    }

    #[test]
    fn shared_into_unique_slot_rejected() {
        let r = strict(&format!("{NODE}val a: &Node = new(*) Node(v: 1)\n"));
        assert!(is_ownership(&r), "expected ownership error, got {r:?}");
    }

    // ---- conversions ----------------------------------------------------

    #[test]
    fn unique_to_shared_requires_explicit_move() {
        let ok = strict(&format!("{NODE}val u: &Node = new(&) Node(v: 1)\nval s: *Node = share(move u)\n"));
        assert!(ok.is_ok(), "share(move u) should be accepted: {ok:?}");
        let bad = strict(&format!("{NODE}val u: &Node = new(&) Node(v: 1)\nval s: *Node = share(u)\n"));
        assert!(is_ownership(&bad), "share(u) without move must be rejected, got {bad:?}");
    }

    #[test]
    fn share_of_shared_rejected() {
        let r = strict(&format!("{NODE}val s: *Node = new(*) Node(v: 1)\nval t: *Node = share(move s)\n"));
        assert!(is_ownership(&r), "share() takes only a unique owner, got {r:?}");
    }

    #[test]
    fn weak_of_shared_and_upgrade_to_option_shared() {
        let ok = strict(&format!(
            "{NODE}val s: *Node = new(*) Node(v: 1)\nval w: -Node = weak_of(s)\nval o: *Node? = w.upgrade()\n"
        ));
        assert!(ok.is_ok(), "weak_of/upgrade chain should typecheck: {ok:?}");
    }

    #[test]
    fn weak_of_unique_rejected() {
        let r = strict(&format!("{NODE}val u: &Node = new(&) Node(v: 1)\nval w: -Node = weak_of(u)\n"));
        assert!(is_ownership(&r), "weak_of(&T) must be rejected, got {r:?}");
    }

    #[test]
    fn upgrade_is_not_a_unique() {
        let r = strict(&format!(
            "{NODE}val s: *Node = new(*) Node(v: 1)\nval w: -Node = weak_of(s)\nval u: &Node = w.upgrade()\n"
        ));
        assert!(is_ownership(&r), "upgrade yields Option<*T>, never &T: {r:?}");
    }

    #[test]
    fn weak_field_read_without_upgrade_rejected() {
        let r = strict(&format!(
            "{NODE}val s: *Node = new(*) Node(v: 1)\nval w: -Node = weak_of(s)\nval x = w.v\n"
        ));
        assert!(is_ownership(&r), "-T must be upgraded before use: {r:?}");
    }

    // ---- bare T == &T under no-GC ----------------------------------------

    #[test]
    fn bare_class_is_unique_in_strict_mode() {
        let r = strict(&format!("{NODE}val a: Node = new(*) Node(v: 1)\n"));
        assert!(is_ownership(&r), "bare `Node` is `&Node` under no-GC, so *Node must not flow in: {r:?}");
        let ok = strict(&format!("{NODE}val a: Node = new(&) Node(v: 1)\n"));
        assert!(ok.is_ok(), "bare `Node` accepts a unique owner: {ok:?}");
    }

    #[test]
    fn bare_new_is_unique_in_strict_mode() {
        let ok = strict(&format!("{NODE}val a: &Node = new Node(v: 1)\n"));
        assert!(ok.is_ok(), "bare `new` constructs a unique owner under no-GC: {ok:?}");
        let bad = strict(&format!("{NODE}val a: *Node = new Node(v: 1)\n"));
        assert!(is_ownership(&bad), "bare `new` is not shared under no-GC: {bad:?}");
    }

    #[test]
    fn bare_value_types_are_not_wrapped() {
        let ok = strict("val a: i64 = 1\nval t: text = \"x\"\n");
        assert!(ok.is_ok(), "primitives stay values: {ok:?}");
    }

    // ---- &mut T == mut T ------------------------------------------------

    #[test]
    fn amp_mut_and_mut_capability_are_one_type_in_strict_mode() {
        let mut c = TypeChecker::new();
        c.nogc_strict = true;
        let a = c.ast_type_to_type(&simple_parser::ast::Type::Pointer {
            kind: simple_parser::ast::PointerKind::BorrowMut,
            inner: Box::new(simple_parser::ast::Type::Simple("Node".into())),
        });
        let b = c.ast_type_to_type(&simple_parser::ast::Type::Capability {
            capability: simple_parser::ast::ReferenceCapability::Exclusive,
            inner: Box::new(simple_parser::ast::Type::Simple("Node".into())),
        });
        assert_eq!(a, b);
        assert!(c.unify(&a, &Type::Unique(Box::new(named("Node")))).is_err());
    }

    // ---- function boundaries -------------------------------------------

    #[test]
    fn return_and_argument_kinds_checked() {
        let bad_ret = strict(&format!("{NODE}fn mk() -> *Node:\n    return new(&) Node(v: 1)\n"));
        assert!(is_ownership(&bad_ret), "returning &T from a *T fn: {bad_ret:?}");
        let bad_arg = strict(&format!(
            "{NODE}fn take(n: *Node) -> i64:\n    return 0\nval x = take(new(&) Node(v: 1))\n"
        ));
        assert!(is_ownership(&bad_arg), "passing &T to a *T param: {bad_arg:?}");
        let ok = strict(&format!(
            "{NODE}fn take(n: *Node) -> i64:\n    return 0\nval x = take(new(*) Node(v: 1))\n"
        ));
        assert!(ok.is_ok(), "matching kinds: {ok:?}");
    }

    // ---- review findings (Opus, stage 1a) ---------------------------------

    #[test]
    fn assignment_keeps_declared_kind() {
        let r = strict(&format!(
            "{NODE}var u: &Node = new(&) Node(v: 1)\nval s: *Node = new(*) Node(v: 2)\nu = s\n"
        ));
        assert!(is_ownership(&r), "assigning *T into a &T variable: {r:?}");
    }

    #[test]
    fn implicit_return_checked() {
        let r = strict(&format!("{NODE}fn f(s: *Node) -> &Node:\n    s\n"));
        assert!(is_ownership(&r), "trailing-expression return of *T from a &T fn: {r:?}");
    }

    #[test]
    fn deref_does_not_launder_shared_into_unique() {
        let r = strict(&format!("{NODE}val s: *Node = new(*) Node(v: 1)\nval u: &Node = *s\n"));
        assert!(is_ownership(&r), "`*s` must not become a fresh unique owner: {r:?}");
    }

    #[test]
    fn nested_containers_checked() {
        let r = strict(&format!(
            "{NODE}fn f(xs: [*Node]) -> i64:\n    val ys: [&Node] = xs\n    return 0\n"
        ));
        assert!(is_ownership(&r), "[*Node] into [&Node]: {r:?}");
        let ok = strict(&format!(
            "{NODE}fn f(xs: [*Node]) -> i64:\n    val ys: [*Node] = xs\n    return 0\n"
        ));
        assert!(ok.is_ok(), "same element kind: {ok:?}");
    }

    #[test]
    fn default_mode_types_are_exactly_legacy() {
        // Default mode erases the sigils exactly as before this lane.
        let mut c = TypeChecker::new();
        let t = c.ast_type_to_type(&simple_parser::ast::Type::Pointer {
            kind: simple_parser::ast::PointerKind::Shared,
            inner: Box::new(simple_parser::ast::Type::Simple("Node".into())),
        });
        assert_eq!(t, named("Node"));
        // `new X` is not inferred in default mode (it used to fall to a fresh
        // variable), so an error inside it cannot newly propagate.
        let r = lenient("val a = new Node(undefined_thing)\n");
        assert!(r.is_ok(), "default-mode `new` must not newly propagate errors: {r:?}");
    }

    #[test]
    fn gate_skips_leading_imports() {
        let src = format!("use std.text\n@no_gc(strict)\n{NODE}val a: *Node = new(&) Node(v: 1)\n");
        assert!(is_ownership(&crate::check(&parse(&src))), "imports before the attribute");
    }

    // ---- opt-in gate -----------------------------------------------------

    #[test]
    fn default_mode_reports_no_ownership_errors() {
        for src in [
            "val a: *Node = new(&) Node(v: 1)",
            "val a: Node = new(*) Node(v: 1)",
            "val s: *Node = new(*) Node(v: 1)\nval x: &Node = s",
        ] {
            let r = lenient(&format!("{NODE}{src}\n"));
            assert!(!is_ownership(&r), "default mode must stay legacy-compatible for `{src}`: {r:?}");
        }
    }

    #[test]
    fn strict_mode_detected_from_module_attribute() {
        let src = format!("@no_gc(strict)\nmod m\n{NODE}val a: *Node = new(&) Node(v: 1)\n");
        let r = crate::check(&parse(&src));
        assert!(is_ownership(&r), "@no_gc(strict) must enable the checks: {r:?}");
        let plain = format!("@no_gc\nmod m\n{NODE}val a: *Node = new(&) Node(v: 1)\n");
        assert!(!is_ownership(&crate::check(&parse(&plain))), "plain @no_gc stays legacy");
        let first = format!("@no_gc(strict)\n{NODE}val a: *Node = new(&) Node(v: 1)\n");
        assert!(is_ownership(&crate::check(&parse(&first))), "file-top @no_gc(strict) on the first item");
        let later = format!("{NODE}@no_gc(strict)\nfn f() -> i64:\n    return 0\nval a: *Node = new(&) Node(v: 1)\n");
        assert!(!is_ownership(&crate::check(&parse(&later))), "a later item's attribute is not file-level");
    }
}
