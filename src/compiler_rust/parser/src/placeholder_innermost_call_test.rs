//! Regressions for
//! `doc/08_tracking/bug/placeholder_lambda_as_fn_param_callback_unevaluated_2026-07-20.md`
//! and
//! `doc/08_tracking/bug/placeholder_lambda_scoping_nested_ordinary_call_2026-08-31.md`.
//!
//! A placeholder belongs to the nearest enclosing call argument, so
//! `print(apply(_1 + 1, 41) + 0)` makes `apply`'s first argument the lambda,
//! not `print`'s whole argument. A higher-order callee (`map`, ...) still owns
//! placeholders of nested ordinary calls.
#[cfg(test)]
mod placeholder_innermost_call {
    fn ast(src: &str) -> String {
        let module = crate::Parser::new(src).parse().expect("source must parse");
        format!("{:?}", module)
    }

    #[test]
    fn nested_ordinary_call_owns_its_placeholder() {
        let dump = ast("fn main():\n    print(apply(_1 + 1, 41) + 0)\n");
        let lambda = dump.find("Lambda").expect("a lambda must be produced");
        let apply = dump.find("\"apply\"").expect("apply call present");
        assert!(lambda > apply, "lambda must sit inside apply's argument, not wrap print's: {dump}");
    }

    #[test]
    fn filed_nested_ordinary_call_owns_second_placeholder_argument() {
        let dump = ast(
            "fn main():\n    expect(index_of_func(\"hello\", _1 == \"l\")).to_equal(2)\n",
        );
        let lambda = dump.find("Lambda").expect("a lambda must be produced");
        let index_of_func = dump
            .find("\"index_of_func\"")
            .expect("index_of_func call present");
        assert!(
            lambda > index_of_func,
            "lambda must sit inside index_of_func's second argument, not wrap expect's: {dump}"
        );
    }

    #[test]
    fn higher_order_callee_still_owns_nested_ordinary_placeholders() {
        let dump = ast("fn main():\n    val r = xs.map(self.f(_.1))\n");
        let lambda = dump.find("Lambda").expect("a lambda must be produced");
        let f = dump.find("\"f\"").expect("f call present");
        assert!(lambda < f, "map's lambda must capture the nested call's placeholder: {dump}");
    }
}
