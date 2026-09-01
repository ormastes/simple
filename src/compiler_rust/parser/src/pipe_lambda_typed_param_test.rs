//! Regression tests for typed pipe-lambda parameters (`|x: i64| ...`).
//! See doc/08_tracking/bug/pipe_lambda_typed_param_parser_gap_2026-08-07.md.

#[cfg(test)]
mod pipe_lambda_typed_param {
    use crate::ast::{Expr, LambdaParam, Node};

    fn parse_expr(src: &str) -> Expr {
        let module = crate::Parser::new(src)
            .parse()
            .unwrap_or_else(|e| panic!("expected `{src}` to parse, got error: {e:?}"));
        let stmt = module
            .items
            .into_iter()
            .next()
            .unwrap_or_else(|| panic!("expected at least one statement in `{src}`"));
        match stmt {
            Node::Expression(e) => e,
            Node::Let(l) => l.value.unwrap_or_else(|| panic!("`let` in `{src}` had no value")),
            other => panic!("expected an expression/let statement in `{src}`, got {other:?}"),
        }
    }

    fn lambda_params(expr: Expr) -> Vec<LambdaParam> {
        match expr {
            Expr::Lambda { params, .. } => params,
            other => panic!("expected Expr::Lambda, got {other:?}"),
        }
    }

    #[test]
    fn single_typed_pipe_lambda_param_parses() {
        let params = lambda_params(parse_expr("val f = |x: i64| x + 1\n"));
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].name, "x");
        assert!(params[0].ty.is_some(), "typed param must record its type");
    }

    #[test]
    fn multi_typed_pipe_lambda_params_parse() {
        let params = lambda_params(parse_expr("val g = |x: i64, y: i64| x + y\n"));
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].name, "x");
        assert_eq!(params[1].name, "y");
        assert!(params[0].ty.is_some());
        assert!(params[1].ty.is_some());
    }

    #[test]
    fn untyped_pipe_lambda_params_still_parse() {
        let params = lambda_params(parse_expr("val h = |x| x + 1\n"));
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].name, "x");
        assert!(params[0].ty.is_none());
    }

    #[test]
    fn backslash_lambda_multi_param_untyped_still_parses() {
        // The backslash-lambda form uses a bare trailing `:` to end its
        // parameter list and start the body -- `: Type` per-param must stay
        // disabled there (allow_types=false), or `\x, y: x + y` would try to
        // parse `x + y` as a type for `y`.
        let params = lambda_params(parse_expr("val k = \\x, y: x + y\n"));
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].name, "x");
        assert_eq!(params[1].name, "y");
        assert!(params[0].ty.is_none());
        assert!(params[1].ty.is_none());
    }
}
