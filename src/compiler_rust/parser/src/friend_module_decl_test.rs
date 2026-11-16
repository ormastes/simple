#[cfg(test)]
mod friend_module_decl {
    use crate::Parser;

    fn parse_items(src: &str) -> Result<usize, String> {
        Parser::new(src)
            .parse()
            .map(|m| m.items.len())
            .map_err(|e| format!("{e:?}"))
    }

    #[test]
    fn module_level_friend_directive_parses() {
        // `friend <package.path>` is a module access directive (pure-Simple
        // frontend: enum_module_body.spl); the seed must accept it so lib
        // modules that carry it can be interpreted.
        let src = "friend lib.nogc_sync_mut.io\nfn f() -> i64:\n    1\n";
        let dump = format!("{:?}", Parser::new(src).parse().unwrap().items);
        assert!(!dump.contains("\"friend\""), "friend directive parsed as an expression: {dump}");
        assert_eq!(parse_items(src).unwrap(), 2);
    }

    #[test]
    fn friend_directive_with_keyword_path_segment_parses() {
        let src = "friend lib.common.task_runner\nval x = 1\n";
        assert_eq!(parse_items(src).unwrap(), 2);
    }

    #[test]
    fn friend_remains_usable_as_a_variable_and_call() {
        let src = "val friend = 3\nval y = friend + 1\nfriend(y)\n";
        assert_eq!(parse_items(src).unwrap(), 3);
    }
}

#[cfg(test)]
mod module_access_directives {
    use crate::Parser;

    fn dump(src: &str) -> String {
        format!("{:?}", Parser::new(src).parse().unwrap().items)
    }

    #[test]
    fn internal_export_directive_parses_as_no_op() {
        // pure-Simple frontend: `internal_export NAME` (enum_module_body.spl).
        let src = "internal_export helper_v1\ninternal_export TypeV1\nfn f() -> i64:\n    1\n";
        let d = dump(src);
        assert!(!d.contains("\"internal_export\""), "parsed as a call: {d}");
        assert_eq!(Parser::new(src).parse().unwrap().items.len(), 3);
    }

    #[test]
    fn layer_directive_parses_as_no_op() {
        let src = "layer domain\nlayer app uses domain, infra\nval x = 1\n";
        let d = dump(src);
        assert!(!d.contains("\"layer\""), "parsed as a call: {d}");
        assert_eq!(Parser::new(src).parse().unwrap().items.len(), 3);
    }

    #[test]
    fn directive_words_remain_usable_as_identifiers() {
        let src = "val layer = 3\nval n = layer + 1\nlayer(n)\nval internal_export = 2\nval m = internal_export and layer\ninternal_export(m)\n";
        assert_eq!(Parser::new(src).parse().unwrap().items.len(), 6);
    }
}
