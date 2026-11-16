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
