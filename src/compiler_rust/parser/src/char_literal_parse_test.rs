#[cfg(test)]
mod char_literal_parse {
    use crate::Parser;

    fn items(src: &str, on: bool) -> String {
        let module = Parser::new_with_char_literals(src, on)
            .parse()
            .unwrap_or_else(|e| panic!("parse failed (char mode {on}): {e:?}\n{src}"));
        format!("{:?}", module.items)
    }

    #[test]
    fn char_literal_is_string_expr_when_gate_on() {
        let on = items("val c: char = 'x'\n", true);
        assert!(on.contains("String(\"x\")"), "{on}");
        // Same AST node the legacy raw-string form produced.
        assert_eq!(on, items("val c: char = 'x'\n", false));
    }

    #[test]
    fn char_literal_escape_when_gate_on() {
        let on = items("val c = '\\n'\n", true);
        assert!(on.contains("String(\"\\n\")"), "{on}");
    }

    #[test]
    fn char_literal_in_match_pattern_and_comparison() {
        let src = "fn f(c: char) -> i64:\n    match c:\n        case 'a': 1\n        case '\\t': 2\n        case 'b'..='z': 3\n        case _: 0\n\nfn g(s: text) -> bool:\n    s[0] == 'q' or 'q' == s[0]\n";
        let on = items(src, true);
        assert!(on.contains("Literal(String(\"a\"))"), "{on}");
        assert!(on.contains("Literal(String(\"\\t\"))"), "{on}");
        assert!(on.contains("Range"), "{on}");
        assert!(on.contains("String(\"q\")"), "{on}");
    }

    #[test]
    fn char_literal_as_no_paren_call_argument() {
        let on = items("fn main():\n    print 'z'\n", true);
        assert!(on.contains("String(\"z\")"), "{on}");
    }
}
