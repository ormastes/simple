use simple_compiler::di::parse_di_config;
use simple_compiler::interpreter::evaluate_module_with_di;
use simple_parser::Parser;

#[test]
fn interpreter_injects_constructor_params() {
    let source = r#"
class Repo:
    fn new(self):
        return self

class Service:
    #[inject]
    fn new(self, repo: Repo) -> i64:
        return 123

main = Service()
"#;

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse module");

    let di_toml: toml::Value = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
  { on = "pc{ type(Repo) }", impl = "Repo", scope = "Singleton", priority = 10 }
]
"#
    .parse()
    .expect("parse di toml");
    let di_config = parse_di_config(&di_toml).expect("di config").expect("di config present");

    let result = evaluate_module_with_di(&module.items, Some(&di_config))
        .expect("eval module");
    assert_eq!(result, 123);
}
