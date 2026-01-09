use simple_compiler::aop_config::parse_aop_config;
use simple_compiler::di::parse_di_config;
use simple_compiler::interpreter::evaluate_module_with_di_and_aop;
use simple_parser::Parser;

#[test]
fn interpreter_applies_runtime_around_init() {
    let source = r#"
fn repo_around(proceed):
    let _repo = proceed()
    return WrappedRepo()

class Repo:
    fn new(self):
        return self

    fn value(self) -> i64:
        return 0

class WrappedRepo:
    fn new(self):
        return self

    fn value(self) -> i64:
        return 1

class Service:
    #[inject]
    fn new(self, repo: Repo) -> i64:
        return repo.value()

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
    let di_config = parse_di_config(&di_toml)
        .expect("di config")
        .expect("di config present");

    let aop_toml: toml::Value = r#"
[aspects.runtime]
enabled = true
around = [
  { on = "pc{ init(Repo) }", use = "repo_around", priority = 10 }
]
"#
    .parse()
    .expect("parse aop toml");
    let aop_config = parse_aop_config(&aop_toml)
        .expect("aop config")
        .expect("aop config present");

    let result =
        evaluate_module_with_di_and_aop(&module.items, Some(&di_config), Some(&aop_config))
            .expect("eval module");
    assert_eq!(result, 1);
}
