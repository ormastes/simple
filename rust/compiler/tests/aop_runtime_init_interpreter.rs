use simple_compiler::aop_config::parse_aop_config;
use simple_compiler::di::parse_di_config;
use simple_compiler::interpreter::evaluate_module_with_di_and_aop;
use simple_parser::Parser;

/// AOP runtime aspect interception test
/// This tests whether AOP aspects can intercept constructor calls at runtime
/// and replace the object being initialized.
///
/// Test flow:
/// 1. Service() constructor triggers DI resolution for repo: Repo
/// 2. AOP around advice intercepts Repo init via pc{ init(Repo) }
/// 3. The proceed() callback creates the original Repo
/// 4. The advice returns a WrappedRepo instead
/// 5. Service.get_value() returns 1 (from WrappedRepo) instead of 0 (from Repo)
#[test]
fn interpreter_applies_runtime_around_init() {
    let source = r#"
fn repo_around(proceed):
    let _repo = proceed()
    return WrappedRepo()

class Repo:
    fn value(self) -> i64:
        return 0

class WrappedRepo:
    fn value(self) -> i64:
        return 1

class Service:
    repo: Repo

    #[inject]
    fn new(self, repo: Repo):
        self.repo = repo

    fn get_value(self) -> i64:
        return self.repo.value()

val service = Service()
main = service.get_value()
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
        evaluate_module_with_di_and_aop(&module.items, Some(&di_config), Some(&aop_config)).expect("eval module");
    assert_eq!(result, 1);
}
