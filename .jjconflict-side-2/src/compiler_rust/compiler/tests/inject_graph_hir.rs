use simple_compiler::{
    di::{
        self, di_config_from_hir_inject_graphs, merge_di_config_with_hir_graphs, parse_di_config, parse_di_sdn_config,
    },
    hir::{self, HirInjectItem},
    mir,
};
use simple_parser::Parser;

fn lower(source: &str) -> simple_compiler::hir::HirModule {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse source");
    hir::lower(&ast).expect("lower to HIR")
}

#[test]
fn lowers_source_inject_graph_to_hir() {
    let source = r#"inject AppGraph mixed:
    root App
    scan app.*
    load "config/di.sdn"
    bind UserRepo = SqlUserRepo lifetime scoped configurable
    bind CryptoRng = SystemCryptoRng lifetime singleton final
    slot PaymentProvider runtime named payments default StripePaymentProvider
    profile test:
        bind UserRepo = MemoryUserRepo
"#;

    let module = lower(source);
    assert_eq!(module.inject_graphs.len(), 1);

    let graph = &module.inject_graphs[0];
    assert_eq!(graph.name, "AppGraph");
    assert_eq!(graph.mode.as_deref(), Some("mixed"));
    assert_eq!(graph.items.len(), 7);

    assert!(matches!(&graph.items[0], HirInjectItem::Root { type_ref } if type_ref == "App"));
    assert!(matches!(&graph.items[1], HirInjectItem::Scan { pattern } if pattern == "app.*"));
    assert!(matches!(&graph.items[2], HirInjectItem::Load { path } if path == "config/di.sdn"));
    assert!(matches!(
        &graph.items[3],
        HirInjectItem::Bind {
            service,
            target,
            lifetime: Some(lifetime),
            configurable: true,
            final_binding: false,
        } if service == "UserRepo" && target == "SqlUserRepo" && lifetime == "scoped"
    ));
    assert!(matches!(
        &graph.items[4],
        HirInjectItem::Bind {
            service,
            target,
            lifetime: Some(lifetime),
            configurable: false,
            final_binding: true,
        } if service == "CryptoRng" && target == "SystemCryptoRng" && lifetime == "singleton"
    ));
    assert!(matches!(
        &graph.items[5],
        HirInjectItem::Slot {
            service,
            qualifier: Some(qualifier),
            default_target: Some(default_target),
        } if service == "PaymentProvider" && qualifier == "payments" && default_target == "StripePaymentProvider"
    ));
    assert!(matches!(&graph.items[6], HirInjectItem::Profile { name, items } if name == "test" && items.len() == 1));
}

#[test]
fn rejects_inject_graph_load_outside_current_tree() {
    let mut parser = Parser::new("inject AppGraph runtime:\n    load \"../di.sdn\"\n");
    let ast = parser.parse().expect("parse source");
    let err = hir::lower(&ast).expect_err("lowering must reject parent path load");
    assert!(err.to_string().contains("cannot escape the current directory"));
}

#[test]
fn source_inject_graph_builds_di_config_rules() {
    let module = lower(
        r#"inject AppGraph compile:
    bind UserRepo = SqlUserRepo lifetime scoped configurable
    bind CryptoRng = SystemCryptoRng lifetime singleton final
"#,
    );

    let config = di_config_from_hir_inject_graphs(&module.inject_graphs)
        .expect("build DI config")
        .expect("source graph config");
    let ctx = di::create_di_match_context("UserRepo", "", &[]);
    let binding = config
        .select_binding("default", &ctx)
        .expect("select binding")
        .expect("binding present");

    assert_eq!(binding.impl_type, "SqlUserRepo.new");
    assert_eq!(binding.scope, di::DiScope::Scoped);
    assert!(binding.configurable);
    assert!(!binding.final_binding);
    assert_eq!(binding.default_instance_class.as_deref(), Some("SqlUserRepo"));

    let rng_ctx = di::create_di_match_context("CryptoRng", "", &[]);
    let rng = config
        .select_binding("default", &rng_ctx)
        .expect("select rng")
        .expect("rng binding present");
    assert_eq!(rng.impl_type, "SystemCryptoRng.new");
    assert_eq!(rng.scope, di::DiScope::Singleton);
    assert!(rng.final_binding);
}

#[test]
fn source_inject_graph_always_creates_default_profile() {
    let module = lower(
        r#"inject AppGraph compile:
    root App
"#,
    );

    let config = di_config_from_hir_inject_graphs(&module.inject_graphs)
        .expect("build DI config")
        .expect("source graph config");
    let ctx = di::create_di_match_context("Missing", "", &[]);

    assert!(config.profiles.contains_key("default"));
    assert_eq!(config.roots, vec!["App".to_string()]);
    assert!(config.select_binding("default", &ctx).expect("select").is_none());
}

#[test]
fn source_inject_graph_enables_di_conventions_by_default() {
    let module = lower(
        r#"inject AppGraph compile:
    root App
"#,
    );

    let config = di_config_from_hir_inject_graphs(&module.inject_graphs)
        .expect("build DI config")
        .expect("source graph config");

    assert_eq!(config.conventions, di::DiConventionConfig::default());
    assert!(config.conventions.self_binding);
    assert!(config.conventions.single_visible_impl);
    assert!(config.conventions.naming_fallback);
    assert!(config.conventions.folder_fallback);
    assert!(config.conventions.std_defaults);
}

#[test]
fn parsed_di_config_enables_conventions_by_default() {
    let config = parse_di_toml(
        r#"
[di]
"#,
    );

    assert_eq!(config.conventions, di::DiConventionConfig::default());
    assert!(config.conventions.self_binding);
    assert!(config.conventions.single_visible_impl);
    assert!(config.conventions.naming_fallback);
    assert!(config.conventions.folder_fallback);
    assert!(config.conventions.std_defaults);
}

#[test]
fn parsed_di_config_allows_individual_convention_toggles() {
    let config = parse_di_toml(
        r#"
[di]

[di.conventions]
self_binding = false
single_visible_impl = false
naming_fallback = false
folder_fallback = false
std_defaults = false
"#,
    );

    assert!(!config.conventions.self_binding);
    assert!(!config.conventions.single_visible_impl);
    assert!(!config.conventions.naming_fallback);
    assert!(!config.conventions.folder_fallback);
    assert!(!config.conventions.std_defaults);
}

#[test]
fn source_inject_graph_satisfies_mir_constructor_injection() {
    let source = r#"
class Database:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(db: Database) -> Self:
        return Self {}

inject AppGraph compile:
    root UserService
    bind Database = Database lifetime singleton

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let mir_module = mir::lower_to_mir(&hir_module).expect("source inject graph should provide DI config");
    assert!(mir_module.functions.iter().any(|f| f.name == "main"));
}

#[test]
fn convention_di_self_binds_concrete_constructor_without_config() {
    let source = r#"
class Database:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(db: Database) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let mir_module = mir::lower_to_mir(&hir_module).expect("concrete class should self-bind by convention");
    assert_main_calls(&mir_module, "Database.new");
}

#[test]
fn convention_di_policy_can_disable_self_binding() {
    let source = r#"
class Database:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(db: Database) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;
    let hir_module = lower(source);
    let config = parse_di_toml(
        r#"
[di]
conventions = { self_binding = false, single_visible_impl = false, naming_fallback = false, std_defaults = false }
"#,
    );

    let err = mir::lower_to_mir_with_mode_and_di(&hir_module, mir::ContractMode::All, Some(config))
        .expect_err("disabled conventions should require explicit binding");
    assert!(err.to_string().contains("Database"));
}

#[test]
fn convention_di_uses_single_visible_implementation_without_bind() {
    let source = r#"
trait Clock:
    fn now() -> i64

class SystemClock:
    fn new() -> Self:
        return Self {}

impl Clock for SystemClock:
    fn now() -> i64:
        return 1

class UserService:
    @inject
    fn new(clock: Clock) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let mir_module = mir::lower_to_mir(&hir_module).expect("single impl should bind by convention");
    assert_main_calls(&mir_module, "SystemClock.new");
}

#[test]
fn convention_di_uses_std_default_provider_without_impl() {
    let source = r#"
trait Clock:
    fn now() -> i64

class SystemClock:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(clock: Clock) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let mir_module = mir::lower_to_mir(&hir_module).expect("std default should bind Clock to SystemClock");
    assert_main_calls(&mir_module, "SystemClock.new");
}

#[test]
fn convention_di_uses_logger_std_default_when_naming_is_disabled() {
    let source = r#"
trait Logger:
    fn info(msg: str)

class ConsoleLogger:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(logger: Logger) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let config = parse_di_toml(
        r#"
[di]
conventions = { self_binding = false, single_visible_impl = false, naming_fallback = false, folder_fallback = false, std_defaults = true }
"#,
    );

    let mir_module = mir::lower_to_mir_with_mode_and_di(&hir_module, mir::ContractMode::All, Some(config))
        .expect("std default should bind Logger to ConsoleLogger");
    assert_main_calls(&mir_module, "ConsoleLogger.new");
}

#[test]
fn convention_di_folder_policy_uses_repo_scan_when_naming_is_disabled() {
    let source = r#"
trait UserRepo:
    fn count() -> i64

class SqlUserRepo:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(repo: UserRepo) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let config = parse_di_toml(
        r#"
[di]
scan = ["infra.repo.*"]
conventions = { self_binding = false, single_visible_impl = false, naming_fallback = false, folder_fallback = true, std_defaults = false }
"#,
    );

    let mir_module = mir::lower_to_mir_with_mode_and_di(&hir_module, mir::ContractMode::All, Some(config))
        .expect("folder policy should bind scanned repo implementation");
    assert_main_calls(&mir_module, "SqlUserRepo.new");
}

#[test]
fn runtime_slot_default_target_satisfies_constructor_injection() {
    let source = r#"
trait PaymentProvider:
    fn pay() -> i64

class StripePaymentProvider:
    fn new() -> Self:
        return Self {}

class CheckoutService:
    @inject
    fn new(provider: PaymentProvider) -> Self:
        return Self {}

inject AppGraph mixed:
    slot PaymentProvider runtime default StripePaymentProvider

fn main():
    val service = CheckoutService()
    return 0
"#;

    let hir_module = lower(source);
    let mir_module = mir::lower_to_mir(&hir_module).expect("runtime slot default should provide static fallback");
    assert_main_calls(&mir_module, "StripePaymentProvider.new");
}

#[test]
fn convention_di_reports_ambiguous_visible_implementations() {
    let source = r#"
trait Clock:
    fn now() -> i64

class SystemClock:
    fn new() -> Self:
        return Self {}

class FakeClock:
    fn new() -> Self:
        return Self {}

impl Clock for SystemClock:
    fn now() -> i64:
        return 1

impl Clock for FakeClock:
    fn now() -> i64:
        return 2

class UserService:
    @inject
    fn new(clock: Clock) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let err = mir::lower_to_mir(&hir_module).expect_err("ambiguous impls should require explicit binding");
    let message = err.to_string();
    assert!(message.contains("ambiguous"));
    assert!(message.contains("Clock"));
    assert!(message.contains("SystemClock"));
    assert!(message.contains("FakeClock"));
}

#[test]
fn convention_di_can_disable_default_fallbacks() {
    let source = r#"
class Database:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(db: Database) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let di_config = parse_di_toml(
        r#"
[di]
conventions = false
"#,
    );
    let err = mir::lower_to_mir_with_mode_and_di(&hir_module, mir::ContractMode::All, Some(di_config))
        .expect_err("disabled conventions should require explicit binding");
    let message = err.to_string();
    assert!(message.contains("No binding found"));
    assert!(message.contains("Database"));
}

#[test]
fn convention_di_uses_std_default_when_enabled() {
    let source = r#"
trait Clock:
    fn now() -> i64

class SystemClock:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(clock: Clock) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let di_config = parse_di_toml(
        r#"
[di.conventions]
self_binding = false
single_visible_impl = false
folder_fallback = false
naming_fallback = false
std_defaults = true
"#,
    );
    let mir_module = mir::lower_to_mir_with_mode_and_di(&hir_module, mir::ContractMode::All, Some(di_config))
        .expect("std default should resolve Clock to SystemClock");
    assert_main_calls(&mir_module, "SystemClock.new");
}

#[test]
fn convention_di_uses_test_folder_fallback_when_enabled() {
    let source = r#"
trait UserRepo:
    fn find() -> i64

class FakeUserRepo:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(repo: UserRepo) -> Self:
        return Self {}

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let di_config = parse_di_toml(
        r#"
[di]
scan = ["test/fake/*"]

[di.conventions]
self_binding = false
single_visible_impl = false
folder_fallback = true
naming_fallback = false
std_defaults = false
"#,
    );
    let mir_module =
        mir::lower_to_mir_with_mode_di_profile(&hir_module, mir::ContractMode::All, Some(di_config), "test")
            .expect("test folder convention should resolve FakeUserRepo");
    assert_main_calls(&mir_module, "FakeUserRepo.new");
}

#[test]
fn explicit_binding_overrides_convention() {
    let source = r#"
trait Clock:
    fn now() -> i64

class SystemClock:
    fn new() -> Self:
        return Self {}

class FakeClock:
    fn new() -> Self:
        return Self {}

impl Clock for SystemClock:
    fn now() -> i64:
        return 1

impl Clock for FakeClock:
    fn now() -> i64:
        return 2

class UserService:
    @inject
    fn new(clock: Clock) -> Self:
        return Self {}

inject AppGraph compile:
    bind Clock = FakeClock

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let mir_module = mir::lower_to_mir(&hir_module).expect("explicit binding should override convention");
    assert_main_calls(&mir_module, "FakeClock.new");
    assert_main_does_not_call(&mir_module, "SystemClock.new");
}

#[test]
fn mir_lowerer_uses_selected_source_inject_profile() {
    let source = r#"
class Database:
    fn new() -> Self:
        return Self {}

class MemoryDatabase:
    fn new() -> Self:
        return Self {}

class UserService:
    @inject
    fn new(db: Database) -> Self:
        return Self {}

inject AppGraph compile:
    root UserService
    bind Database = Database
    profile test:
        bind Database = MemoryDatabase

fn main():
    val service = UserService()
    return 0
"#;

    let hir_module = lower(source);
    let mir_module = mir::lower_to_mir_with_mode_di_profile(&hir_module, mir::ContractMode::All, None, "test")
        .expect("source inject graph test profile should provide DI config");

    assert_main_calls(&mir_module, "MemoryDatabase.new");
}

#[test]
fn external_config_can_override_configurable_source_binding() {
    let module = lower(
        r#"inject AppGraph compile:
    bind UserRepo = SqlUserRepo configurable
"#,
    );
    let external = parse_di_toml(
        r#"
[di]

[di.profiles.default]
bindings = [
    { on = "type(UserRepo)", impl = "MemoryUserRepo.new", scope = "Singleton" }
]
"#,
    );

    let merged = merge_di_config_with_hir_graphs(Some(external), &module.inject_graphs)
        .expect("merge allowed")
        .expect("merged config");
    let ctx = di::create_di_match_context("UserRepo", "", &[]);
    let selected = merged
        .select_binding("default", &ctx)
        .expect("select")
        .expect("binding present");

    assert_eq!(selected.impl_type, "MemoryUserRepo.new");
    assert_eq!(selected.scope, di::DiScope::Singleton);
}

#[test]
fn external_config_cannot_override_final_source_binding() {
    let module = lower(
        r#"inject AppGraph compile:
    bind CryptoRng = SystemCryptoRng final
"#,
    );
    let external = parse_di_toml(
        r#"
[di]

[di.profiles.default]
bindings = [
    { on = "type(CryptoRng)", impl = "FakeCryptoRng.new" }
]
"#,
    );

    let err = merge_di_config_with_hir_graphs(Some(external), &module.inject_graphs).unwrap_err();
    assert!(err.contains("cannot override final/non-configurable binding"));
    assert!(err.contains("CryptoRng"));
}

#[test]
fn external_config_cannot_override_plain_source_binding() {
    let module = lower(
        r#"inject AppGraph compile:
    bind UserRepo = SqlUserRepo
"#,
    );
    let external = parse_di_toml(
        r#"
[di]

[di.profiles.default]
bindings = [
    { on = "type(UserRepo)", impl = "MemoryUserRepo.new" }
]
"#,
    );

    let err = merge_di_config_with_hir_graphs(Some(external), &module.inject_graphs).unwrap_err();
    assert!(err.contains("cannot override final/non-configurable binding"));
    assert!(err.contains("UserRepo"));
}

#[test]
fn sdn_di_config_parses_nested_bind_lifetime_profiles_and_slots() {
    let config = parse_di_sdn_config(
        r#"di:
    graph: AppGraph
    mode: mixed
    root: App
    scan = [app.*, infra.*]
    load: config/di.sdn
    bind:
        UserRepo: SqlUserRepo
        Logger: JsonLogger
    lifetime:
        Logger: singleton
    runtime_slot:
        PaymentProvider: StripePaymentProvider

profile:
    test:
        bind:
            UserRepo: MemoryUserRepo
            Clock:
                impl: FakeClock
                lifetime: scoped
                configurable: true
"#,
    )
    .expect("parse SDN DI config")
    .expect("DI config present");

    assert_eq!(config.graph.as_deref(), Some("AppGraph"));
    assert_eq!(config.mode, di::DiMode::Mixed);
    assert_eq!(config.roots, vec!["App".to_string()]);
    assert_eq!(config.scans, vec!["app.*".to_string(), "infra.*".to_string()]);
    assert_eq!(config.loads, vec!["config/di.sdn".to_string()]);
    assert!(config.profiles.contains_key("default"));
    assert_eq!(config.runtime_slots.len(), 1);
    assert_eq!(config.runtime_slots[0].type_name, "PaymentProvider");
    assert_eq!(
        config.runtime_slots[0].default_impl.as_deref(),
        Some("StripePaymentProvider")
    );

    let logger = config
        .select_binding("default", &di::create_di_match_context("Logger", "", &[]))
        .expect("select Logger")
        .expect("Logger binding");
    assert_eq!(logger.impl_type, "JsonLogger.new");
    assert_eq!(logger.scope, di::DiScope::Singleton);

    let test_repo = config
        .select_binding("test", &di::create_di_match_context("UserRepo", "", &[]))
        .expect("select UserRepo")
        .expect("test UserRepo binding");
    assert_eq!(test_repo.impl_type, "MemoryUserRepo.new");
}

#[test]
fn sdn_di_config_parses_table_bindings() {
    let config = parse_di_sdn_config(
        r#"di:
    graph: AppGraph

di_bind |type, impl, lifetime, profile, configurable|
    UserRepo, SqlUserRepo, scoped, default, true
    Clock, FakeClock, singleton, test, false
"#,
    )
    .expect("parse SDN DI table")
    .expect("DI config present");

    let repo = config
        .select_binding("default", &di::create_di_match_context("UserRepo", "", &[]))
        .expect("select UserRepo")
        .expect("default UserRepo binding");
    assert_eq!(repo.impl_type, "SqlUserRepo.new");
    assert_eq!(repo.scope, di::DiScope::Scoped);
    assert!(repo.configurable);

    let clock = config
        .select_binding("test", &di::create_di_match_context("Clock", "", &[]))
        .expect("select Clock")
        .expect("test Clock binding");
    assert_eq!(clock.impl_type, "FakeClock.new");
    assert_eq!(clock.scope, di::DiScope::Singleton);
}

#[test]
fn sdn_di_config_rejects_load_outside_current_tree() {
    let err = parse_di_sdn_config(
        r#"di:
    load: config/../di.sdn
"#,
    )
    .expect_err("SDN DI load path should be rejected");
    assert!(err.contains("cannot escape the current directory"));
}

#[test]
fn source_inject_graph_rejects_empty_load_path() {
    let mut parser = Parser::new("inject AppGraph runtime:\n    load \"\"\n");
    let ast = parser.parse().expect("parse source");
    let err = hir::lower(&ast).expect_err("lowering must reject empty load path");
    assert!(err.to_string().contains("cannot be empty"));
}

#[test]
fn source_inject_graph_rejects_normalized_parent_load_path() {
    let mut parser = Parser::new("inject AppGraph runtime:\n    load \"config/../x.sdn\"\n");
    let ast = parser.parse().expect("parse source");
    let err = hir::lower(&ast).expect_err("lowering must reject normalized parent path");
    assert!(err.to_string().contains("cannot escape the current directory"));
}

fn assert_main_calls(mir_module: &mir::MirModule, target_name: &str) {
    let main_func = mir_module
        .functions
        .iter()
        .find(|f| f.name == "main")
        .expect("main function");
    let has_call = main_func
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .any(|inst| matches!(inst, mir::MirInst::Call { target, .. } if target.name() == target_name));

    assert!(has_call, "expected main to call {}", target_name);
}

fn assert_main_does_not_call(mir_module: &mir::MirModule, target_name: &str) {
    let main_func = mir_module
        .functions
        .iter()
        .find(|f| f.name == "main")
        .expect("main function");
    let has_call = main_func
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .any(|inst| matches!(inst, mir::MirInst::Call { target, .. } if target.name() == target_name));

    assert!(!has_call, "expected main not to call {}", target_name);
}

fn parse_di_toml(toml_str: &str) -> di::DiConfig {
    let toml_value: toml::Value = toml::from_str(toml_str).expect("parse TOML");
    parse_di_config(&toml_value)
        .expect("parse DI config")
        .expect("DI config present")
}
