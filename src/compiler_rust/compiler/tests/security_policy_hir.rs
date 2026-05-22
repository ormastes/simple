use simple_compiler::hir::{self, HirCapabilityItem, HirSandboxItem, HirSecurityItem};
use simple_compiler::security::{
    build_security_inventory, infer_security_coordinate, lower_security_to_aop, source_security_violations_sdn,
    security_metadata_id, source_security_violations_sdn_with_module, SecurityAdviceStep, SecuritySourceFile,
};
use simple_compiler::weaving::WeavingConfig;
use simple_parser::Parser;
use std::path::Path;

fn lower(source: &str) -> simple_compiler::hir::HirModule {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse source");
    hir::lower(&ast).expect("lower to HIR")
}

fn hir_function(name: &str, body: Vec<hir::HirStmt>) -> hir::HirFunction {
    hir_function_with_params(name, vec![], body)
}

fn hir_function_with_params(name: &str, params: Vec<hir::LocalVar>, body: Vec<hir::HirStmt>) -> hir::HirFunction {
    hir::HirFunction {
        name: name.to_string(),
        span: None,
        params,
        locals: vec![],
        return_type: hir::TypeId::I64,
        body,
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: false,
        inject: false,
        concurrency_mode: hir::ConcurrencyMode::Actor,
        module_path: String::new(),
        attributes: vec![],
        effects: vec![],
        layout_hint: None,
        verification_mode: hir::VerificationMode::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    }
}

fn capability_param(name: &str, type_name: &str) -> hir::LocalVar {
    hir::LocalVar {
        name: name.to_string(),
        ty: hir::TypeId::I64,
        type_name_hint: Some(type_name.to_string()),
        mutability: simple_parser::ast::Mutability::Immutable,
        inject: false,
        is_ghost: false,
    }
}

#[test]
fn lowers_security_policy_with_default_conventions() {
    let module = lower(
        r#"security AppSecurity:
    root src/security
    default deny
    allow feature user -> feature admin through UserAdminGate
"#,
    );
    let policy = &module.security_policies[0];
    assert_eq!(policy.name, "AppSecurity");
    assert!(policy.conventions_enabled);
    assert!(matches!(&policy.items[0], HirSecurityItem::Root { path } if path == "src/security"));
    assert!(matches!(
        &policy.items[2],
        HirSecurityItem::Allow { from, to, through: Some(gate) }
            if from == "feature user" && to == "feature admin" && gate == "UserAdminGate"
    ));
}

#[test]
fn lowers_gate_sandbox_and_inventory() {
    let module = lower(
        r#"security gate UserAdminGate:
    from feature user
    to feature admin
    policy CanRequestAdminAction
    audit all
    sandbox admin_sandbox
    grant:
        ReadDir["/reports"]
        AuditLog

sandbox admin_sandbox:
    backend auto
    net deny all
"#,
    );

    let gate = &module.security_gates[0];
    assert_eq!(gate.from.as_deref(), Some("feature user"));
    assert_eq!(gate.to.as_deref(), Some("feature admin"));
    assert_eq!(gate.policy.as_deref(), Some("CanRequestAdminAction"));
    assert_eq!(module.aop_advices.len(), 1);
    assert_eq!(module.aop_advices[0].form, "around");
    assert_eq!(
        module.aop_advices[0].advice_function,
        "__simple_security_gate_UserAdminGate"
    );
    assert_eq!(
        module.aop_advices[0].predicate_text,
        "pc{ execution(* UserAdminGate.*(..)) }"
    );
    let generated = lower_security_to_aop(&module);
    let gate_id = security_metadata_id("UserAdminGate");
    let policy_id = security_metadata_id("CanRequestAdminAction");
    let sandbox_id = security_metadata_id("admin_sandbox");
    let audit_id = security_metadata_id("all");
    assert_eq!(generated.advice_plans.len(), 1);
    assert_eq!(generated.advice_plans[0].gate_id, gate_id);
    assert_eq!(
        generated.advice_plans[0].steps,
        vec![
            SecurityAdviceStep::EnterGate {
                gate: "UserAdminGate".to_string(),
                gate_id,
            },
            SecurityAdviceStep::RequirePolicy {
                policy: "CanRequestAdminAction".to_string(),
                policy_id,
            },
            SecurityAdviceStep::EnterSandbox {
                sandbox: "admin_sandbox".to_string(),
                sandbox_id,
            },
            SecurityAdviceStep::AuditStart {
                gate: "UserAdminGate".to_string(),
                gate_id,
                audit: "all".to_string(),
                audit_id,
            },
            SecurityAdviceStep::Proceed,
            SecurityAdviceStep::AuditSuccess {
                gate: "UserAdminGate".to_string(),
                gate_id,
            },
            SecurityAdviceStep::AuditFailure {
                gate: "UserAdminGate".to_string(),
                gate_id,
            },
            SecurityAdviceStep::ExitSandbox { sandbox_id },
            SecurityAdviceStep::ExitGate { gate_id },
        ]
    );
    assert!(matches!(&module.sandbox_policies[0].items[0], HirSandboxItem::Backend { name } if name == "auto"));

    let inventory = build_security_inventory(&module);
    assert!(inventory.gate_inventory_md.contains("UserAdminGate"));
    assert!(inventory
        .security_aspects_spl
        .contains("aspect GeneratedUserAdminGateAdvice"));
    assert!(inventory.security_aspects_spl.contains("PolicyRuntime.require"));
    assert!(inventory.security_aspects_spl.contains("SandboxRuntime.enter"));
    assert!(inventory
        .security_aop_sdn
        .contains("__simple_security_gate_UserAdminGate"));
    assert!(inventory
        .security_aop_sdn
        .contains("pc{ execution(* UserAdminGate.*(..)) }"));
    assert!(inventory
        .security_aop_sdn
        .contains("require_policy: CanRequestAdminAction"));
    assert!(inventory.security_aop_sdn.contains("enter_sandbox: admin_sandbox"));
    assert!(inventory.security_aop_sdn.contains("audit_success: UserAdminGate"));
    assert!(inventory.security_aop_sdn.contains(&format!("gate_id: {}", gate_id)));
    assert!(inventory.sandbox_manifest_sdn.contains("- ReadDir[\"/reports\"]"));
    assert!(inventory.violations_sdn.contains("[]"));

    let weaving_config = WeavingConfig::from_hir_module(&module);
    assert!(weaving_config.enabled);
    assert_eq!(weaving_config.security_advice_plans.len(), 1);
}

#[test]
fn renders_security_boundary_aspect_from_policy_rules() {
    let module = lower(
        r#"security AppSecurity:
    allow feature user -> feature admin through UserAdminGate
    deny feature plugin -> feature infra except PluginInfraGate
"#,
    );

    let inventory = build_security_inventory(&module);
    assert!(inventory
        .security_aspects_spl
        .contains("aspect GeneratedSecurityBoundary"));
    assert!(inventory
        .security_aspects_spl
        .contains("through security_gate(UserAdminGate)"));
    assert!(inventory
        .security_aspects_spl
        .contains("unless security_gate(PluginInfraGate)"));
}

#[test]
fn lowers_security_boundary_rules_to_hir_arch_rules() {
    let module = lower(
        r#"security AppSecurity:
    deny feature user -> feature admin except UserAdminGate
    allow feature admin -> feature audit
"#,
    );

    let generated = lower_security_to_aop(&module);
    assert_eq!(generated.arch_rules.len(), 2);
    assert!(generated.arch_rules.iter().any(|rule| {
        rule.rule_type == "forbid"
            && rule.predicate_text == "pc{ depend(feature.user.**, feature.admin.**) }"
            && rule.message.as_deref() == Some("Security boundary requires gate UserAdminGate")
    }));
    assert!(generated.arch_rules.iter().any(|rule| {
        rule.rule_type == "allow" && rule.predicate_text == "pc{ depend(feature.admin.**, feature.audit.**) }"
    }));
    let inventory = build_security_inventory(&module);
    assert!(inventory.security_aop_sdn.contains("type: forbid"));
    assert!(inventory
        .security_aop_sdn
        .contains("pc{ depend(feature.user.**, feature.admin.**) }"));
    assert!(module
        .arch_rules
        .iter()
        .any(|rule| rule.predicate_text == "pc{ depend(feature.user.**, feature.admin.**) }"));
}

#[test]
fn infers_security_coordinates_from_feature_folders() {
    let coordinate = infer_security_coordinate(Path::new("src/feature/user/service/profile.spl"));
    assert_eq!(coordinate.feature.as_deref(), Some("user"));
    assert_eq!(coordinate.layer.as_deref(), Some("service"));
    assert_eq!(coordinate.trust.as_deref(), Some("app"));
    assert_eq!(coordinate.runtime.as_deref(), None);
    assert!(!coordinate.security_root);

    let security = infer_security_coordinate(Path::new("src/security/gate/user_admin_gate.spl"));
    assert_eq!(security.feature.as_deref(), Some("security"));
    assert_eq!(security.layer.as_deref(), Some("security_gate"));
    assert_eq!(security.trust.as_deref(), Some("app"));
    assert!(security.security_root);

    let plugin = infer_security_coordinate(Path::new("src/feature/plugin/sandbox/report.spl"));
    assert_eq!(plugin.feature.as_deref(), Some("plugin"));
    assert_eq!(plugin.layer.as_deref(), Some("sandbox"));
    assert_eq!(plugin.trust.as_deref(), Some("plugin"));
    assert_eq!(plugin.runtime.as_deref(), Some("sandboxed"));
}

#[test]
fn reports_sec201_for_direct_feature_boundary_import() {
    let files = vec![
        SecuritySourceFile {
            path: "src/feature/user/service/profile.spl".to_string(),
            source: "use feature.admin.infra.admin_user_repo\nclass Profile:\n    fn run():\n        AdminUserRepo.delete(1)\n".to_string(),
        },
        SecuritySourceFile {
            path: "src/feature/admin/infra/admin_user_repo.spl".to_string(),
            source: "class AdminUserRepo:\n    fn delete(id: Int):\n        return\n".to_string(),
        },
    ];

    let violations = source_security_violations_sdn(&files);
    assert!(violations.contains("code: SEC201"));
    assert!(violations.contains("from_feature: user"));
    assert!(violations.contains("to_feature: admin"));
}

#[test]
fn sec201_uses_declared_gate_as_required_crossing() {
    let module = lower(
        r#"security AppSecurity:
    deny feature user -> feature admin except UserAdminGate
"#,
    );
    let files = vec![
        SecuritySourceFile {
            path: "src/feature/user/service/profile.spl".to_string(),
            source: "class Profile:\n    fn run():\n        AdminUserRepo.delete(1)\n".to_string(),
        },
        SecuritySourceFile {
            path: "src/feature/admin/infra/admin_user_repo.spl".to_string(),
            source: "class AdminUserRepo:\n    fn delete(id: Int):\n        return\n".to_string(),
        },
    ];

    let violations = source_security_violations_sdn_with_module(&files, &module);
    assert!(violations.contains("code: SEC201"));
    assert!(violations.contains("edge: call"));
    assert!(violations.contains("required: route through UserAdminGate"));
}

#[test]
fn sec201_allows_cross_feature_port_imports_but_not_direct_calls() {
    let files = vec![
        SecuritySourceFile {
            path: "src/feature/user/service/profile.spl".to_string(),
            source: "use feature.admin.port.admin_user_port\nclass Profile:\n    fn run():\n        AdminUserRepo.delete(1)\n"
                .to_string(),
        },
        SecuritySourceFile {
            path: "src/feature/admin/infra/admin_user_repo.spl".to_string(),
            source: "class AdminUserRepo:\n    fn delete(id: Int):\n        return\n".to_string(),
        },
    ];

    let violations = source_security_violations_sdn(&files);
    assert!(violations.contains("code: SEC201"));
    assert!(violations.contains("edge: call"));
    assert!(!violations.contains("edge: import"));
}

#[test]
fn sec201_uses_hir_resolved_imports_when_modules_are_available() {
    let files = vec![
        SecuritySourceFile {
            path: "src/feature/user/service/profile.spl".to_string(),
            source: "class Profile:\n    pass\n".to_string(),
        },
        SecuritySourceFile {
            path: "src/feature/admin/infra/admin_user_repo.spl".to_string(),
            source: "class AdminUserRepo:\n    pass\n".to_string(),
        },
    ];
    let mut user_module = hir::HirModule::new();
    user_module.imports.push(hir::HirImport {
        from_path: vec![
            "crate".to_string(),
            "feature".to_string(),
            "admin".to_string(),
            "infra".to_string(),
            "admin_user_repo".to_string(),
        ],
        items: vec![],
        is_glob: true,
        is_type_only: false,
        is_lazy: false,
    });
    let admin_module = hir::HirModule::new();

    let violations =
        simple_compiler::security::source_security_violations_sdn_with_modules(&files, &[user_module, admin_module]);
    assert!(violations.contains("code: SEC201"));
    assert!(violations.contains("edge: import"));
    assert!(violations.contains("to_layer: infra"));
}

#[test]
fn sec201_uses_hir_resolved_global_calls_when_modules_are_available() {
    let files = vec![
        SecuritySourceFile {
            path: "src/feature/user/service/profile.spl".to_string(),
            source: "class Profile:\n    pass\n".to_string(),
        },
        SecuritySourceFile {
            path: "src/feature/admin/domain/delete.spl".to_string(),
            source: "fn admin_delete():\n    return\n".to_string(),
        },
    ];
    let mut user_module = hir::HirModule::new();
    user_module.functions.push(hir_function(
        "run",
        vec![hir::HirStmt::Expr(hir::HirExpr {
            kind: hir::HirExprKind::Call {
                func: Box::new(hir::HirExpr {
                    kind: hir::HirExprKind::Global("admin_delete".to_string()),
                    ty: hir::TypeId::I64,
                }),
                args: vec![],
            },
            ty: hir::TypeId::I64,
        })],
    ));
    let mut admin_module = hir::HirModule::new();
    admin_module.functions.push(hir_function("admin_delete", vec![]));

    let violations =
        simple_compiler::security::source_security_violations_sdn_with_modules(&files, &[user_module, admin_module]);
    assert!(violations.contains("code: SEC201"));
    assert!(violations.contains("edge: call"));
    assert!(violations.contains("to_feature: admin"));
}

#[test]
fn sec201_prefers_resolved_hir_graph_when_full_workspace_is_available() {
    let files = vec![
        SecuritySourceFile {
            path: "src/feature/user/service/profile.spl".to_string(),
            source: "class Profile:\n    fn run():\n        AdminUserRepo.delete(1)\n".to_string(),
        },
        SecuritySourceFile {
            path: "src/feature/admin/domain/delete.spl".to_string(),
            source: "fn admin_delete():\n    return\n".to_string(),
        },
    ];
    let mut user_module = hir::HirModule::new();
    user_module.functions.push(hir_function("run", vec![]));
    let mut admin_module = hir::HirModule::new();
    admin_module.functions.push(hir_function("admin_delete", vec![]));

    let violations =
        simple_compiler::security::source_security_violations_sdn_with_modules(&files, &[user_module, admin_module]);
    assert!(!violations.contains("code: SEC201"));
}

#[test]
fn sec201_does_not_treat_type_declarations_as_call_edges() {
    let files = vec![
        SecuritySourceFile {
            path: "src/feature/admin/infra/admin_user_repo.spl".to_string(),
            source: "class AdminUserRepo:\n    fn delete():\n        return\n".to_string(),
        },
        SecuritySourceFile {
            path: "src/feature/user/domain/user.spl".to_string(),
            source: "class User:\n    pass\n".to_string(),
        },
    ];

    let violations = source_security_violations_sdn(&files);
    assert!(!violations.contains("code: SEC201"));
}

#[test]
fn reports_sec301_for_scattered_authorization_outside_security_root() {
    let files = vec![SecuritySourceFile {
        path: "src/feature/user/service/profile.spl".to_string(),
        source: "class Profile:\n    fn delete():\n        if current_user().is_admin:\n            return\n"
            .to_string(),
    }];

    let violations = source_security_violations_sdn(&files);
    assert!(violations.contains("code: SEC301"));
    assert!(violations.contains("authorization predicate"));
}

#[test]
fn sec301_uses_hir_resolved_authorization_calls_when_modules_are_available() {
    let files = vec![SecuritySourceFile {
        path: "src/feature/user/service/profile.spl".to_string(),
        source: "class Profile:\n    pass\n".to_string(),
    }];
    let mut module = hir::HirModule::new();
    module.functions.push(hir_function(
        "run",
        vec![hir::HirStmt::Expr(hir::HirExpr {
            kind: hir::HirExprKind::MethodCall {
                receiver: Box::new(hir::HirExpr {
                    kind: hir::HirExprKind::Global("current_user".to_string()),
                    ty: hir::TypeId::I64,
                }),
                method: "is_admin".to_string(),
                args: vec![],
                dispatch: hir::DispatchMode::Static,
            },
            ty: hir::TypeId::BOOL,
        })],
    ));

    let violations = simple_compiler::security::source_security_violations_sdn_with_modules(&files, &[module]);
    assert!(violations.contains("code: SEC301"));
    assert!(violations.contains("message: resolved authorization predicate"));
    assert!(violations.contains("predicate: is_admin"));
    assert!(violations.contains("edge: resolved_call"));
}

#[test]
fn sec301_prefers_resolved_hir_when_full_workspace_is_available() {
    let files = vec![SecuritySourceFile {
        path: "src/feature/user/service/profile.spl".to_string(),
        source: "class Profile:\n    fn show():\n        return current_user().is_admin\n".to_string(),
    }];
    let mut module = hir::HirModule::new();
    module.functions.push(hir_function("show", vec![]));

    let violations = simple_compiler::security::source_security_violations_sdn_with_modules(&files, &[module]);
    assert!(!violations.contains("code: SEC301"));
}

#[test]
fn allows_security_observation_for_ui_only_hints() {
    let files = vec![SecuritySourceFile {
        path: "src/feature/user/service/profile.spl".to_string(),
        source: "@security_observation\nfn can_show_admin_button():\n    return current_user().is_admin\n".to_string(),
    }];

    let violations = source_security_violations_sdn(&files);
    assert!(!violations.contains("code: SEC301"));
}

#[test]
fn sec401_uses_hir_resolved_ambient_authority_calls_when_modules_are_available() {
    let files = vec![SecuritySourceFile {
        path: "src/feature/plugin/sandbox/report.spl".to_string(),
        source: "class ReportPlugin:\n    pass\n".to_string(),
    }];
    let mut module = hir::HirModule::new();
    module.functions.push(hir_function(
        "run",
        vec![hir::HirStmt::Expr(hir::HirExpr {
            kind: hir::HirExprKind::MethodCall {
                receiver: Box::new(hir::HirExpr {
                    kind: hir::HirExprKind::Global("File".to_string()),
                    ty: hir::TypeId::I64,
                }),
                method: "open".to_string(),
                args: vec![],
                dispatch: hir::DispatchMode::Static,
            },
            ty: hir::TypeId::I64,
        })],
    ));

    let violations = simple_compiler::security::source_security_violations_sdn_with_modules(&files, &[module]);
    assert!(violations.contains("code: SEC401"));
    assert!(violations.contains("message: resolved raw ambient authority API"));
    assert!(violations.contains("api: File.open"));
    assert!(violations.contains("edge: resolved_call"));
    assert!(violations.contains("trust: plugin"));
    assert!(violations.contains("runtime: sandboxed"));
    assert!(violations.contains("required: inject narrowed capability handle ReadFile or WriteFile"));
    assert!(violations.contains("replacement: ReadFile.read_text or WriteFile.write_text"));
}

#[test]
fn sec401_prefers_resolved_hir_when_full_workspace_is_available() {
    let files = vec![SecuritySourceFile {
        path: "src/feature/plugin/sandbox/report.spl".to_string(),
        source: "class ReportPlugin:\n    fn run():\n        File.open(\"/etc/passwd\")\n".to_string(),
    }];
    let mut module = hir::HirModule::new();
    module.functions.push(hir_function("run", vec![]));

    let violations = simple_compiler::security::source_security_violations_sdn_with_modules(&files, &[module]);
    assert!(!violations.contains("code: SEC401"));
}

#[test]
fn sec401_accepts_hir_resolved_explicit_capability_handles() {
    let files = vec![SecuritySourceFile {
        path: "src/feature/plugin/sandbox/report.spl".to_string(),
        source: "class ReportPlugin:\n    pass\n".to_string(),
    }];
    let mut module = hir::HirModule::new();
    module.functions.push(hir_function_with_params(
        "run",
        vec![capability_param("file", "ReadFile"), capability_param("env", "EnvVar")],
        vec![
            hir::HirStmt::Expr(hir::HirExpr {
                kind: hir::HirExprKind::MethodCall {
                    receiver: Box::new(hir::HirExpr {
                        kind: hir::HirExprKind::Global("File".to_string()),
                        ty: hir::TypeId::I64,
                    }),
                    method: "open".to_string(),
                    args: vec![],
                    dispatch: hir::DispatchMode::Static,
                },
                ty: hir::TypeId::I64,
            }),
            hir::HirStmt::Expr(hir::HirExpr {
                kind: hir::HirExprKind::MethodCall {
                    receiver: Box::new(hir::HirExpr {
                        kind: hir::HirExprKind::Global("Env".to_string()),
                        ty: hir::TypeId::I64,
                    }),
                    method: "get".to_string(),
                    args: vec![],
                    dispatch: hir::DispatchMode::Static,
                },
                ty: hir::TypeId::I64,
            }),
        ],
    ));

    let violations = simple_compiler::security::source_security_violations_sdn_with_modules(&files, &[module]);
    assert!(!violations.contains("code: SEC401"));
}

#[test]
fn reports_sec401_for_raw_ambient_authority_apis() {
    let files = vec![SecuritySourceFile {
        path: "src/feature/plugin/service/report.spl".to_string(),
        source: "class ReportPlugin:\n    fn run():\n        File.open(\"/etc/passwd\")\n        Env.get(\"SECRET\")\n"
            .to_string(),
    }];

    let violations = source_security_violations_sdn(&files);
    assert!(violations.contains("code: SEC401"));
    assert!(violations.contains("File.open"));
    assert!(violations.contains("ReadFile or WriteFile"));
    assert!(violations.contains("ReadFile.read_text or WriteFile.write_text"));
    assert!(violations.contains("EnvVar"));
    assert!(violations.contains("EnvVar.get"));
}

#[test]
fn lowers_capability_policy_and_renders_manifest() {
    let module = lower(
        r#"capability ReadReports:
    resource Dir
    actions [read]
    scope path starts_with "/reports"

security gate PluginGate:
    from trust app
    to trust plugin
    grant:
        ReadReports
"#,
    );

    assert_eq!(module.capability_policies.len(), 1);
    assert_eq!(module.capability_policies[0].name, "ReadReports");
    assert!(matches!(
        &module.capability_policies[0].items[0],
        HirCapabilityItem::Rule { key, value } if key == "resource" && value == "Dir"
    ));

    let inventory = build_security_inventory(&module);
    assert!(inventory.capability_manifest_sdn.contains("ReadReports"));
    assert!(inventory.capability_manifest_sdn.contains("resource: Dir"));
    assert!(inventory.violations_sdn.contains("[]"));
}

#[test]
fn reports_unknown_gate_capability_grant() {
    let module = lower(
        r#"security gate PluginGate:
    from trust app
    to trust plugin
    grant:
        RootShell
"#,
    );

    let inventory = build_security_inventory(&module);
    assert!(inventory.violations_sdn.contains("SEC_CAPABILITY_UNKNOWN"));
    assert!(inventory.violations_sdn.contains("RootShell"));
}
