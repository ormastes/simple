use simple_parser::ast::*;
use simple_parser::Parser;

fn parse_items(source: &str) -> Vec<Node> {
    let mut parser = Parser::new(source);
    parser.parse().expect("parse security policy").items
}

#[test]
fn parses_security_policy_with_convention_defaults() {
    let items = parse_items(
        r#"security AppSecurity:
    root src/security
    default deny
    dimension layer:
        order ui -> api -> service -> domain -> port -> infra
    allow feature user -> feature admin through UserAdminGate
    deny feature user -> feature admin direct
"#,
    );

    let Node::SecurityPolicy(policy) = &items[0] else {
        panic!("expected security policy");
    };
    assert_eq!(policy.name, "AppSecurity");
    assert!(policy.conventions_enabled);
    assert!(matches!(&policy.items[0], SecurityItem::Root { path, .. } if path == "src/security"));
    assert!(matches!(&policy.items[1], SecurityItem::Default { action, .. } if action == "deny"));
    assert!(matches!(
        &policy.items[3],
        SecurityItem::Allow { from, to, through: Some(gate), .. }
            if from == "feature user" && to == "feature admin" && gate == "UserAdminGate"
    ));
}

#[test]
fn parses_minimal_security_policy_with_layer_and_isolate_sugar() {
    let items = parse_items(
        r#"security:
    layers ui -> api -> service -> domain -> port -> infra
    isolate user, admin, billing
"#,
    );

    let Node::SecurityPolicy(policy) = &items[0] else {
        panic!("expected security policy");
    };
    assert_eq!(policy.name, "default");
    assert!(policy.conventions_enabled);
    assert!(matches!(
        &policy.items[0],
        SecurityItem::Dimension { name, rules, .. }
            if name == "layer" && rules == &vec!["order ui->api->service->domain->port->infra".to_string()]
    ));
    assert!(matches!(
        &policy.items[1],
        SecurityItem::Dimension { name, rules, .. }
            if name == "feature" && rules == &vec!["isolate user,admin,billing".to_string()]
    ));
}

#[test]
fn parses_security_policy_configurable_and_final_markers() {
    let items = parse_items(
        r#"security AppSecurity:
    allow feature admin -> feature user through AdminUserGate configurable
    deny feature user -> feature admin final
"#,
    );

    let Node::SecurityPolicy(policy) = &items[0] else {
        panic!("expected security policy");
    };
    assert!(matches!(
        &policy.items[0],
        SecurityItem::Allow {
            configurable: true,
            final_rule: false,
            ..
        }
    ));
    assert!(matches!(
        &policy.items[1],
        SecurityItem::Deny {
            configurable: false,
            final_rule: true,
            ..
        }
    ));
}

#[test]
fn parses_security_gate_and_sandbox_policy() {
    let items = parse_items(
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

    let Node::SecurityGate(gate) = &items[0] else {
        panic!("expected security gate");
    };
    assert_eq!(gate.from.as_deref(), Some("feature user"));
    assert_eq!(gate.to.as_deref(), Some("feature admin"));
    assert_eq!(gate.grants, vec!["ReadDir[\"/reports\"]", "AuditLog"]);

    let Node::SandboxPolicy(sandbox) = &items[1] else {
        panic!("expected sandbox policy");
    };
    assert_eq!(sandbox.name, "admin_sandbox");
    assert!(matches!(&sandbox.items[0], SandboxItem::Backend { name, .. } if name == "auto"));
}

#[test]
fn parses_native_capability_policy() {
    let items = parse_items(
        r#"capability ReadReports:
    resource Dir
    actions [read]
    scope path starts_with "/reports"
"#,
    );

    let Node::CapabilityPolicy(capability) = &items[0] else {
        panic!("expected capability policy");
    };
    assert_eq!(capability.name, "ReadReports");
    assert_eq!(capability.items.len(), 3);
    assert!(
        matches!(&capability.items[0], CapabilityItem::Rule { key, value, .. } if key == "resource" && value == "Dir")
    );
}

#[test]
fn parses_ui_policy_snapshot_rules() {
    let items = parse_items(
        r#"ui_policy UserProfileUi:
    show EditProfileButton when can(UserProfileWrite(self.user_id))
    show AdminPanelLink when can(AdminPanelView)
"#,
    );

    let Node::UiPolicy(policy) = &items[0] else {
        panic!("expected ui policy");
    };
    assert_eq!(policy.name, "UserProfileUi");
    assert!(matches!(
        &policy.items[0],
        UiPolicyItem::Show { key, condition, .. }
            if key == "EditProfileButton" && condition == "can(UserProfileWrite(self.user_id))"
    ));
}
