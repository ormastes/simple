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
