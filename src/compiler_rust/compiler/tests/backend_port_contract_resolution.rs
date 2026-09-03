use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

#[test]
fn static_backend_registry_resolves_versioned_backend_port_contract() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let owner_path = repository.join("src/compiler/70.backend/backend_port.spl");
    let consumer_path = repository.join(
        "src/compiler/70.backend/backend/static_backend_registry.spl",
    );
    let owner = fs::read_to_string(&owner_path).expect("read backend-port owner");
    let consumer = fs::read_to_string(&consumer_path).expect("read backend registry");

    assert!(owner.contains("pub const BACKEND_PORT_ERROR_MAJOR = \"PLUG-E-MAJOR\""));
    assert!(owner.contains("pub const BACKEND_PORT_IFACE_DIGEST ="));
    assert!(owner.contains("pub struct BackendPortV1:"));
    assert!(owner.contains("pub trait BackendPlugin:"));
    assert!(consumer.contains("BACKEND_PORT_ERROR_MAJOR"));

    let owner_ast = Parser::new(&owner).parse().expect("parse backend-port owner");
    hir::lower_with_context_and_project_hint(&owner_ast, &owner_path, Some(&repository))
        .expect("lower backend-port owner");

    let consumer_ast = Parser::new(&consumer)
        .parse()
        .expect("parse static backend registry");
    hir::lower_with_context_and_project_hint(
        &consumer_ast,
        &consumer_path,
        Some(&repository),
    )
    .expect("resolve backend-port constants during project-aware lowering");
}
