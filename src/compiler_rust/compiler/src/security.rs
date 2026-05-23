use std::collections::BTreeSet;
use std::path::{Component, Path};

use simple_sdn::SdnValue;

use crate::hir::{
    HirAopAdvice, HirArchRule, HirCapabilityItem, HirExpr, HirExprKind, HirFunction, HirImport, HirModule,
    HirSandboxItem, HirSecurityGate, HirSecurityItem, HirSecurityPolicy, HirStmt, HirUiPolicyItem,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecurityInventory {
    pub layer_map_sdn: String,
    pub feature_map_sdn: String,
    pub gate_map_sdn: String,
    pub gate_inventory_md: String,
    pub access_matrix_sdn: String,
    pub security_aspects_spl: String,
    pub security_aop_sdn: String,
    pub capability_manifest_sdn: String,
    pub sandbox_manifest_sdn: String,
    pub ui_policy_sdn: String,
    pub violations_sdn: String,
    pub report_md: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecuritySourceFile {
    pub path: String,
    pub source: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecuritySdnConfig {
    pub path: String,
    pub source: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecurityCoordinate {
    pub feature: Option<String>,
    pub layer: Option<String>,
    pub trust: Option<String>,
    pub runtime: Option<String>,
    pub security_root: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SecurityBoundaryGate {
    from_feature: String,
    to_feature: String,
    gate: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SecurityFeatureEdge {
    file: String,
    line: usize,
    from_layer: Option<String>,
    from_feature: String,
    to_feature: String,
    target_layer: Option<String>,
    kind: SecurityFeatureEdgeKind,
    text: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SecurityFeatureEdgeKind {
    Import,
    Call,
}

#[derive(Debug, Clone)]
pub struct SecurityAopLowering {
    pub aop_advices: Vec<HirAopAdvice>,
    pub arch_rules: Vec<HirArchRule>,
    pub advice_plans: Vec<SecurityAdvicePlan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecurityAdvicePlan {
    pub gate: String,
    pub gate_id: u64,
    pub advice_function: String,
    pub steps: Vec<SecurityAdviceStep>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SecurityAdviceStep {
    EnterGate {
        gate: String,
        gate_id: u64,
    },
    RequirePolicy {
        policy: String,
        policy_id: u64,
    },
    EnterSandbox {
        sandbox: String,
        sandbox_id: u64,
    },
    AuditStart {
        gate: String,
        gate_id: u64,
        audit: String,
        audit_id: u64,
    },
    Proceed,
    AuditSuccess {
        gate: String,
        gate_id: u64,
    },
    AuditFailure {
        gate: String,
        gate_id: u64,
    },
    ExitSandbox {
        sandbox_id: u64,
    },
    ExitGate {
        gate_id: u64,
    },
}

const DEFAULT_SECURITY_LAYERS: &[&str] = &["ui", "api", "service", "domain", "port", "infra", "driver", "kernel"];

pub fn build_security_inventory(module: &HirModule) -> SecurityInventory {
    let gates = collect_gates(module);
    let gate_names: BTreeSet<String> = gates.iter().map(|gate| gate.name.clone()).collect();
    let sandbox_names: BTreeSet<String> = module
        .sandbox_policies
        .iter()
        .map(|sandbox| sandbox.name.clone())
        .collect();
    let capability_names: BTreeSet<String> = module
        .capability_policies
        .iter()
        .map(|capability| capability.name.clone())
        .collect();

    let violations_sdn = render_violations(&gates, &gate_names, &sandbox_names, &capability_names);
    SecurityInventory {
        layer_map_sdn: String::new(),
        feature_map_sdn: String::new(),
        gate_map_sdn: String::new(),
        gate_inventory_md: render_gate_inventory(&gates),
        access_matrix_sdn: render_access_matrix(&module.security_policies),
        security_aspects_spl: render_security_aspects(&module.security_policies, &gates),
        security_aop_sdn: render_security_aop_lowering(&lower_security_to_aop(module)),
        capability_manifest_sdn: render_capability_manifest(module),
        sandbox_manifest_sdn: render_sandbox_manifest(module, &gates),
        ui_policy_sdn: render_ui_policy(&[], module),
        report_md: render_security_report(
            gates.len(),
            module.security_policies.len(),
            sandbox_names.len(),
            capability_names.len(),
            &violations_sdn,
        ),
        violations_sdn,
    }
}

pub fn build_security_inventory_for_source(file: &SecuritySourceFile, module: &HirModule) -> SecurityInventory {
    let gates = convention_enriched_gates(file, module);
    let gate_names: BTreeSet<String> = gates.iter().map(|gate| gate.name.clone()).collect();
    let sandbox_names: BTreeSet<String> = module
        .sandbox_policies
        .iter()
        .map(|sandbox| sandbox.name.clone())
        .collect();
    let capability_names: BTreeSet<String> = module
        .capability_policies
        .iter()
        .map(|capability| capability.name.clone())
        .collect();

    let violations_sdn = render_violations(&gates, &gate_names, &sandbox_names, &capability_names);
    SecurityInventory {
        layer_map_sdn: String::new(),
        feature_map_sdn: String::new(),
        gate_map_sdn: build_security_gate_map(std::slice::from_ref(file), std::slice::from_ref(module)),
        gate_inventory_md: render_gate_inventory(&gates),
        access_matrix_sdn: render_access_matrix(&module.security_policies),
        security_aspects_spl: render_security_aspects(&module.security_policies, &gates),
        security_aop_sdn: render_security_aop_lowering(&lower_security_to_aop(module)),
        capability_manifest_sdn: render_capability_manifest(module),
        sandbox_manifest_sdn: render_sandbox_manifest(module, &gates),
        ui_policy_sdn: render_ui_policy(std::slice::from_ref(file), module),
        report_md: render_security_report(
            gates.len(),
            module.security_policies.len(),
            sandbox_names.len(),
            capability_names.len(),
            &violations_sdn,
        ),
        violations_sdn,
    }
}

pub fn build_security_maps(files: &[SecuritySourceFile]) -> (String, String) {
    let mut layer_map = String::from("security_layer_map:\n");
    let mut feature_map = String::from("security_feature_map:\n");
    let mut layer_count = 0;
    let mut feature_count = 0;

    for file in files {
        let coordinate = infer_security_coordinate(Path::new(&file.path));
        if let Some(layer) = coordinate.layer.as_deref() {
            layer_count += 1;
            layer_map.push_str("  - file: ");
            layer_map.push_str(&file.path);
            layer_map.push('\n');
            layer_map.push_str("    layer: ");
            layer_map.push_str(layer);
            layer_map.push('\n');
            if let Some(feature) = coordinate.feature.as_deref() {
                layer_map.push_str("    feature: ");
                layer_map.push_str(feature);
                layer_map.push('\n');
            }
        }
        if let Some(feature) = coordinate.feature.as_deref() {
            feature_count += 1;
            feature_map.push_str("  - feature: ");
            feature_map.push_str(feature);
            feature_map.push('\n');
            feature_map.push_str("    file: ");
            feature_map.push_str(&file.path);
            feature_map.push('\n');
            if let Some(layer) = coordinate.layer.as_deref() {
                feature_map.push_str("    layer: ");
                feature_map.push_str(layer);
                feature_map.push('\n');
            }
            if let Some(trust) = coordinate.trust.as_deref() {
                feature_map.push_str("    trust: ");
                feature_map.push_str(trust);
                feature_map.push('\n');
            }
            if let Some(runtime) = coordinate.runtime.as_deref() {
                feature_map.push_str("    runtime: ");
                feature_map.push_str(runtime);
                feature_map.push('\n');
            }
            if coordinate.security_root {
                feature_map.push_str("    security_root: true\n");
            }
        }
    }

    if layer_count == 0 {
        layer_map.push_str("  []\n");
    }
    if feature_count == 0 {
        feature_map.push_str("  []\n");
    }

    (layer_map, feature_map)
}

pub fn build_security_gate_map(files: &[SecuritySourceFile], modules: &[HirModule]) -> String {
    let mut out = String::from("security_gate_map:\n");
    let mut count = 0;
    for (file, module) in files.iter().zip(modules) {
        for gate in convention_enriched_gates(file, module) {
            count += 1;
            out.push_str("  - gate: ");
            out.push_str(&gate.name);
            out.push('\n');
            out.push_str("    file: ");
            out.push_str(&file.path);
            out.push('\n');
            if let Some(from) = gate.from.as_deref() {
                out.push_str("    from: ");
                out.push_str(from);
                out.push('\n');
            }
            if let Some(to) = gate.to.as_deref() {
                out.push_str("    to: ");
                out.push_str(to);
                out.push('\n');
            }
            if convention_gate_boundary_from_path(&file.path).is_some() {
                out.push_str("    inferred: true\n");
            }
        }
    }
    if count == 0 {
        out.push_str("  []\n");
    }
    out
}

pub fn lower_security_to_aop(module: &HirModule) -> SecurityAopLowering {
    let gates = collect_gates(module);
    let mut aop_advices = Vec::new();
    let mut arch_rules = Vec::new();
    let mut advice_plans = Vec::new();

    for gate in &gates {
        let advice_function = format!("__simple_security_gate_{}", gate.name);
        aop_advices.push(HirAopAdvice {
            predicate_text: format!("pc{{ execution(* {}.*(..)) }}", gate.name),
            advice_function: advice_function.clone(),
            form: "around".to_string(),
            priority: 10_000,
        });
        advice_plans.push(SecurityAdvicePlan {
            gate: gate.name.clone(),
            gate_id: security_metadata_id(&gate.name),
            advice_function,
            steps: security_advice_steps(gate),
        });
    }

    for policy in &module.security_policies {
        for item in &policy.items {
            match item {
                HirSecurityItem::Deny {
                    from,
                    to,
                    except,
                    direct,
                    ..
                } => {
                    arch_rules.push(HirArchRule {
                        rule_type: "forbid".to_string(),
                        predicate_text: format!(
                            "pc{{ depend({}, {}) }}",
                            security_clause_to_pattern(from),
                            security_clause_to_pattern(to)
                        ),
                        message: Some(match except {
                            Some(gate) => format!("Security boundary requires gate {}", gate),
                            None if *direct => "Direct security boundary crossing is forbidden".to_string(),
                            None => "Security boundary crossing is forbidden".to_string(),
                        }),
                        priority: 10_000,
                    });
                }
                HirSecurityItem::Allow {
                    from,
                    to,
                    through: None,
                    ..
                } => {
                    arch_rules.push(HirArchRule {
                        rule_type: "allow".to_string(),
                        predicate_text: format!(
                            "pc{{ depend({}, {}) }}",
                            security_clause_to_pattern(from),
                            security_clause_to_pattern(to)
                        ),
                        message: Some("Security policy allows this boundary crossing".to_string()),
                        priority: 10_100,
                    });
                }
                _ => {}
            }
        }
    }

    SecurityAopLowering {
        aop_advices,
        arch_rules,
        advice_plans,
    }
}

pub fn security_metadata_id(value: &str) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in value.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn security_advice_steps(gate: &HirSecurityGate) -> Vec<SecurityAdviceStep> {
    let gate_id = security_metadata_id(&gate.name);
    let mut steps = vec![SecurityAdviceStep::EnterGate {
        gate: gate.name.clone(),
        gate_id,
    }];
    if let Some(policy) = &gate.policy {
        steps.push(SecurityAdviceStep::RequirePolicy {
            policy: policy.clone(),
            policy_id: security_metadata_id(policy),
        });
    }
    if let Some(sandbox) = &gate.sandbox {
        steps.push(SecurityAdviceStep::EnterSandbox {
            sandbox: sandbox.clone(),
            sandbox_id: security_metadata_id(sandbox),
        });
    }
    if let Some(audit) = &gate.audit {
        steps.push(SecurityAdviceStep::AuditStart {
            gate: gate.name.clone(),
            gate_id,
            audit: audit.clone(),
            audit_id: security_metadata_id(audit),
        });
    }
    steps.push(SecurityAdviceStep::Proceed);
    if gate.audit.is_some() {
        steps.push(SecurityAdviceStep::AuditSuccess {
            gate: gate.name.clone(),
            gate_id,
        });
        steps.push(SecurityAdviceStep::AuditFailure {
            gate: gate.name.clone(),
            gate_id,
        });
    }
    if let Some(sandbox) = &gate.sandbox {
        steps.push(SecurityAdviceStep::ExitSandbox {
            sandbox_id: security_metadata_id(sandbox),
        });
    }
    steps.push(SecurityAdviceStep::ExitGate { gate_id });
    steps
}

pub fn infer_security_coordinate(path: &Path) -> SecurityCoordinate {
    let parts: Vec<String> = path
        .components()
        .filter_map(|component| match component {
            Component::Normal(value) => Some(value.to_string_lossy().to_string()),
            _ => None,
        })
        .collect();

    if parts.iter().any(|part| part == "security") {
        return SecurityCoordinate {
            feature: Some("security".to_string()),
            layer: Some("security_gate".to_string()),
            trust: Some("app".to_string()),
            runtime: infer_runtime_dimension(&parts),
            security_root: true,
        };
    }

    for window in parts.windows(4) {
        if window[0] == "src" && window[1] == "feature" {
            let feature = window[2].clone();
            return SecurityCoordinate {
                trust: Some(infer_trust_dimension(&parts, &feature)),
                runtime: infer_runtime_dimension(&parts),
                feature: Some(feature),
                layer: Some(window[3].clone()),
                security_root: false,
            };
        }
    }

    if let Some(src_index) = parts.iter().position(|part| part == "src") {
        if let Some(layer) = parts.get(src_index + 1).filter(|part| is_conventional_layer(part)) {
            let feature_parts = path_feature_parts(&parts[(src_index + 2)..]);
            if !feature_parts.is_empty() {
                let feature = feature_parts.join(".");
                return SecurityCoordinate {
                    trust: Some(infer_trust_dimension(&parts, &feature)),
                    runtime: infer_runtime_dimension(&parts),
                    feature: Some(feature),
                    layer: Some(layer.clone()),
                    security_root: false,
                };
            }
        }
    }

    SecurityCoordinate {
        feature: None,
        layer: None,
        trust: infer_path_trust_dimension(&parts),
        runtime: infer_runtime_dimension(&parts),
        security_root: false,
    }
}

fn path_feature_parts(parts: &[String]) -> Vec<String> {
    let end = parts
        .last()
        .is_some_and(|part| part.rsplit_once('.').is_some())
        .then_some(parts.len().saturating_sub(1))
        .unwrap_or(parts.len());
    parts[..end].to_vec()
}

fn is_conventional_layer(value: &str) -> bool {
    DEFAULT_SECURITY_LAYERS.contains(&value)
}

fn infer_trust_dimension(parts: &[String], feature: &str) -> String {
    infer_path_trust_dimension(parts).unwrap_or_else(|| {
        if feature == "plugin" {
            "plugin".to_string()
        } else {
            "app".to_string()
        }
    })
}

fn infer_path_trust_dimension(parts: &[String]) -> Option<String> {
    if parts.iter().any(|part| part == "untrusted") {
        Some("untrusted".to_string())
    } else if parts.iter().any(|part| part == "third_party" || part == "vendor") {
        Some("third_party".to_string())
    } else if parts.iter().any(|part| part == "plugin" || part == "plugins") {
        Some("plugin".to_string())
    } else if parts.iter().any(|part| part == "kernel") {
        Some("kernel".to_string())
    } else {
        None
    }
}

fn infer_runtime_dimension(parts: &[String]) -> Option<String> {
    if parts
        .iter()
        .any(|part| part == "sandbox" || part == "sandboxed" || part.ends_with("_sandbox"))
    {
        Some("sandboxed".to_string())
    } else if parts.iter().any(|part| part == "baremetal" || part == "kernel") {
        Some("baremetal".to_string())
    } else {
        None
    }
}

pub fn source_security_violations_sdn(files: &[SecuritySourceFile]) -> String {
    source_security_violations_sdn_with_modules(files, &[])
}

pub fn source_security_violations_sdn_with_module(files: &[SecuritySourceFile], module: &HirModule) -> String {
    source_security_violations_sdn_with_modules(files, std::slice::from_ref(module))
}

pub fn source_security_violations_sdn_with_modules(files: &[SecuritySourceFile], modules: &[HirModule]) -> String {
    let mut out = String::from("security_violations:\n");
    let mut count = 0;
    let known_features = known_features(files);
    let mut boundary_gates = collect_boundary_gates(modules);
    boundary_gates.extend(collect_convention_boundary_gates(files, modules));
    let full_lowered_workspace = has_full_lowered_workspace(files, modules);
    let feature_graph = build_security_feature_graph(files, modules, &known_features);
    let hir_authorization_uses = build_hir_authorization_uses(files, modules);
    let hir_ambient_uses = build_hir_ambient_uses(files, modules);

    for edge in feature_graph {
        if edge.to_feature == edge.from_feature {
            if let (Some(from_layer), Some(to_layer)) = (edge.from_layer.as_deref(), edge.target_layer.as_deref()) {
                if is_layer_skip(from_layer, to_layer) {
                    count += 1;
                    out.push_str("  - code: SEC101\n");
                    out.push_str("    message: layer skip denied by convention-first security rules\n");
                    out.push_str(&format!("    file: {}\n", edge.file));
                    out.push_str(&format!("    line: {}\n", edge.line));
                    out.push_str(&format!("    edge: {}\n", edge.kind.as_str()));
                    out.push_str(&format!("    from_layer: {}\n", from_layer));
                    out.push_str(&format!("    to_layer: {}\n", to_layer));
                    out.push_str(&format!("    feature: {}\n", edge.from_feature));
                    out.push_str(
                        "    required: follow the declared layer order or use an explicit gate/port exception\n",
                    );
                }
            }
            continue;
        }
        if edge.to_feature == edge.from_feature || is_shared_feature(&edge.to_feature) {
            continue;
        }
        if matches!(edge.kind, SecurityFeatureEdgeKind::Import) && edge.target_layer.as_deref() == Some("port") {
            continue;
        }

        let configured_gate = boundary_gate_for(&boundary_gates, &edge.from_feature, &edge.to_feature);
        if configured_gate.as_deref().is_some_and(|gate| edge.text.contains(gate)) {
            continue;
        }

        count += 1;
        out.push_str("  - code: SEC201\n");
        out.push_str("    message: forbidden feature crossing without security gate\n");
        out.push_str(&format!("    file: {}\n", edge.file));
        out.push_str(&format!("    line: {}\n", edge.line));
        out.push_str(&format!("    edge: {}\n", edge.kind.as_str()));
        out.push_str(&format!("    from_feature: {}\n", edge.from_feature));
        out.push_str(&format!("    to_feature: {}\n", edge.to_feature));
        if let Some(layer) = &edge.target_layer {
            out.push_str(&format!("    to_layer: {}\n", layer));
        }
        match configured_gate {
            Some(gate) => out.push_str(&format!("    required: route through {}\n", gate)),
            None => out.push_str("    required: route through declared security gate\n"),
        }
    }

    let mut reported_authorization_files = BTreeSet::new();
    let mut reported_ambient_apis = BTreeSet::new();
    if !full_lowered_workspace {
        for file in files {
            let coordinate = infer_security_coordinate(Path::new(&file.path));
            let Some(from_feature) = coordinate.feature.as_deref() else {
                continue;
            };
            if coordinate.security_root || from_feature == "security" {
                continue;
            }
            let mut in_async_function = false;
            let mut async_function_indent = 0usize;
            for (line_no, line) in file.source.lines().enumerate() {
                let trimmed = line.trim();
                let indent = line.len().saturating_sub(line.trim_start().len());
                if leaves_async_function(trimmed, indent, in_async_function, async_function_indent) {
                    in_async_function = false;
                }
                if is_async_function_header(trimmed) {
                    in_async_function = true;
                    async_function_indent = indent;
                }
                if trimmed.is_empty() || trimmed.starts_with('#') {
                    continue;
                }

                if uses_authorization_predicate(trimmed) && !is_security_observation(&file.source, line_no) {
                    reported_authorization_files.insert(file.path.clone());
                    count += 1;
                    out.push_str("  - code: SEC301\n");
                    out.push_str("    message: authorization predicate used outside security root\n");
                    out.push_str(&format!("    file: {}\n", file.path));
                    out.push_str(&format!("    line: {}\n", line_no + 1));
                    render_coordinate_fields(&mut out, &coordinate);
                    out.push_str("    required: move authoritative authorization to src/security/** or mark UI-only code with @security_observation\n");
                }

                if let Some(api) = raw_ambient_api(trimmed) {
                    reported_ambient_apis.insert((file.path.clone(), api.name.to_string()));
                    count += 1;
                    out.push_str("  - code: SEC401\n");
                    out.push_str("    message: raw ambient authority API used without an explicit capability handle\n");
                    out.push_str(&format!("    file: {}\n", file.path));
                    out.push_str(&format!("    line: {}\n", line_no + 1));
                    out.push_str(&format!("    api: {}\n", api.name));
                    render_coordinate_fields(&mut out, &coordinate);
                    out.push_str(&format!(
                        "    required: inject narrowed capability handle {}\n",
                        api.required
                    ));
                    out.push_str(&format!("    replacement: {}\n", api.replacement));
                }

                if in_async_function && uses_thread_local_security_context(trimmed) {
                    count += 1;
                    out.push_str("  - code: SEC501\n");
                    out.push_str("    message: unsafe SecurityContext access inside async function\n");
                    out.push_str(&format!("    file: {}\n", file.path));
                    out.push_str(&format!("    line: {}\n", line_no + 1));
                    render_coordinate_fields(&mut out, &coordinate);
                    out.push_str(
                        "    required: use task-local SecurityContext or pass an explicit context parameter\n",
                    );
                }
            }
        }
    }

    for authorization_use in hir_authorization_uses {
        if !reported_authorization_files.insert(authorization_use.file.to_string()) {
            continue;
        }
        count += 1;
        out.push_str("  - code: SEC301\n");
        out.push_str("    message: resolved authorization predicate used outside security root\n");
        out.push_str(&format!("    file: {}\n", authorization_use.file));
        out.push_str("    line: 1\n");
        out.push_str(&format!("    predicate: {}\n", authorization_use.predicate));
        out.push_str("    edge: resolved_call\n");
        render_coordinate_fields(&mut out, &infer_security_coordinate(Path::new(authorization_use.file)));
        out.push_str("    required: move authoritative authorization to src/security/** or mark UI-only code with @security_observation\n");
    }

    for ambient_use in hir_ambient_uses {
        if !reported_ambient_apis.insert((ambient_use.file.to_string(), ambient_use.api.name.to_string())) {
            continue;
        }
        count += 1;
        out.push_str("  - code: SEC401\n");
        out.push_str("    message: resolved raw ambient authority API used without an explicit capability handle\n");
        out.push_str(&format!("    file: {}\n", ambient_use.file));
        out.push_str("    line: 1\n");
        out.push_str(&format!("    api: {}\n", ambient_use.api.name));
        out.push_str("    edge: resolved_call\n");
        render_coordinate_fields(&mut out, &infer_security_coordinate(Path::new(ambient_use.file)));
        out.push_str(&format!(
            "    required: inject narrowed capability handle {}\n",
            ambient_use.api.required
        ));
        out.push_str(&format!("    replacement: {}\n", ambient_use.api.replacement));
    }

    if count == 0 {
        out.push_str("  []\n");
    }
    out
}

pub fn security_sdn_merge_violations_sdn(modules: &[HirModule], configs: &[SecuritySdnConfig]) -> String {
    let source_rules = collect_source_policy_rules(modules);
    let mut out = String::from("security_sdn_merge_violations:\n");
    let mut count = 0;
    let mut overrides = Vec::new();

    for config in configs {
        match parse_security_sdn_config(config) {
            Ok(mut parsed) => overrides.append(&mut parsed),
            Err(error) => {
                count += 1;
                out.push_str("  - code: SEC603\n");
                out.push_str("    message: invalid security SDN config\n");
                out.push_str(&format!("    config: {}\n", config.path));
                out.push_str(&format!("    error: {}\n", error));
                out.push_str("    required: use documented security.allow/security.deny SDN entries\n");
            }
        }
    }

    for override_rule in overrides {
        if override_rule.action != "allow" {
            continue;
        }
        for source_rule in &source_rules {
            if source_rule.action != "deny" {
                continue;
            }
            if source_rule.from != override_rule.from || source_rule.to != override_rule.to {
                continue;
            }
            if source_rule.final_rule {
                count += 1;
                out.push_str("  - code: SEC601\n");
                out.push_str("    message: SDN override attempts to weaken final source security policy\n");
                out.push_str(&format!("    config: {}\n", override_rule.path));
                out.push_str(&format!("    line: {}\n", override_rule.line));
                out.push_str(&format!("    from: {}\n", override_rule.from));
                out.push_str(&format!("    to: {}\n", override_rule.to));
                out.push_str("    required: remove the override or change the source policy; final policies cannot be relaxed by config\n");
            } else if !source_rule.configurable {
                count += 1;
                out.push_str("  - code: SEC602\n");
                out.push_str("    message: SDN override attempts to weaken non-configurable source security policy\n");
                out.push_str(&format!("    config: {}\n", override_rule.path));
                out.push_str(&format!("    line: {}\n", override_rule.line));
                out.push_str(&format!("    from: {}\n", override_rule.from));
                out.push_str(&format!("    to: {}\n", override_rule.to));
                out.push_str("    required: mark the source rule configurable before SDN can relax it\n");
            }
        }
    }

    if count == 0 {
        out.push_str("  []\n");
    }
    out
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SecurityPolicyRule {
    action: &'static str,
    from: String,
    to: String,
    configurable: bool,
    final_rule: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SecuritySdnOverride {
    action: String,
    from: String,
    to: String,
    path: String,
    line: usize,
}

fn collect_source_policy_rules(modules: &[HirModule]) -> Vec<SecurityPolicyRule> {
    let mut rules = Vec::new();
    for module in modules {
        for policy in &module.security_policies {
            for item in &policy.items {
                match item {
                    HirSecurityItem::Allow {
                        from,
                        to,
                        configurable,
                        final_rule,
                        ..
                    } => rules.push(SecurityPolicyRule {
                        action: "allow",
                        from: security_clause_key(from),
                        to: security_clause_key(to),
                        configurable: *configurable,
                        final_rule: *final_rule,
                    }),
                    HirSecurityItem::Deny {
                        from,
                        to,
                        configurable,
                        final_rule,
                        ..
                    } => rules.push(SecurityPolicyRule {
                        action: "deny",
                        from: security_clause_key(from),
                        to: security_clause_key(to),
                        configurable: *configurable,
                        final_rule: *final_rule,
                    }),
                    _ => {}
                }
            }
        }
    }
    rules
}

fn collect_text_policy_overrides(configs: &[SecuritySdnConfig]) -> Vec<SecuritySdnOverride> {
    let mut overrides = Vec::new();
    for config in configs {
        for (line_no, line) in config.source.lines().enumerate() {
            if let Some((action, from, to)) = parse_sdn_policy_override_line(line) {
                overrides.push(SecuritySdnOverride {
                    action,
                    from,
                    to,
                    path: config.path.clone(),
                    line: line_no + 1,
                });
            }
        }
    }
    overrides
}

fn parse_security_sdn_config(config: &SecuritySdnConfig) -> Result<Vec<SecuritySdnOverride>, String> {
    let value = simple_sdn::parse(&config.source).map_err(|error| error.to_string())?;
    let Some(root) = value.as_dict() else {
        return Err("security SDN config root must be a dictionary".to_string());
    };
    let Some(security) = root.get("security").and_then(SdnValue::as_dict) else {
        return Ok(collect_text_policy_overrides(std::slice::from_ref(config)));
    };

    let mut overrides = Vec::new();
    for action in ["allow", "deny"] {
        if let Some(value) = security.get(action) {
            collect_structured_sdn_overrides(action, value, config, &mut overrides)?;
        }
    }

    if overrides.is_empty() {
        overrides.extend(collect_text_policy_overrides(std::slice::from_ref(config)));
    }
    Ok(overrides)
}

fn collect_structured_sdn_overrides(
    action: &str,
    value: &SdnValue,
    config: &SecuritySdnConfig,
    overrides: &mut Vec<SecuritySdnOverride>,
) -> Result<(), String> {
    if let Some(entries) = value.as_array() {
        for entry in entries {
            collect_structured_sdn_overrides(action, entry, config, overrides)?;
        }
        return Ok(());
    }
    if let Some(line) = value.as_str() {
        if let Some((parsed_action, from, to)) = parse_sdn_policy_override_line(&format!("{} {}", action, line)) {
            overrides.push(SecuritySdnOverride {
                action: parsed_action,
                from,
                to,
                path: config.path.clone(),
                line: 1,
            });
        }
        return Ok(());
    }
    let Some(entry) = value.as_dict() else {
        return Err(format!(
            "security.{} entries must be dictionaries, strings, or arrays",
            action
        ));
    };
    let from = entry
        .get("from")
        .and_then(sdn_security_clause_key)
        .ok_or_else(|| format!("security.{} entry missing from", action))?;
    let to = entry
        .get("to")
        .and_then(sdn_security_clause_key)
        .ok_or_else(|| format!("security.{} entry missing to", action))?;
    overrides.push(SecuritySdnOverride {
        action: action.to_string(),
        from,
        to,
        path: config.path.clone(),
        line: 1,
    });
    Ok(())
}

fn sdn_security_clause_key(value: &SdnValue) -> Option<String> {
    if let Some(text) = value.as_str() {
        return Some(security_clause_key(text));
    }
    let dict = value.as_dict()?;
    for key in ["feature", "security", "layer", "trust"] {
        if let Some(value) = dict.get(key).and_then(SdnValue::as_str) {
            return Some(security_clause_key(&format!("{} {}", key, value)));
        }
    }
    None
}

fn parse_sdn_policy_override_line(line: &str) -> Option<(String, String, String)> {
    let trimmed = line.trim().trim_start_matches('-').trim();
    let action = if let Some(rest) = trimmed.strip_prefix("allow ") {
        ("allow", rest)
    } else if let Some(rest) = trimmed.strip_prefix("deny ") {
        ("deny", rest)
    } else {
        return None;
    };
    let (from, rest) = action.1.split_once("->")?;
    let to = rest
        .split_whitespace()
        .take_while(|part| *part != "through" && *part != "except" && *part != "direct")
        .collect::<Vec<_>>()
        .join(" ");
    Some((
        action.0.to_string(),
        security_clause_key(from),
        security_clause_key(&to),
    ))
}

fn security_clause_key(clause: &str) -> String {
    let normalized = clause
        .trim()
        .trim_matches('{')
        .trim_matches('}')
        .replace(':', " ")
        .replace(',', " ");
    let parts: Vec<&str> = normalized.split_whitespace().collect();
    if parts.len() >= 2 && (parts[0] == "feature" || parts[0] == "security") {
        parts[1..].join(".")
    } else {
        parts.join(".")
    }
}

fn build_security_feature_graph(
    files: &[SecuritySourceFile],
    modules: &[HirModule],
    known_features: &BTreeSet<String>,
) -> Vec<SecurityFeatureEdge> {
    if has_full_lowered_workspace(files, modules) {
        return build_hir_feature_graph(files, modules);
    }

    let mut feature_graph = build_feature_graph(files, known_features);
    feature_graph.extend(build_hir_feature_graph(files, modules));
    feature_graph
}

fn has_full_lowered_workspace(files: &[SecuritySourceFile], modules: &[HirModule]) -> bool {
    !files.is_empty() && files.len() == modules.len()
}

fn build_feature_graph(files: &[SecuritySourceFile], known_features: &BTreeSet<String>) -> Vec<SecurityFeatureEdge> {
    let mut edges = Vec::new();
    for file in files {
        let coordinate = infer_security_coordinate(Path::new(&file.path));
        let Some(from_feature) = coordinate.feature.as_deref() else {
            continue;
        };
        let from_layer = coordinate.layer.clone();
        if coordinate.security_root || from_feature == "security" {
            continue;
        }

        for (line_no, line) in file.source.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            for marker in ["feature.", "feature/"] {
                if let Some((feature, layer)) = feature_import_details(trimmed, marker) {
                    edges.push(SecurityFeatureEdge {
                        file: file.path.clone(),
                        line: line_no + 1,
                        from_layer: from_layer.clone(),
                        from_feature: from_feature.to_string(),
                        to_feature: feature,
                        target_layer: layer,
                        kind: SecurityFeatureEdgeKind::Import,
                        text: trimmed.to_string(),
                    });
                }
            }
            if let Some((feature, layer)) = layer_first_import_details(trimmed) {
                edges.push(SecurityFeatureEdge {
                    file: file.path.clone(),
                    line: line_no + 1,
                    from_layer: from_layer.clone(),
                    from_feature: from_feature.to_string(),
                    to_feature: feature,
                    target_layer: Some(layer),
                    kind: SecurityFeatureEdgeKind::Import,
                    text: trimmed.to_string(),
                });
            }

            for target_feature in referenced_features(trimmed, known_features) {
                edges.push(SecurityFeatureEdge {
                    file: file.path.clone(),
                    line: line_no + 1,
                    from_layer: from_layer.clone(),
                    from_feature: from_feature.to_string(),
                    to_feature: target_feature,
                    target_layer: None,
                    kind: SecurityFeatureEdgeKind::Call,
                    text: trimmed.to_string(),
                });
            }
        }
    }
    edges
}

fn render_coordinate_fields(out: &mut String, coordinate: &SecurityCoordinate) {
    if let Some(feature) = &coordinate.feature {
        out.push_str(&format!("    feature: {}\n", feature));
    }
    if let Some(layer) = &coordinate.layer {
        out.push_str(&format!("    layer: {}\n", layer));
    }
    if let Some(trust) = &coordinate.trust {
        out.push_str(&format!("    trust: {}\n", trust));
    }
    if let Some(runtime) = &coordinate.runtime {
        out.push_str(&format!("    runtime: {}\n", runtime));
    }
}

fn build_hir_feature_graph(files: &[SecuritySourceFile], modules: &[HirModule]) -> Vec<SecurityFeatureEdge> {
    if files.len() != modules.len() {
        return Vec::new();
    }

    let mut edges = Vec::new();
    let mut symbol_features = std::collections::BTreeMap::new();
    for (file, module) in files.iter().zip(modules) {
        let coordinate = infer_security_coordinate(Path::new(&file.path));
        let Some(feature) = coordinate.feature.clone() else {
            continue;
        };
        if coordinate.security_root || feature == "security" {
            continue;
        }
        for function in &module.functions {
            symbol_features.insert(function.name.clone(), (feature.clone(), coordinate.layer.clone()));
            if let Some((owner, _)) = function.name.split_once('.') {
                symbol_features
                    .entry(owner.to_string())
                    .or_insert_with(|| (feature.clone(), coordinate.layer.clone()));
            }
        }
        for (global, _) in &module.globals {
            symbol_features.insert(global.clone(), (feature.clone(), coordinate.layer.clone()));
        }
    }

    for (file, module) in files.iter().zip(modules) {
        let coordinate = infer_security_coordinate(Path::new(&file.path));
        let Some(from_feature) = coordinate.feature.as_deref() else {
            continue;
        };
        if coordinate.security_root || from_feature == "security" {
            continue;
        }

        for import in &module.imports {
            if let Some((to_feature, target_layer)) = hir_import_feature_details(import) {
                edges.push(SecurityFeatureEdge {
                    file: file.path.clone(),
                    line: 1,
                    from_layer: coordinate.layer.clone(),
                    from_feature: from_feature.to_string(),
                    to_feature,
                    target_layer,
                    kind: SecurityFeatureEdgeKind::Import,
                    text: import.from_path.join("."),
                });
            }
        }

        for function in &module.functions {
            for symbol in referenced_hir_symbols(&function.body) {
                if let Some((to_feature, target_layer)) = symbol_features.get(&symbol) {
                    edges.push(SecurityFeatureEdge {
                        file: file.path.clone(),
                        line: 1,
                        from_layer: coordinate.layer.clone(),
                        from_feature: from_feature.to_string(),
                        to_feature: to_feature.clone(),
                        target_layer: target_layer.clone(),
                        kind: SecurityFeatureEdgeKind::Call,
                        text: symbol,
                    });
                }
            }
        }
    }

    edges
}

fn hir_import_feature_details(import: &HirImport) -> Option<(String, Option<String>)> {
    if let Some(feature_index) = import.from_path.iter().position(|part| part == "feature") {
        let feature = import.from_path.get(feature_index + 1)?.clone();
        let layer = import.from_path.get(feature_index + 2).cloned();
        return Some((feature, layer));
    }
    let layer_index = import.from_path.iter().position(|part| is_conventional_layer(part))?;
    let layer = import.from_path.get(layer_index)?.clone();
    let rest = &import.from_path[(layer_index + 1)..];
    let feature = import_feature_path(rest)?;
    Some((feature, Some(layer)))
}

#[derive(Debug, Clone, Copy)]
struct SecurityAuthorizationUse<'a> {
    file: &'a str,
    predicate: &'a str,
}

fn build_hir_authorization_uses<'a>(
    files: &'a [SecuritySourceFile],
    modules: &'a [HirModule],
) -> Vec<SecurityAuthorizationUse<'a>> {
    if files.len() != modules.len() {
        return Vec::new();
    }

    let mut uses = Vec::new();
    for (file, module) in files.iter().zip(modules) {
        let coordinate = infer_security_coordinate(Path::new(&file.path));
        let Some(from_feature) = coordinate.feature.as_deref() else {
            continue;
        };
        if coordinate.security_root || from_feature == "security" || source_has_security_observation(&file.source) {
            continue;
        }

        for function in &module.functions {
            for symbol in referenced_hir_symbols(&function.body) {
                if let Some(predicate) = authorization_predicate_symbol(&symbol) {
                    uses.push(SecurityAuthorizationUse {
                        file: &file.path,
                        predicate,
                    });
                }
            }
        }
    }
    uses
}

#[derive(Debug, Clone, Copy)]
struct SecurityAmbientUse<'a> {
    file: &'a str,
    api: RawAmbientApi,
}

fn build_hir_ambient_uses<'a>(
    files: &'a [SecuritySourceFile],
    modules: &'a [HirModule],
) -> Vec<SecurityAmbientUse<'a>> {
    if files.len() != modules.len() {
        return Vec::new();
    }

    let mut uses = Vec::new();
    for (file, module) in files.iter().zip(modules) {
        let coordinate = infer_security_coordinate(Path::new(&file.path));
        let Some(from_feature) = coordinate.feature.as_deref() else {
            continue;
        };
        if coordinate.security_root || from_feature == "security" {
            continue;
        }

        for function in &module.functions {
            let capability_handles = function_capability_handles(function);
            for symbol in referenced_hir_symbols(&function.body) {
                if let Some(api) = raw_ambient_api_symbol(&symbol) {
                    if capability_requirement_satisfied(api.required, &capability_handles) {
                        continue;
                    }
                    uses.push(SecurityAmbientUse { file: &file.path, api });
                }
            }
        }
    }
    uses
}

fn function_capability_handles(function: &HirFunction) -> BTreeSet<String> {
    function
        .params
        .iter()
        .chain(function.locals.iter())
        .filter_map(|local| local.type_name_hint.as_deref())
        .map(capability_handle_name)
        .filter(|handle| is_builtin_capability_handle(handle))
        .map(ToString::to_string)
        .collect()
}

fn capability_requirement_satisfied(required: &str, handles: &BTreeSet<String>) -> bool {
    required
        .split(" or ")
        .map(str::trim)
        .any(|required_handle| handles.contains(required_handle))
}

fn referenced_hir_symbols(stmts: &[HirStmt]) -> BTreeSet<String> {
    let mut symbols = BTreeSet::new();
    for stmt in stmts {
        collect_hir_stmt_symbols(stmt, &mut symbols);
    }
    symbols
}

fn collect_hir_stmt_symbols(stmt: &HirStmt, symbols: &mut BTreeSet<String>) {
    match stmt {
        HirStmt::Let { value, .. } | HirStmt::Return(value) => {
            if let Some(expr) = value {
                collect_hir_expr_symbols(expr, symbols);
            }
        }
        HirStmt::Assign { target, value } => {
            collect_hir_expr_symbols(target, symbols);
            collect_hir_expr_symbols(value, symbols);
        }
        HirStmt::Expr(expr) => collect_hir_expr_symbols(expr, symbols),
        HirStmt::If {
            condition,
            then_block,
            else_block,
        } => {
            collect_hir_expr_symbols(condition, symbols);
            for stmt in then_block {
                collect_hir_stmt_symbols(stmt, symbols);
            }
            if let Some(else_block) = else_block {
                for stmt in else_block {
                    collect_hir_stmt_symbols(stmt, symbols);
                }
            }
        }
        HirStmt::While { condition, body, .. } => {
            collect_hir_expr_symbols(condition, symbols);
            for stmt in body {
                collect_hir_stmt_symbols(stmt, symbols);
            }
        }
        HirStmt::For { iterable, body, .. } => {
            collect_hir_expr_symbols(iterable, symbols);
            for stmt in body {
                collect_hir_stmt_symbols(stmt, symbols);
            }
        }
        HirStmt::Loop { body, .. } | HirStmt::Defer { body } => {
            for stmt in body {
                collect_hir_stmt_symbols(stmt, symbols);
            }
        }
        HirStmt::Assert { condition, .. } | HirStmt::Assume { condition, .. } | HirStmt::Admit { condition, .. } => {
            collect_hir_expr_symbols(condition, symbols);
        }
        HirStmt::Break
        | HirStmt::Continue
        | HirStmt::ProofHint { .. }
        | HirStmt::Calc { .. }
        | HirStmt::InlineAsm { .. } => {}
    }
}

fn collect_hir_expr_symbols(expr: &HirExpr, symbols: &mut BTreeSet<String>) {
    match &expr.kind {
        HirExprKind::Global(name) => {
            symbols.insert(name.clone());
        }
        HirExprKind::Binary { left, right, .. } => {
            collect_hir_expr_symbols(left, symbols);
            collect_hir_expr_symbols(right, symbols);
        }
        HirExprKind::Unary { operand, .. } => collect_hir_expr_symbols(operand, symbols),
        HirExprKind::Call { func, args } => {
            collect_hir_expr_symbols(func, symbols);
            for arg in args {
                collect_hir_expr_symbols(arg, symbols);
            }
        }
        HirExprKind::MethodCall {
            receiver, method, args, ..
        } => {
            if let HirExprKind::Global(owner) = &receiver.kind {
                symbols.insert(format!("{}.{}", owner, method));
            }
            collect_hir_expr_symbols(receiver, symbols);
            for arg in args {
                collect_hir_expr_symbols(arg, symbols);
            }
        }
        HirExprKind::FieldAccess { receiver, .. } => collect_hir_expr_symbols(receiver, symbols),
        HirExprKind::Index { receiver, index } => {
            collect_hir_expr_symbols(receiver, symbols);
            collect_hir_expr_symbols(index, symbols);
        }
        HirExprKind::Tuple(items) | HirExprKind::Array(items) | HirExprKind::VecLiteral(items) => {
            for item in items {
                collect_hir_expr_symbols(item, symbols);
            }
        }
        HirExprKind::ArrayRepeat { value, count } => {
            collect_hir_expr_symbols(value, symbols);
            collect_hir_expr_symbols(count, symbols);
        }
        HirExprKind::StructInit { fields, .. } => {
            for field in fields {
                collect_hir_expr_symbols(field, symbols);
            }
        }
        HirExprKind::Dict(items) => {
            for (key, value) in items {
                collect_hir_expr_symbols(key, symbols);
                collect_hir_expr_symbols(value, symbols);
            }
        }
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_hir_expr_symbols(condition, symbols);
            collect_hir_expr_symbols(then_branch, symbols);
            if let Some(else_branch) = else_branch {
                collect_hir_expr_symbols(else_branch, symbols);
            }
        }
        HirExprKind::Block(stmts) => {
            for stmt in stmts {
                collect_hir_stmt_symbols(stmt, symbols);
            }
        }
        HirExprKind::Ref(expr)
        | HirExprKind::Deref(expr)
        | HirExprKind::Yield(expr)
        | HirExprKind::GeneratorCreate { body: expr }
        | HirExprKind::FutureCreate { body: expr }
        | HirExprKind::Await(expr)
        | HirExprKind::ActorSpawn { body: expr }
        | HirExprKind::ContractOld(expr) => collect_hir_expr_symbols(expr, symbols),
        HirExprKind::PointerNew { value, .. } => collect_hir_expr_symbols(value, symbols),
        HirExprKind::Cast { expr, .. } => collect_hir_expr_symbols(expr, symbols),
        HirExprKind::Lambda { body, .. } => collect_hir_expr_symbols(body, symbols),
        HirExprKind::BuiltinCall { args, .. } | HirExprKind::GpuIntrinsic { args, .. } => {
            for arg in args {
                collect_hir_expr_symbols(arg, symbols);
            }
        }
        HirExprKind::LetIn { value, body, .. } => {
            collect_hir_expr_symbols(value, symbols);
            collect_hir_expr_symbols(body, symbols);
        }
        HirExprKind::NeighborAccess { array, .. } => collect_hir_expr_symbols(array, symbols),
        HirExprKind::Local(_)
        | HirExprKind::Integer(_)
        | HirExprKind::Float(_)
        | HirExprKind::String(_)
        | HirExprKind::Bool(_)
        | HirExprKind::Nil
        | HirExprKind::ContractResult => {}
    }
}

fn collect_boundary_gates(modules: &[HirModule]) -> Vec<SecurityBoundaryGate> {
    let mut rules = Vec::new();
    for module in modules {
        for gate in collect_gates(module) {
            if let (Some(from), Some(to)) = (gate.from.as_deref(), gate.to.as_deref()) {
                if let (Some(from_feature), Some(to_feature)) = (clause_feature(from), clause_feature(to)) {
                    rules.push(SecurityBoundaryGate {
                        from_feature,
                        to_feature,
                        gate: gate.name,
                    });
                }
            }
        }
        for policy in &module.security_policies {
            for item in &policy.items {
                match item {
                    HirSecurityItem::Allow {
                        from,
                        to,
                        through: Some(gate),
                        ..
                    }
                    | HirSecurityItem::Deny {
                        from,
                        to,
                        except: Some(gate),
                        ..
                    } => {
                        if let (Some(from_feature), Some(to_feature)) = (clause_feature(from), clause_feature(to)) {
                            rules.push(SecurityBoundaryGate {
                                from_feature,
                                to_feature,
                                gate: gate.clone(),
                            });
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    rules
}

fn collect_convention_boundary_gates(files: &[SecuritySourceFile], modules: &[HirModule]) -> Vec<SecurityBoundaryGate> {
    files
        .iter()
        .zip(modules)
        .flat_map(|(file, module)| {
            convention_enriched_gates(file, module).into_iter().filter_map(|gate| {
                let from_feature = gate.from.as_deref().and_then(clause_feature)?;
                let to_feature = gate.to.as_deref().and_then(clause_feature)?;
                Some(SecurityBoundaryGate {
                    from_feature,
                    to_feature,
                    gate: gate.name,
                })
            })
        })
        .collect()
}

fn boundary_gate_for<'a>(rules: &'a [SecurityBoundaryGate], from_feature: &str, to_feature: &str) -> Option<&'a str> {
    rules
        .iter()
        .find(|rule| {
            feature_matches_boundary(from_feature, &rule.from_feature)
                && feature_matches_boundary(to_feature, &rule.to_feature)
        })
        .map(|rule| rule.gate.as_str())
}

fn feature_matches_boundary(feature: &str, boundary_feature: &str) -> bool {
    feature == boundary_feature
        || feature
            .strip_prefix(boundary_feature)
            .is_some_and(|suffix| suffix.starts_with('.'))
}

fn clause_feature(clause: &str) -> Option<String> {
    let mut parts = clause.split_whitespace();
    match (parts.next(), parts.next()) {
        (Some("feature"), Some(feature)) => Some(feature.to_string()),
        _ => None,
    }
}

fn known_features(files: &[SecuritySourceFile]) -> BTreeSet<String> {
    let mut features = BTreeSet::new();
    for file in files {
        if let Some(feature) = infer_security_coordinate(Path::new(&file.path)).feature {
            if feature != "security" {
                features.insert(feature);
            }
        }
    }
    features
}

fn referenced_features(line: &str, known_features: &BTreeSet<String>) -> BTreeSet<String> {
    let mut features = BTreeSet::new();
    if !looks_like_call_reference(line) {
        return features;
    }

    for feature in known_features {
        let pascal = pascal_case(feature);
        if !pascal.is_empty() && line.contains(&pascal) && !line.contains("Gate") {
            features.insert(feature.clone());
        }
    }

    features
}

fn looks_like_call_reference(line: &str) -> bool {
    line.contains('(') || line.contains('.')
}

fn feature_import_details(line: &str, marker: &str) -> Option<(String, Option<String>)> {
    let start = line.find(marker)? + marker.len();
    let rest = &line[start..];
    let (feature, rest) = take_security_ident(rest);
    if feature.is_empty() {
        return None;
    }
    let layer = rest
        .strip_prefix('.')
        .or_else(|| rest.strip_prefix('/'))
        .map(take_security_ident)
        .map(|(layer, _)| layer)
        .filter(|layer| !layer.is_empty());
    Some((feature, layer))
}

fn layer_first_import_details(line: &str) -> Option<(String, String)> {
    for layer in DEFAULT_SECURITY_LAYERS {
        for marker in [format!("{layer}."), format!("{layer}/")] {
            let Some(start) = line.find(&marker).map(|index| index + marker.len()) else {
                continue;
            };
            let rest = &line[start..];
            let separator = if marker.ends_with('.') { '.' } else { '/' };
            let segments = take_security_path_segments(rest, separator);
            let Some(feature) = import_feature_path(&segments) else {
                continue;
            };
            return Some((feature, (*layer).to_string()));
        }
    }
    None
}

fn take_security_path_segments(value: &str, separator: char) -> Vec<String> {
    let mut segments = Vec::new();
    let mut rest = value;
    loop {
        let (segment, next) = take_security_ident(rest);
        if segment.is_empty() {
            break;
        }
        segments.push(segment);
        let Some(after_separator) = next.strip_prefix(separator) else {
            break;
        };
        rest = after_separator;
    }
    segments
}

fn import_feature_path(parts: &[String]) -> Option<String> {
    if parts.is_empty() {
        return None;
    }
    let feature_end = if parts.len() > 1 { parts.len() - 1 } else { parts.len() };
    let feature_parts = &parts[..feature_end];
    (!feature_parts.is_empty()).then(|| feature_parts.join("."))
}

fn take_security_ident(value: &str) -> (String, &str) {
    let end = value
        .char_indices()
        .find_map(|(index, ch)| (!ch.is_ascii_alphanumeric() && ch != '_').then_some(index))
        .unwrap_or(value.len());
    (value[..end].to_string(), &value[end..])
}

impl SecurityFeatureEdgeKind {
    fn as_str(self) -> &'static str {
        match self {
            SecurityFeatureEdgeKind::Import => "import",
            SecurityFeatureEdgeKind::Call => "call",
        }
    }
}

fn pascal_case(value: &str) -> String {
    value
        .split('_')
        .filter(|part| !part.is_empty())
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(first) => format!("{}{}", first.to_ascii_uppercase(), chars.as_str()),
                None => String::new(),
            }
        })
        .collect()
}

fn security_clause_to_pattern(clause: &str) -> String {
    let mut parts = clause.split_whitespace();
    match (parts.next(), parts.next()) {
        (Some(dimension), Some(value)) => format!("{}.{}.**", dimension, value),
        _ => clause.replace(' ', "."),
    }
}

fn is_shared_feature(feature: &str) -> bool {
    matches!(feature, "common" | "auth" | "audit" | "security")
}

fn is_layer_skip(from_layer: &str, to_layer: &str) -> bool {
    let Some(from_index) = layer_index(from_layer) else {
        return false;
    };
    let Some(to_index) = layer_index(to_layer) else {
        return false;
    };
    to_index > from_index + 1
}

fn layer_index(layer: &str) -> Option<usize> {
    DEFAULT_SECURITY_LAYERS.iter().position(|candidate| *candidate == layer)
}

fn uses_authorization_predicate(line: &str) -> bool {
    let patterns = [
        "current_user().is_admin",
        "current_user().has_role",
        ".is_admin",
        ".has_role(",
        "authorize(",
        "check_permission(",
        "require_permission(",
    ];
    patterns.iter().any(|pattern| line.contains(pattern))
}

fn is_async_function_header(line: &str) -> bool {
    line.starts_with("async fn ") || line.starts_with("async fn(")
}

fn leaves_async_function(line: &str, indent: usize, in_async_function: bool, async_function_indent: usize) -> bool {
    in_async_function
        && indent <= async_function_indent
        && (line.starts_with("fn ")
            || line.starts_with("async fn ")
            || line.starts_with("class ")
            || line.starts_with("interface ")
            || line.starts_with("security ")
            || line.starts_with("sandbox ")
            || line.starts_with("capability "))
}

fn uses_thread_local_security_context(line: &str) -> bool {
    line.contains("thread_local") && line.contains("SecurityContext")
}

fn is_security_observation(source: &str, line_no: usize) -> bool {
    let lines: Vec<&str> = source.lines().collect();
    let start = line_no.saturating_sub(3);
    lines[start..line_no]
        .iter()
        .any(|line| line.trim() == "@security_observation")
}

fn source_has_security_observation(source: &str) -> bool {
    source.lines().any(|line| line.trim() == "@security_observation")
}

#[derive(Debug, Clone, Copy)]
struct RawAmbientApi {
    name: &'static str,
    required: &'static str,
    replacement: &'static str,
}

fn raw_ambient_api(line: &str) -> Option<RawAmbientApi> {
    raw_ambient_api_patterns()
        .iter()
        .find_map(|(pattern, api)| line.contains(pattern).then_some(*api))
}

fn raw_ambient_api_symbol(symbol: &str) -> Option<RawAmbientApi> {
    raw_ambient_api_patterns()
        .iter()
        .find_map(|(pattern, api)| (symbol == *pattern).then_some(*api))
}

fn raw_ambient_api_patterns() -> &'static [(&'static str, RawAmbientApi)] {
    &[
        (
            "File.open",
            RawAmbientApi {
                name: "File.open",
                required: "ReadFile or WriteFile",
                replacement: "ReadFile.read_text or WriteFile.write_text",
            },
        ),
        (
            "Network.connect",
            RawAmbientApi {
                name: "Network.connect",
                required: "NetworkEndpoint",
                replacement: "NetworkEndpoint.connect",
            },
        ),
        (
            "Env.get",
            RawAmbientApi {
                name: "Env.get",
                required: "EnvVar",
                replacement: "EnvVar.get",
            },
        ),
        (
            "Process.spawn",
            RawAmbientApi {
                name: "Process.spawn",
                required: "ProcessSpawner",
                replacement: "ProcessSpawner.run",
            },
        ),
        (
            "file_read_text",
            RawAmbientApi {
                name: "file_read_text",
                required: "ReadFile",
                replacement: "ReadFile.read_text",
            },
        ),
        (
            "rt_file_read_text",
            RawAmbientApi {
                name: "rt_file_read_text",
                required: "ReadFile",
                replacement: "ReadFile.read_text",
            },
        ),
        (
            "file_write_text",
            RawAmbientApi {
                name: "file_write_text",
                required: "WriteFile",
                replacement: "WriteFile.write_text",
            },
        ),
        (
            "file_write",
            RawAmbientApi {
                name: "file_write",
                required: "WriteFile",
                replacement: "WriteFile.write_text",
            },
        ),
        (
            "rt_file_write_text_at",
            RawAmbientApi {
                name: "rt_file_write_text_at",
                required: "WriteFile",
                replacement: "WriteFile.write_text",
            },
        ),
        (
            "rt_file_write_text",
            RawAmbientApi {
                name: "rt_file_write_text",
                required: "WriteFile",
                replacement: "WriteFile.write_text",
            },
        ),
        (
            "tcp_stream_connect",
            RawAmbientApi {
                name: "tcp_stream_connect",
                required: "NetworkEndpoint",
                replacement: "NetworkEndpoint.connect",
            },
        ),
        (
            "TcpStream.connect",
            RawAmbientApi {
                name: "TcpStream.connect",
                required: "NetworkEndpoint",
                replacement: "NetworkEndpoint.connect",
            },
        ),
        (
            "udp_socket_connect",
            RawAmbientApi {
                name: "udp_socket_connect",
                required: "NetworkEndpoint",
                replacement: "NetworkEndpoint.connect",
            },
        ),
        (
            "env_get",
            RawAmbientApi {
                name: "env_get",
                required: "EnvVar",
                replacement: "EnvVar.get",
            },
        ),
        (
            "rt_env_get",
            RawAmbientApi {
                name: "rt_env_get",
                required: "EnvVar",
                replacement: "EnvVar.get",
            },
        ),
        (
            "process_run",
            RawAmbientApi {
                name: "process_run",
                required: "ProcessSpawner",
                replacement: "ProcessSpawner.run",
            },
        ),
        (
            "rt_process_run",
            RawAmbientApi {
                name: "rt_process_run",
                required: "ProcessSpawner",
                replacement: "ProcessSpawner.run",
            },
        ),
        (
            "rt_process_spawn_async",
            RawAmbientApi {
                name: "rt_process_spawn_async",
                required: "ProcessSpawner",
                replacement: "ProcessSpawner.run",
            },
        ),
    ]
}

fn authorization_predicate_symbol(symbol: &str) -> Option<&'static str> {
    if symbol == "authorize" || symbol == "check_permission" || symbol == "require_permission" {
        return Some(match symbol {
            "authorize" => "authorize",
            "check_permission" => "check_permission",
            _ => "require_permission",
        });
    }
    if symbol == "current_user.is_admin" || symbol.ends_with(".is_admin") {
        return Some("is_admin");
    }
    if symbol == "current_user.has_role" || symbol.ends_with(".has_role") {
        return Some("has_role");
    }
    None
}

fn collect_gates(module: &HirModule) -> Vec<HirSecurityGate> {
    let mut gates = module.security_gates.clone();
    for policy in &module.security_policies {
        for item in &policy.items {
            if let HirSecurityItem::Gate(gate) = item {
                gates.push(gate.clone());
            }
        }
    }
    gates
}

fn convention_enriched_gates(file: &SecuritySourceFile, module: &HirModule) -> Vec<HirSecurityGate> {
    let mut gates = collect_gates(module);
    if let Some((from_feature, to_feature)) = convention_gate_boundary_from_path(&file.path) {
        for gate in &mut gates {
            apply_gate_boundary_if_missing(gate, &from_feature, &to_feature);
        }
    }
    gates
}

fn apply_gate_boundary_if_missing(gate: &mut HirSecurityGate, from_feature: &str, to_feature: &str) {
    if gate.from.is_none() {
        gate.from = Some(format!("feature {from_feature}"));
    }
    if gate.to.is_none() {
        gate.to = Some(format!("feature {to_feature}"));
    }
}

fn convention_gate_boundary_from_path(path: &str) -> Option<(String, String)> {
    let path = Path::new(path);
    let parts: Vec<String> = path
        .components()
        .filter_map(|component| match component {
            Component::Normal(value) => Some(value.to_string_lossy().to_string()),
            _ => None,
        })
        .collect();
    let gate_index = parts
        .windows(3)
        .position(|window| window[0] == "src" && window[1] == "security" && window[2] == "gate")
        .map(|index| index + 2)?;
    let file_name = parts.get(gate_index + 1)?;
    let stem = file_name.rsplit_once('.').map(|(stem, _)| stem).unwrap_or(file_name);
    let mut features: Vec<&str> = stem
        .trim_end_matches("_gate")
        .split('_')
        .filter(|part| !part.is_empty())
        .collect();
    if features.len() < 2 {
        return None;
    }
    let from_feature = features.remove(0).to_string();
    let to_feature = features.join(".");
    Some((from_feature, to_feature))
}

fn render_gate_inventory(gates: &[HirSecurityGate]) -> String {
    let mut out = String::from("# Security Gate Inventory\n\n");
    if gates.is_empty() {
        out.push_str("_No security gates declared._\n");
        return out;
    }
    out.push_str("| Gate | From | To | Policy | Audit | Sandbox | Grants |\n");
    out.push_str("|------|------|----|--------|-------|---------|--------|\n");
    for gate in gates {
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} |\n",
            gate.name,
            gate.from.as_deref().unwrap_or(""),
            gate.to.as_deref().unwrap_or(""),
            gate.policy.as_deref().unwrap_or(""),
            gate.audit.as_deref().unwrap_or(""),
            gate.sandbox.as_deref().unwrap_or(""),
            gate.grants.join(", ")
        ));
    }
    out
}

fn render_access_matrix(policies: &[HirSecurityPolicy]) -> String {
    let mut out = String::from("security_access_matrix:\n");
    for policy in policies {
        out.push_str(&format!("  policy: {}\n", policy.name));
        out.push_str(&format!("  conventions: {}\n", policy.conventions_enabled));
        for item in &policy.items {
            match item {
                HirSecurityItem::Default { action } => out.push_str(&format!("  default: {}\n", action)),
                HirSecurityItem::Allow {
                    from,
                    to,
                    through,
                    configurable,
                    final_rule,
                } => {
                    out.push_str("  allow:\n");
                    out.push_str(&format!("    from: {}\n", from));
                    out.push_str(&format!("    to: {}\n", to));
                    if let Some(gate) = through {
                        out.push_str(&format!("    through: {}\n", gate));
                    }
                    render_policy_mutability(&mut out, *configurable, *final_rule);
                }
                HirSecurityItem::Deny {
                    from,
                    to,
                    except,
                    direct,
                    configurable,
                    final_rule,
                } => {
                    out.push_str("  deny:\n");
                    out.push_str(&format!("    from: {}\n", from));
                    out.push_str(&format!("    to: {}\n", to));
                    if let Some(gate) = except {
                        out.push_str(&format!("    except: {}\n", gate));
                    }
                    if *direct {
                        out.push_str("    direct: true\n");
                    }
                    render_policy_mutability(&mut out, *configurable, *final_rule);
                }
                _ => {}
            }
        }
    }
    out
}

fn render_policy_mutability(out: &mut String, configurable: bool, final_rule: bool) {
    if configurable {
        out.push_str("    configurable: true\n");
    }
    if final_rule {
        out.push_str("    final: true\n");
    }
}

fn render_security_aspects(policies: &[HirSecurityPolicy], gates: &[HirSecurityGate]) -> String {
    let mut out = String::from("# Generated from security policy. Do not edit by hand.\n\n");
    out.push_str("aspect GeneratedSecurityBoundary:\n");
    let mut boundary_count = 0;
    for policy in policies {
        for item in &policy.items {
            match item {
                HirSecurityItem::Allow {
                    from,
                    to,
                    through: Some(gate),
                    ..
                } => {
                    boundary_count += 1;
                    out.push_str("    allow call:\n");
                    out.push_str(&format!("        from {}\n", from));
                    out.push_str(&format!("        to {}\n", to));
                    out.push_str(&format!("        through security_gate({})\n", gate));
                }
                HirSecurityItem::Deny {
                    from,
                    to,
                    except: Some(gate),
                    ..
                } => {
                    boundary_count += 1;
                    out.push_str("    forbid call:\n");
                    out.push_str(&format!("        from {}\n", from));
                    out.push_str(&format!("        to {}\n", to));
                    out.push_str(&format!("        unless security_gate({})\n", gate));
                }
                HirSecurityItem::Deny {
                    from, to, except: None, ..
                } => {
                    boundary_count += 1;
                    out.push_str("    forbid call:\n");
                    out.push_str(&format!("        from {}\n", from));
                    out.push_str(&format!("        to {}\n", to));
                }
                _ => {}
            }
        }
    }
    if boundary_count == 0 {
        out.push_str("    # no explicit boundary rules declared; convention diagnostics still apply\n");
    }

    for gate in gates {
        out.push_str("\n");
        out.push_str(&format!("aspect Generated{}Advice:\n", gate.name));
        out.push_str(&format!("    around execution({}.*):\n", gate.name));
        out.push_str(&format!("        SecurityRuntime.enter_gate(\"{}\")\n", gate.name));
        if let Some(policy) = &gate.policy {
            out.push_str(&format!("        PolicyRuntime.require(\"{}\", args)\n", policy));
        }
        if let Some(sandbox) = &gate.sandbox {
            out.push_str(&format!("        SandboxRuntime.enter(\"{}\")\n", sandbox));
        }
        if let Some(audit) = &gate.audit {
            out.push_str(&format!(
                "        Audit.log_start(\"{}\", \"{}\", args)\n",
                gate.name, audit
            ));
        }
        out.push_str("        try:\n");
        out.push_str("            result = proceed()\n");
        if gate.audit.is_some() {
            out.push_str(&format!("            Audit.log_success(\"{}\", result)\n", gate.name));
        }
        out.push_str("            return result\n");
        out.push_str("        except e:\n");
        if gate.audit.is_some() {
            out.push_str(&format!("            Audit.log_failure(\"{}\", e)\n", gate.name));
        }
        out.push_str("            raise e\n");
        out.push_str("        finally:\n");
        if gate.sandbox.is_some() {
            out.push_str("            SandboxRuntime.exit()\n");
        }
        out.push_str("            SecurityRuntime.exit_gate()\n");
    }

    out
}

fn render_security_aop_lowering(lowering: &SecurityAopLowering) -> String {
    let mut out = String::from("security_aop_lowering:\n");
    out.push_str("  advices:\n");
    if lowering.aop_advices.is_empty() {
        out.push_str("    []\n");
    } else {
        for advice in &lowering.aop_advices {
            out.push_str("    - form: ");
            out.push_str(&advice.form);
            out.push('\n');
            out.push_str("      predicate: ");
            out.push_str(&advice.predicate_text);
            out.push('\n');
            out.push_str("      advice: ");
            out.push_str(&advice.advice_function);
            out.push('\n');
            out.push_str(&format!("      priority: {}\n", advice.priority));
        }
    }

    out.push_str("  arch_rules:\n");
    if lowering.arch_rules.is_empty() {
        out.push_str("    []\n");
    } else {
        for rule in &lowering.arch_rules {
            out.push_str("    - type: ");
            out.push_str(&rule.rule_type);
            out.push('\n');
            out.push_str("      predicate: ");
            out.push_str(&rule.predicate_text);
            out.push('\n');
            if let Some(message) = &rule.message {
                out.push_str("      message: ");
                out.push_str(message);
                out.push('\n');
            }
            out.push_str(&format!("      priority: {}\n", rule.priority));
        }
    }
    out.push_str("  advice_plans:\n");
    if lowering.advice_plans.is_empty() {
        out.push_str("    []\n");
    } else {
        for plan in &lowering.advice_plans {
            out.push_str("    - gate: ");
            out.push_str(&plan.gate);
            out.push('\n');
            out.push_str(&format!("      gate_id: {}\n", plan.gate_id));
            out.push_str("      advice: ");
            out.push_str(&plan.advice_function);
            out.push('\n');
            out.push_str("      steps:\n");
            for step in &plan.steps {
                render_security_advice_step(&mut out, step);
            }
        }
    }
    out
}

fn render_security_advice_step(out: &mut String, step: &SecurityAdviceStep) {
    match step {
        SecurityAdviceStep::EnterGate { gate, gate_id } => {
            out.push_str("        - enter_gate: ");
            out.push_str(gate);
            out.push('\n');
            out.push_str(&format!("          id: {}\n", gate_id));
        }
        SecurityAdviceStep::RequirePolicy { policy, policy_id } => {
            out.push_str("        - require_policy: ");
            out.push_str(policy);
            out.push('\n');
            out.push_str(&format!("          id: {}\n", policy_id));
        }
        SecurityAdviceStep::EnterSandbox { sandbox, sandbox_id } => {
            out.push_str("        - enter_sandbox: ");
            out.push_str(sandbox);
            out.push('\n');
            out.push_str(&format!("          id: {}\n", sandbox_id));
        }
        SecurityAdviceStep::AuditStart {
            gate,
            gate_id,
            audit,
            audit_id,
        } => {
            out.push_str("        - audit_start: ");
            out.push_str(gate);
            out.push('\n');
            out.push_str(&format!("          gate_id: {}\n", gate_id));
            out.push_str("          audit: ");
            out.push_str(audit);
            out.push('\n');
            out.push_str(&format!("          audit_id: {}\n", audit_id));
        }
        SecurityAdviceStep::Proceed => out.push_str("        - proceed\n"),
        SecurityAdviceStep::AuditSuccess { gate, gate_id } => {
            out.push_str("        - audit_success: ");
            out.push_str(gate);
            out.push('\n');
            out.push_str(&format!("          id: {}\n", gate_id));
        }
        SecurityAdviceStep::AuditFailure { gate, gate_id } => {
            out.push_str("        - audit_failure: ");
            out.push_str(gate);
            out.push('\n');
            out.push_str(&format!("          id: {}\n", gate_id));
        }
        SecurityAdviceStep::ExitSandbox { sandbox_id } => {
            out.push_str("        - exit_sandbox\n");
            out.push_str(&format!("          id: {}\n", sandbox_id));
        }
        SecurityAdviceStep::ExitGate { gate_id } => {
            out.push_str("        - exit_gate\n");
            out.push_str(&format!("          id: {}\n", gate_id));
        }
    }
}

fn render_sandbox_manifest(module: &HirModule, gates: &[HirSecurityGate]) -> String {
    let mut out = String::from("sandbox_manifest:\n");
    for sandbox in &module.sandbox_policies {
        out.push_str(&format!("  {}:\n", sandbox.name));
        for item in &sandbox.items {
            match item {
                HirSandboxItem::Backend { name } => out.push_str(&format!("    backend: {}\n", name)),
                HirSandboxItem::Rule { key, value } => out.push_str(&format!("    {}: {}\n", key, value)),
            }
        }
        let grants: Vec<String> = gates
            .iter()
            .filter(|gate| gate.sandbox.as_deref() == Some(sandbox.name.as_str()))
            .flat_map(|gate| gate.grants.clone())
            .collect();
        if !grants.is_empty() {
            out.push_str("    capabilities:\n");
            for grant in grants {
                out.push_str(&format!("      - {}\n", grant));
            }
        }
    }
    out
}

fn render_capability_manifest(module: &HirModule) -> String {
    let mut out = String::from("capability_manifest:\n");
    if module.capability_policies.is_empty() {
        out.push_str("  builtin:\n");
        for capability in builtin_capability_handles() {
            out.push_str(&format!("    - {}\n", capability));
        }
        return out;
    }
    for capability in &module.capability_policies {
        out.push_str(&format!("  {}:\n", capability.name));
        if capability.items.is_empty() {
            out.push_str("    rules: []\n");
        }
        for item in &capability.items {
            match item {
                HirCapabilityItem::Rule { key, value } => out.push_str(&format!("    {}: {}\n", key, value)),
            }
        }
    }
    out
}

fn render_ui_policy(files: &[SecuritySourceFile], module: &HirModule) -> String {
    let mut out = String::from("ui_policy:\n");
    out.push_str("  permission_snapshot:\n");
    out.push_str("    authority: display_only\n");
    out.push_str("    source: server_signed_snapshot\n");
    out.push_str("    server_gate_required: true\n");
    out.push_str("    policy_version_required: true\n");
    out.push_str("    entries:\n");
    let mut count = 0;
    for policy in &module.ui_policies {
        for item in &policy.items {
            match item {
                HirUiPolicyItem::Show { key, condition } => {
                    count += 1;
                    render_ui_policy_entry(&mut out, key, None, None, condition);
                }
                HirUiPolicyItem::Raw { text } => {
                    count += 1;
                    render_ui_policy_entry(&mut out, text, None, None, "");
                }
            }
        }
    }
    for file in files {
        for (line_no, line) in file.source.lines().enumerate() {
            if line.trim() == "@security_observation" {
                count += 1;
                let key = security_observation_key(&file.source, line_no)
                    .unwrap_or_else(|| format!("{}:{}", file.path, line_no + 1));
                let condition = security_observation_condition(&file.source, line_no).unwrap_or_default();
                render_ui_policy_entry(&mut out, &key, Some(&file.path), Some(line_no + 1), &condition);
            }
        }
    }
    if count == 0 {
        out.push_str("      []\n");
    }
    out
}

fn render_ui_policy_entry(out: &mut String, key: &str, file: Option<&str>, line: Option<usize>, condition: &str) {
    out.push_str("      - key: ");
    out.push_str(key);
    out.push('\n');
    if let Some(file) = file {
        out.push_str(&format!("        file: {}\n", file));
    }
    if let Some(line) = line {
        out.push_str(&format!("        line: {}\n", line));
    }
    out.push_str("        authority: display_only\n");
    out.push_str("        server_gate_required: true\n");
    if !condition.is_empty() {
        out.push_str(&format!("        condition: {}\n", condition));
        if let Some(scope) = permission_scope_from_condition(condition) {
            out.push_str(&format!("        scope: {}\n", scope));
        }
    }
}

fn security_observation_key(source: &str, annotation_line: usize) -> Option<String> {
    source
        .lines()
        .skip(annotation_line + 1)
        .map(str::trim)
        .find(|line| !line.is_empty() && !line.starts_with('#'))
        .and_then(|line| {
            line.strip_prefix("fn ")
                .or_else(|| line.strip_prefix("async fn "))
                .and_then(|rest| rest.split(['(', ':']).next())
                .map(str::trim)
                .filter(|name| !name.is_empty())
                .map(ToString::to_string)
        })
}

fn security_observation_condition(source: &str, annotation_line: usize) -> Option<String> {
    source
        .lines()
        .skip(annotation_line + 1)
        .map(str::trim)
        .find(|line| {
            !line.is_empty() && !line.starts_with('#') && !line.starts_with("fn ") && !line.starts_with("async fn ")
        })
        .map(|line| line.strip_prefix("return ").unwrap_or(line).to_string())
}

fn permission_scope_from_condition(condition: &str) -> Option<String> {
    if condition.contains(".is_admin") || condition.contains("has_role(\"admin\")") {
        Some("admin".to_string())
    } else if condition.contains("current_user()") {
        Some("authenticated".to_string())
    } else if condition.contains("can(") {
        Some(
            condition
                .split("can(")
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or("capability")
                .trim()
                .to_string(),
        )
    } else {
        None
    }
}

fn render_security_report(
    gate_count: usize,
    policy_count: usize,
    sandbox_count: usize,
    capability_count: usize,
    violations_sdn: &str,
) -> String {
    let violation_count = violations_sdn.matches("  - code:").count();
    let mut out = String::from("# Security Report\n\n");
    out.push_str("## Summary\n\n");
    out.push_str(&format!("- Gates: {}\n", gate_count));
    out.push_str(&format!("- Policies: {}\n", policy_count));
    out.push_str(&format!("- Sandboxes: {}\n", sandbox_count));
    out.push_str(&format!("- Capabilities: {}\n", capability_count));
    out.push_str(&format!("- Violations: {}\n", violation_count));
    out
}

fn render_violations(
    gates: &[HirSecurityGate],
    _gate_names: &BTreeSet<String>,
    sandbox_names: &BTreeSet<String>,
    capability_names: &BTreeSet<String>,
) -> String {
    let mut out = String::from("security_violations:\n");
    let mut count = 0;
    for gate in gates {
        if let Some(sandbox) = &gate.sandbox {
            if !sandbox_names.contains(sandbox) {
                count += 1;
                out.push_str("  - code: SEC_MANIFEST_MISSING_SANDBOX\n");
                out.push_str(&format!("    gate: {}\n", gate.name));
                out.push_str(&format!("    sandbox: {}\n", sandbox));
            }
        }
        if gate.from.is_none() || gate.to.is_none() {
            count += 1;
            out.push_str("  - code: SEC_GATE_INCOMPLETE_BOUNDARY\n");
            out.push_str(&format!("    gate: {}\n", gate.name));
        }
        for grant in &gate.grants {
            let handle = capability_handle_name(grant);
            if !is_builtin_capability_handle(handle) && !capability_names.contains(handle) {
                count += 1;
                out.push_str("  - code: SEC_CAPABILITY_UNKNOWN\n");
                out.push_str(&format!("    gate: {}\n", gate.name));
                out.push_str(&format!("    grant: {}\n", grant));
                out.push_str("    required: declare capability or use a built-in native capability handle\n");
            }
        }
    }
    if count == 0 {
        out.push_str("  []\n");
    }
    out
}

fn capability_handle_name(grant: &str) -> &str {
    grant
        .split_once('[')
        .map(|(name, _)| name.trim())
        .unwrap_or_else(|| grant.trim())
}

fn is_builtin_capability_handle(name: &str) -> bool {
    builtin_capability_handles().contains(&name)
}

fn builtin_capability_handles() -> &'static [&'static str] {
    &[
        "ReadDir",
        "WriteDir",
        "ReadFile",
        "WriteFile",
        "NetworkEndpoint",
        "EnvVar",
        "AuditLog",
        "ProcessSpawner",
    ]
}
