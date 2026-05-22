use std::collections::BTreeSet;
use std::path::{Component, Path};

use crate::hir::{
    HirAopAdvice, HirArchRule, HirModule, HirSandboxItem, HirSecurityGate, HirSecurityItem, HirSecurityPolicy,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecurityInventory {
    pub gate_inventory_md: String,
    pub access_matrix_sdn: String,
    pub security_aspects_spl: String,
    pub security_aop_sdn: String,
    pub sandbox_manifest_sdn: String,
    pub violations_sdn: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecuritySourceFile {
    pub path: String,
    pub source: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecurityCoordinate {
    pub feature: Option<String>,
    pub layer: Option<String>,
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

pub fn build_security_inventory(module: &HirModule) -> SecurityInventory {
    let gates = collect_gates(module);
    let gate_names: BTreeSet<String> = gates.iter().map(|gate| gate.name.clone()).collect();
    let sandbox_names: BTreeSet<String> = module
        .sandbox_policies
        .iter()
        .map(|sandbox| sandbox.name.clone())
        .collect();

    SecurityInventory {
        gate_inventory_md: render_gate_inventory(&gates),
        access_matrix_sdn: render_access_matrix(&module.security_policies),
        security_aspects_spl: render_security_aspects(&module.security_policies, &gates),
        security_aop_sdn: render_security_aop_lowering(&lower_security_to_aop(module)),
        sandbox_manifest_sdn: render_sandbox_manifest(module, &gates),
        violations_sdn: render_violations(&gates, &gate_names, &sandbox_names),
    }
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
            security_root: true,
        };
    }

    for window in parts.windows(4) {
        if window[0] == "src" && window[1] == "feature" {
            return SecurityCoordinate {
                feature: Some(window[2].clone()),
                layer: Some(window[3].clone()),
                security_root: false,
            };
        }
    }

    SecurityCoordinate {
        feature: None,
        layer: None,
        security_root: false,
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
    let boundary_gates = collect_boundary_gates(modules);
    let feature_graph = build_feature_graph(files, &known_features);

    for edge in feature_graph {
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

    for file in files {
        let coordinate = infer_security_coordinate(Path::new(&file.path));
        let Some(from_feature) = coordinate.feature.as_deref() else {
            continue;
        };
        if coordinate.security_root || from_feature == "security" {
            continue;
        }
        for (line_no, line) in file.source.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            if uses_authorization_predicate(trimmed) && !is_security_observation(&file.source, line_no) {
                count += 1;
                out.push_str("  - code: SEC301\n");
                out.push_str("    message: authorization predicate used outside security root\n");
                out.push_str(&format!("    file: {}\n", file.path));
                out.push_str(&format!("    line: {}\n", line_no + 1));
                out.push_str("    required: move authoritative authorization to src/security/** or mark UI-only code with @security_observation\n");
            }

            if let Some(api) = raw_ambient_api(trimmed) {
                count += 1;
                out.push_str("  - code: SEC401\n");
                out.push_str("    message: raw ambient authority API used without an explicit capability handle\n");
                out.push_str(&format!("    file: {}\n", file.path));
                out.push_str(&format!("    line: {}\n", line_no + 1));
                out.push_str(&format!("    api: {}\n", api));
                out.push_str("    required: inject a narrowed object-capability handle such as ReadDir, WriteDir, NetworkEndpoint, EnvVar, or AuditLog\n");
            }
        }
    }

    if count == 0 {
        out.push_str("  []\n");
    }
    out
}

fn build_feature_graph(files: &[SecuritySourceFile], known_features: &BTreeSet<String>) -> Vec<SecurityFeatureEdge> {
    let mut edges = Vec::new();
    for file in files {
        let coordinate = infer_security_coordinate(Path::new(&file.path));
        let Some(from_feature) = coordinate.feature.as_deref() else {
            continue;
        };
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
                        from_feature: from_feature.to_string(),
                        to_feature: feature,
                        target_layer: layer,
                        kind: SecurityFeatureEdgeKind::Import,
                        text: trimmed.to_string(),
                    });
                }
            }

            for target_feature in referenced_features(trimmed, known_features) {
                edges.push(SecurityFeatureEdge {
                    file: file.path.clone(),
                    line: line_no + 1,
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

fn boundary_gate_for<'a>(rules: &'a [SecurityBoundaryGate], from_feature: &str, to_feature: &str) -> Option<&'a str> {
    rules
        .iter()
        .find(|rule| rule.from_feature == from_feature && rule.to_feature == to_feature)
        .map(|rule| rule.gate.as_str())
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

fn is_security_observation(source: &str, line_no: usize) -> bool {
    let lines: Vec<&str> = source.lines().collect();
    let start = line_no.saturating_sub(3);
    lines[start..line_no]
        .iter()
        .any(|line| line.trim() == "@security_observation")
}

fn raw_ambient_api(line: &str) -> Option<&'static str> {
    let apis = [
        ("File.open", "File.open"),
        ("Network.connect", "Network.connect"),
        ("Env.get", "Env.get"),
        ("Process.spawn", "Process.spawn"),
    ];
    apis.iter()
        .find_map(|(pattern, api)| line.contains(pattern).then_some(*api))
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
                HirSecurityItem::Allow { from, to, through } => {
                    out.push_str("  allow:\n");
                    out.push_str(&format!("    from: {}\n", from));
                    out.push_str(&format!("    to: {}\n", to));
                    if let Some(gate) = through {
                        out.push_str(&format!("    through: {}\n", gate));
                    }
                }
                HirSecurityItem::Deny {
                    from,
                    to,
                    except,
                    direct,
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
                }
                _ => {}
            }
        }
    }
    out
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

fn render_violations(
    gates: &[HirSecurityGate],
    _gate_names: &BTreeSet<String>,
    sandbox_names: &BTreeSet<String>,
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
    }
    if count == 0 {
        out.push_str("  []\n");
    }
    out
}
