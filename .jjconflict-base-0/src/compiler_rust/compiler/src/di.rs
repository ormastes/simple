//! Dependency injection configuration and predicate parsing.

use crate::predicate::{MatchContext, Predicate, PredicateContext};
use crate::predicate_parser;
use simple_sdn::SdnValue;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiMode {
    Compile,
    Runtime,
    Mixed,
    Hybrid,
    Manual,
}

impl DiMode {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "compile" => Ok(DiMode::Compile),
            "runtime" => Ok(DiMode::Runtime),
            "mixed" => Ok(DiMode::Mixed),
            "hybrid" => Ok(DiMode::Hybrid),
            "manual" => Ok(DiMode::Manual),
            _ => Err(format!("unknown di.mode '{}'", value)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiScope {
    Singleton,
    Transient,
    Scoped,
    Thread,
    Task,
    Arena,
    Static,
    Extern,
}

impl DiScope {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "Singleton" | "singleton" => Ok(DiScope::Singleton),
            "Transient" | "transient" => Ok(DiScope::Transient),
            "Scoped" | "scoped" | "request" => Ok(DiScope::Scoped),
            "Thread" | "thread" => Ok(DiScope::Thread),
            "Task" | "task" => Ok(DiScope::Task),
            "Arena" | "arena" => Ok(DiScope::Arena),
            "Static" | "static" => Ok(DiScope::Static),
            "Extern" | "extern" => Ok(DiScope::Extern),
            _ => Err(format!("unknown scope '{}'", value)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct DiBindingRule {
    pub predicate: Predicate,
    pub impl_type: String,
    pub scope: DiScope,
    pub priority: i64,
    pub order: usize,
    pub raw_predicate: String,
    pub configurable: bool,
    pub final_binding: bool,
    pub default_instance_class: Option<String>,
}

#[derive(Debug, Clone, Default)]
pub struct DiProfile {
    pub bindings: Vec<DiBindingRule>,
}

#[derive(Debug, Clone)]
pub struct DiConfig {
    pub mode: DiMode,
    pub conventions: DiConventionConfig,
    pub graph: Option<String>,
    pub roots: Vec<String>,
    pub scans: Vec<String>,
    pub loads: Vec<String>,
    pub runtime_slots: Vec<DiRuntimeSlot>,
    pub profiles: HashMap<String, DiProfile>,
    /// Which concurrent backend to use (pure_std or native).
    pub concurrent_backend: crate::concurrent_providers::ConcurrentBackend,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiConventionConfig {
    pub self_binding: bool,
    pub single_visible_impl: bool,
    pub naming_fallback: bool,
    pub folder_fallback: bool,
    pub std_defaults: bool,
}

impl Default for DiConventionConfig {
    fn default() -> Self {
        Self {
            self_binding: true,
            single_visible_impl: true,
            naming_fallback: true,
            folder_fallback: true,
            std_defaults: true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct DiRuntimeSlot {
    pub type_name: String,
    pub qualifier: Option<String>,
    pub default_impl: Option<String>,
}

#[derive(Debug, Clone)]
pub struct DiResolveError {
    pub profile: String,
    pub matches: Vec<(String, i64, i32)>,
}

/// Helper to create a match context for DI binding selection.
pub fn create_di_match_context<'a>(type_name: &'a str, module_path: &'a str, attrs: &'a [String]) -> MatchContext<'a> {
    MatchContext::new()
        .with_type_name(type_name)
        .with_module_path(module_path)
        .with_attrs(attrs)
}

impl DiConfig {
    pub fn ensure_default_profile(&mut self) {
        self.profiles.entry("default".to_string()).or_default();
    }

    pub fn select_binding(
        &self,
        profile: &str,
        ctx: &MatchContext<'_>,
    ) -> Result<Option<&DiBindingRule>, DiResolveError> {
        let Some(profile_cfg) = self.profiles.get(profile) else {
            return Ok(None);
        };

        let mut matches = Vec::new();
        for binding in &profile_cfg.bindings {
            if binding.predicate.matches(ctx) {
                let specificity = binding.predicate.specificity();
                matches.push((binding, specificity));
            }
        }

        if matches.is_empty() {
            return Ok(None);
        }

        matches.sort_by(|(a, a_spec), (b, b_spec)| {
            a.priority
                .cmp(&b.priority)
                .then_with(|| a_spec.cmp(b_spec))
                .then_with(|| b.order.cmp(&a.order))
        });

        let (winner, _) = matches.last().unwrap();
        Ok(Some(*winner))
    }

    pub fn binding_allows_config_override(
        &self,
        profile: &str,
        ctx: &MatchContext<'_>,
    ) -> Result<bool, DiResolveError> {
        Ok(self
            .select_binding(profile, ctx)?
            .map(|binding| binding.configurable && !binding.final_binding)
            .unwrap_or(false))
    }
}

pub fn parse_di_config(toml: &toml::Value) -> Result<Option<DiConfig>, String> {
    let Some(di_table) = toml.get("di").and_then(|v| v.as_table()) else {
        return Ok(None);
    };

    let mode = di_table
        .get("mode")
        .and_then(|v| v.as_str())
        .map(DiMode::parse)
        .transpose()?
        .unwrap_or(DiMode::Hybrid);
    let conventions = parse_convention_config(di_table)?;

    let graph = di_table.get("graph").and_then(|v| v.as_str()).map(|s| s.to_string());

    let roots = parse_string_or_array(di_table.get("root").or_else(|| di_table.get("roots")), "di.root")?;
    let scans = parse_string_or_array(di_table.get("scan").or_else(|| di_table.get("scans")), "di.scan")?;
    let loads = parse_string_or_array(di_table.get("load").or_else(|| di_table.get("loads")), "di.load")?;
    for path in &loads {
        validate_local_child_config_path(path)?;
    }

    let runtime_slots = parse_runtime_slots(di_table.get("runtime_slots").or_else(|| di_table.get("slots")))?;

    let mut profiles = HashMap::new();
    if let Some(profiles_table) = di_table.get("profiles").and_then(|v| v.as_table()) {
        for (profile_name, profile_value) in profiles_table {
            let mut profile = DiProfile::default();
            let bindings = match profile_value.get("bindings") {
                None => Vec::new(),
                Some(value) => value
                    .as_array()
                    .ok_or_else(|| format!("di.profiles.{}.bindings must be an array", profile_name))?
                    .clone(),
            };

            for (idx, binding_val) in bindings.iter().enumerate() {
                let binding = binding_val
                    .as_table()
                    .ok_or_else(|| format!("di.profiles.{}.bindings[{}] must be a table", profile_name, idx))?;

                let predicate_raw = binding
                    .get("on")
                    .or_else(|| binding.get("predicate"))
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| format!("di.profiles.{}.bindings[{}] missing 'on' predicate", profile_name, idx))?;
                let predicate = predicate_parser::parse_predicate(predicate_raw)?;
                // Validate that the predicate is legal for DI context
                predicate
                    .validate(PredicateContext::DependencyInjection)
                    .map_err(|e| format!("invalid predicate for DI binding: {}", e))?;

                let impl_type = binding
                    .get("impl")
                    .or_else(|| binding.get("impl_type"))
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| format!("di.profiles.{}.bindings[{}] missing 'impl' type", profile_name, idx))?
                    .to_string();

                let scope = binding
                    .get("scope")
                    .and_then(|v| v.as_str())
                    .map(DiScope::parse)
                    .transpose()?
                    .unwrap_or(DiScope::Transient);

                let priority = binding.get("priority").and_then(|v| v.as_integer()).unwrap_or(0);
                let configurable = binding.get("configurable").and_then(|v| v.as_bool()).unwrap_or(false);
                let final_binding = binding
                    .get("final")
                    .or_else(|| binding.get("final_binding"))
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false);
                if configurable && final_binding {
                    return Err(format!(
                        "di.profiles.{}.bindings[{}] cannot be both configurable and final",
                        profile_name, idx
                    ));
                }
                let default_instance_class = binding
                    .get("default")
                    .or_else(|| binding.get("default_impl"))
                    .or_else(|| binding.get("default_instance_class"))
                    .and_then(|v| v.as_str())
                    .map(|s| s.to_string());

                profile.bindings.push(DiBindingRule {
                    predicate,
                    impl_type,
                    scope,
                    priority,
                    order: idx,
                    raw_predicate: predicate_raw.to_string(),
                    configurable,
                    final_binding,
                    default_instance_class,
                });
            }

            profiles.insert(profile_name.clone(), profile);
        }
    }

    let concurrent_backend = di_table
        .get("concurrent_backend")
        .and_then(|v| v.as_str())
        .map(crate::concurrent_providers::ConcurrentBackend::parse)
        .transpose()?
        .unwrap_or_default();

    let mut config = DiConfig {
        mode,
        conventions,
        graph,
        roots,
        scans,
        loads,
        runtime_slots,
        profiles,
        concurrent_backend,
    };
    config.ensure_default_profile();
    Ok(Some(config))
}

pub fn parse_di_sdn_config(source: &str) -> Result<Option<DiConfig>, String> {
    let value = simple_sdn::parse(source).map_err(|e| format!("invalid DI SDN config: {}", e))?;
    parse_di_sdn_value(&value)
}

pub fn parse_di_sdn_value(value: &SdnValue) -> Result<Option<DiConfig>, String> {
    let Some(root) = value.as_dict() else {
        return Err("DI SDN config root must be a dictionary".to_string());
    };

    let di_value = root.get("di");
    let di_table = di_value.and_then(SdnValue::as_dict);
    let has_di_bind = root.contains_key("di_bind") || di_table.is_some_and(|di| di.contains_key("di_bind"));
    if di_table.is_none() && !has_di_bind {
        return Ok(None);
    }
    let empty = indexmap::IndexMap::new();
    let di_table = di_table.unwrap_or(&empty);

    let mode = di_table
        .get("mode")
        .and_then(sdn_string)
        .map(|s| DiMode::parse(&s))
        .transpose()?
        .unwrap_or(DiMode::Hybrid);
    let conventions = parse_sdn_convention_config(di_table.get("conventions").or_else(|| di_table.get("convention")))?;
    let graph = di_table.get("graph").and_then(sdn_string);

    let roots = parse_sdn_string_or_array(di_table.get("root").or_else(|| di_table.get("roots")), "di.root")?;
    let scans = parse_sdn_string_or_array(di_table.get("scan").or_else(|| di_table.get("scans")), "di.scan")?
        .into_iter()
        .map(normalize_sdn_scan_pattern)
        .collect();
    let loads = parse_sdn_string_or_array(di_table.get("load").or_else(|| di_table.get("loads")), "di.load")?;
    for path in &loads {
        validate_local_child_config_path(path)?;
    }

    let mut runtime_slots = Vec::new();
    for key in ["runtime_slot", "runtime_slots", "slots"] {
        runtime_slots.extend(parse_sdn_runtime_slots(di_table.get(key), &format!("di.{}", key))?);
    }

    let mut profiles = HashMap::new();
    collect_sdn_profile("default", &SdnValue::Dict(di_table.clone()), &mut profiles)?;

    if let Some(profiles_value) = root.get("profile").or_else(|| root.get("profiles")) {
        let profiles_map = profiles_value
            .as_dict()
            .ok_or_else(|| "profile/profiles must be a dictionary".to_string())?;
        for (profile_name, profile_value) in profiles_map {
            collect_sdn_profile(profile_name, profile_value, &mut profiles)?;
        }
    }

    for table in [di_table.get("di_bind"), root.get("di_bind")].into_iter().flatten() {
        collect_sdn_bind_table("default", table, &mut profiles)?;
    }

    let concurrent_backend = di_table
        .get("concurrent_backend")
        .and_then(sdn_string)
        .map(|s| crate::concurrent_providers::ConcurrentBackend::parse(&s))
        .transpose()?
        .unwrap_or_default();

    let mut config = DiConfig {
        mode,
        conventions,
        graph,
        roots,
        scans,
        loads,
        runtime_slots,
        profiles,
        concurrent_backend,
    };
    config.ensure_default_profile();
    Ok(Some(config))
}

fn parse_string_or_array(value: Option<&toml::Value>, field: &str) -> Result<Vec<String>, String> {
    match value {
        None => Ok(Vec::new()),
        Some(v) => {
            if let Some(s) = v.as_str() {
                return Ok(vec![s.to_string()]);
            }
            let arr = v
                .as_array()
                .ok_or_else(|| format!("{} must be a string or array of strings", field))?;
            arr.iter()
                .enumerate()
                .map(|(idx, item)| {
                    item.as_str()
                        .map(|s| s.to_string())
                        .ok_or_else(|| format!("{}[{}] must be a string", field, idx))
                })
                .collect()
        }
    }
}

fn parse_convention_config(di_table: &toml::value::Table) -> Result<DiConventionConfig, String> {
    let Some(value) = di_table.get("conventions").or_else(|| di_table.get("convention")) else {
        return Ok(DiConventionConfig::default());
    };

    if let Some(enabled) = value.as_bool() {
        return Ok(DiConventionConfig {
            self_binding: enabled,
            single_visible_impl: enabled,
            naming_fallback: enabled,
            folder_fallback: enabled,
            std_defaults: enabled,
        });
    }

    let table = value
        .as_table()
        .ok_or_else(|| "di.conventions must be a boolean or table".to_string())?;
    let bool_field = |name: &str, default: bool| -> Result<bool, String> {
        table
            .get(name)
            .map(|v| {
                v.as_bool()
                    .ok_or_else(|| format!("di.conventions.{} must be a boolean", name))
            })
            .transpose()
            .map(|v| v.unwrap_or(default))
    };
    let defaults = DiConventionConfig::default();
    Ok(DiConventionConfig {
        self_binding: bool_field("self_binding", defaults.self_binding)?,
        single_visible_impl: bool_field("single_visible_impl", defaults.single_visible_impl)?,
        naming_fallback: bool_field("naming_fallback", defaults.naming_fallback)?,
        folder_fallback: bool_field("folder_fallback", defaults.folder_fallback)?,
        std_defaults: bool_field("std_defaults", defaults.std_defaults)?,
    })
}

fn parse_runtime_slots(value: Option<&toml::Value>) -> Result<Vec<DiRuntimeSlot>, String> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    let arr = value
        .as_array()
        .ok_or_else(|| "di.runtime_slots must be an array".to_string())?;
    let mut slots = Vec::new();
    for (idx, slot_value) in arr.iter().enumerate() {
        let slot = slot_value
            .as_table()
            .ok_or_else(|| format!("di.runtime_slots[{}] must be a table", idx))?;
        let type_name = slot
            .get("type")
            .or_else(|| slot.get("type_name"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("di.runtime_slots[{}] missing type", idx))?
            .to_string();
        let qualifier = slot
            .get("named")
            .or_else(|| slot.get("qualifier"))
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());
        let default_impl = slot
            .get("default")
            .or_else(|| slot.get("default_impl"))
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());
        slots.push(DiRuntimeSlot {
            type_name,
            qualifier,
            default_impl,
        });
    }
    Ok(slots)
}

fn parse_sdn_string_or_array(value: Option<&SdnValue>, field: &str) -> Result<Vec<String>, String> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    if let Some(s) = sdn_string(value) {
        return Ok(vec![normalize_sdn_string_field(s, field)]);
    }
    let array = value
        .as_array()
        .ok_or_else(|| format!("{} must be a string or array of strings", field))?;
    array
        .iter()
        .enumerate()
        .map(|(idx, item)| {
            sdn_string(item)
                .map(|s| normalize_sdn_string_field(s, field))
                .ok_or_else(|| format!("{}[{}] must be a string", field, idx))
        })
        .collect()
}

fn normalize_sdn_string_field(value: String, field: &str) -> String {
    if field.contains("scan") && value.ends_with('.') {
        format!("{}*", value)
    } else {
        value
    }
}

fn normalize_sdn_scan_pattern(pattern: String) -> String {
    if pattern.ends_with('.') {
        format!("{}*", pattern)
    } else {
        pattern
    }
}

fn parse_sdn_convention_config(value: Option<&SdnValue>) -> Result<DiConventionConfig, String> {
    let Some(value) = value else {
        return Ok(DiConventionConfig::default());
    };
    if let Some(enabled) = value.as_bool() {
        return Ok(DiConventionConfig {
            self_binding: enabled,
            single_visible_impl: enabled,
            naming_fallback: enabled,
            folder_fallback: enabled,
            std_defaults: enabled,
        });
    }
    let table = value
        .as_dict()
        .ok_or_else(|| "di.conventions must be a boolean or dictionary".to_string())?;
    let defaults = DiConventionConfig::default();
    Ok(DiConventionConfig {
        self_binding: sdn_bool_field(
            table.get("self_binding"),
            defaults.self_binding,
            "di.conventions.self_binding",
        )?,
        single_visible_impl: sdn_bool_field(
            table.get("single_visible_impl"),
            defaults.single_visible_impl,
            "di.conventions.single_visible_impl",
        )?,
        naming_fallback: sdn_bool_field(
            table.get("naming_fallback"),
            defaults.naming_fallback,
            "di.conventions.naming_fallback",
        )?,
        folder_fallback: sdn_bool_field(
            table.get("folder_fallback"),
            defaults.folder_fallback,
            "di.conventions.folder_fallback",
        )?,
        std_defaults: sdn_bool_field(
            table.get("std_defaults"),
            defaults.std_defaults,
            "di.conventions.std_defaults",
        )?,
    })
}

fn sdn_bool_field(value: Option<&SdnValue>, default: bool, field: &str) -> Result<bool, String> {
    value
        .map(|v| v.as_bool().ok_or_else(|| format!("{} must be a boolean", field)))
        .transpose()
        .map(|v| v.unwrap_or(default))
}

fn parse_sdn_runtime_slots(value: Option<&SdnValue>, field: &str) -> Result<Vec<DiRuntimeSlot>, String> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    match value {
        SdnValue::Dict(map) => map
            .iter()
            .map(|(type_name, slot_value)| sdn_slot_from_value(type_name, slot_value, field))
            .collect(),
        SdnValue::Array(items) => items
            .iter()
            .enumerate()
            .map(|(idx, item)| {
                let slot = item
                    .as_dict()
                    .ok_or_else(|| format!("{}[{}] must be a dictionary", field, idx))?;
                let type_name = slot
                    .get("type")
                    .or_else(|| slot.get("type_name"))
                    .and_then(sdn_string)
                    .ok_or_else(|| format!("{}[{}] missing type", field, idx))?;
                let qualifier = slot.get("named").or_else(|| slot.get("qualifier")).and_then(sdn_string);
                let default_impl = slot
                    .get("default")
                    .or_else(|| slot.get("default_impl"))
                    .or_else(|| slot.get("impl"))
                    .and_then(sdn_string);
                Ok(DiRuntimeSlot {
                    type_name,
                    qualifier,
                    default_impl,
                })
            })
            .collect(),
        SdnValue::Table { fields, rows, .. } => {
            let fields = fields
                .as_ref()
                .ok_or_else(|| format!("{} table must use named fields", field))?;
            rows.iter()
                .enumerate()
                .map(|(idx, row)| sdn_slot_from_table_row(fields, row, field, idx))
                .collect()
        }
        _ => Err(format!("{} must be a dictionary, array, or table", field)),
    }
}

fn sdn_slot_from_value(type_name: &str, value: &SdnValue, field: &str) -> Result<DiRuntimeSlot, String> {
    if let Some(default_impl) = sdn_string(value) {
        return Ok(DiRuntimeSlot {
            type_name: type_name.to_string(),
            qualifier: None,
            default_impl: Some(default_impl),
        });
    }
    let table = value
        .as_dict()
        .ok_or_else(|| format!("{}.{} must be a string or dictionary", field, type_name))?;
    Ok(DiRuntimeSlot {
        type_name: table
            .get("type")
            .or_else(|| table.get("type_name"))
            .and_then(sdn_string)
            .unwrap_or_else(|| type_name.to_string()),
        qualifier: table
            .get("named")
            .or_else(|| table.get("qualifier"))
            .and_then(sdn_string),
        default_impl: table
            .get("default")
            .or_else(|| table.get("default_impl"))
            .or_else(|| table.get("impl"))
            .and_then(sdn_string),
    })
}

fn sdn_slot_from_table_row(
    fields: &[String],
    row: &[SdnValue],
    field: &str,
    row_idx: usize,
) -> Result<DiRuntimeSlot, String> {
    let type_name = sdn_table_field(fields, row, "type")
        .or_else(|| sdn_table_field(fields, row, "type_name"))
        .ok_or_else(|| format!("{} row {} missing type", field, row_idx))?;
    Ok(DiRuntimeSlot {
        type_name,
        qualifier: sdn_table_field(fields, row, "named").or_else(|| sdn_table_field(fields, row, "qualifier")),
        default_impl: sdn_table_field(fields, row, "default")
            .or_else(|| sdn_table_field(fields, row, "default_impl"))
            .or_else(|| sdn_table_field(fields, row, "impl")),
    })
}

fn collect_sdn_profile(
    profile_name: &str,
    value: &SdnValue,
    profiles: &mut HashMap<String, DiProfile>,
) -> Result<(), String> {
    let Some(profile_table) = value.as_dict() else {
        return Err(format!("DI profile '{}' must be a dictionary", profile_name));
    };
    let lifetime_table = profile_table
        .get("lifetime")
        .or_else(|| profile_table.get("lifetimes"))
        .and_then(SdnValue::as_dict);

    for bind_key in ["bind", "binds"] {
        let Some(bind_value) = profile_table.get(bind_key) else {
            continue;
        };
        let bind_table = bind_value
            .as_dict()
            .ok_or_else(|| format!("DI profile '{}.{}' must be a dictionary", profile_name, bind_key))?;
        for (service, target_value) in bind_table {
            let (target, scope, configurable, final_binding, priority) =
                parse_sdn_binding_target(service, target_value, lifetime_table)?;
            push_binding(
                profiles.entry(profile_name.to_string()).or_default(),
                service,
                &target,
                scope,
                priority,
                configurable,
                final_binding,
            )?;
        }
    }

    for table_key in ["di_bind", "bindings"] {
        if let Some(table) = profile_table.get(table_key) {
            collect_sdn_bind_table(profile_name, table, profiles)?;
        }
    }
    Ok(())
}

fn parse_sdn_binding_target(
    service: &str,
    value: &SdnValue,
    lifetime_table: Option<&indexmap::IndexMap<String, SdnValue>>,
) -> Result<(String, DiScope, bool, bool, i64), String> {
    let lifetime_scope = lifetime_table
        .and_then(|table| table.get(service))
        .and_then(sdn_string)
        .map(|scope| DiScope::parse(&scope))
        .transpose()?;
    if let Some(target) = sdn_string(value) {
        return Ok((target, lifetime_scope.unwrap_or(DiScope::Transient), false, false, 0));
    }
    let table = value
        .as_dict()
        .ok_or_else(|| format!("DI bind.{} must be a string or dictionary", service))?;
    let target = table
        .get("impl")
        .or_else(|| table.get("impl_type"))
        .or_else(|| table.get("class"))
        .and_then(sdn_string)
        .ok_or_else(|| format!("DI bind.{} missing impl", service))?;
    let scope = table
        .get("lifetime")
        .or_else(|| table.get("scope"))
        .and_then(sdn_string)
        .map(|scope| DiScope::parse(&scope))
        .transpose()?
        .or(lifetime_scope)
        .unwrap_or(DiScope::Transient);
    let configurable = table.get("configurable").and_then(SdnValue::as_bool).unwrap_or(false);
    let final_binding = table
        .get("final")
        .or_else(|| table.get("final_binding"))
        .and_then(SdnValue::as_bool)
        .unwrap_or(false);
    let priority = table.get("priority").and_then(SdnValue::as_i64).unwrap_or(0);
    Ok((target, scope, configurable, final_binding, priority))
}

fn collect_sdn_bind_table(
    profile_name: &str,
    value: &SdnValue,
    profiles: &mut HashMap<String, DiProfile>,
) -> Result<(), String> {
    match value {
        SdnValue::Table { fields, rows, .. } => {
            let fields = fields
                .as_ref()
                .ok_or_else(|| "di_bind table must use named fields".to_string())?;
            for (idx, row) in rows.iter().enumerate() {
                let service =
                    sdn_table_field(fields, row, "type").ok_or_else(|| format!("di_bind row {} missing type", idx))?;
                let target = sdn_table_field(fields, row, "impl")
                    .or_else(|| sdn_table_field(fields, row, "impl_type"))
                    .ok_or_else(|| format!("di_bind row {} missing impl", idx))?;
                let scope = sdn_table_field(fields, row, "lifetime")
                    .or_else(|| sdn_table_field(fields, row, "scope"))
                    .map(|scope| DiScope::parse(&scope))
                    .transpose()?
                    .unwrap_or(DiScope::Transient);
                let configurable = sdn_table_field(fields, row, "configurable")
                    .map(|value| parse_sdn_bool_text(&value, "di_bind configurable"))
                    .transpose()?
                    .unwrap_or(false);
                let final_binding = sdn_table_field(fields, row, "final")
                    .or_else(|| sdn_table_field(fields, row, "final_binding"))
                    .map(|value| parse_sdn_bool_text(&value, "di_bind final"))
                    .transpose()?
                    .unwrap_or(false);
                let priority = sdn_table_field(fields, row, "priority")
                    .map(|value| {
                        value
                            .parse::<i64>()
                            .map_err(|_| format!("di_bind priority '{}' must be an integer", value))
                    })
                    .transpose()?
                    .unwrap_or(0);
                let target_profile =
                    sdn_table_field(fields, row, "profile").unwrap_or_else(|| profile_name.to_string());
                push_binding(
                    profiles.entry(target_profile).or_default(),
                    &service,
                    &target,
                    scope,
                    priority,
                    configurable,
                    final_binding,
                )?;
            }
            Ok(())
        }
        SdnValue::Array(items) => {
            for (idx, item) in items.iter().enumerate() {
                let table = item
                    .as_dict()
                    .ok_or_else(|| format!("bindings[{}] must be a dictionary", idx))?;
                let service = table
                    .get("type")
                    .or_else(|| table.get("service"))
                    .and_then(sdn_string)
                    .ok_or_else(|| format!("bindings[{}] missing type", idx))?;
                let target = table
                    .get("impl")
                    .or_else(|| table.get("impl_type"))
                    .and_then(sdn_string)
                    .ok_or_else(|| format!("bindings[{}] missing impl", idx))?;
                let scope = table
                    .get("lifetime")
                    .or_else(|| table.get("scope"))
                    .and_then(sdn_string)
                    .map(|scope| DiScope::parse(&scope))
                    .transpose()?
                    .unwrap_or(DiScope::Transient);
                let configurable = table.get("configurable").and_then(SdnValue::as_bool).unwrap_or(false);
                let final_binding = table
                    .get("final")
                    .or_else(|| table.get("final_binding"))
                    .and_then(SdnValue::as_bool)
                    .unwrap_or(false);
                let priority = table.get("priority").and_then(SdnValue::as_i64).unwrap_or(0);
                push_binding(
                    profiles.entry(profile_name.to_string()).or_default(),
                    &service,
                    &target,
                    scope,
                    priority,
                    configurable,
                    final_binding,
                )?;
            }
            Ok(())
        }
        _ => Err("di_bind/bindings must be a table or array".to_string()),
    }
}

fn push_binding(
    profile: &mut DiProfile,
    service: &str,
    target: &str,
    scope: DiScope,
    priority: i64,
    configurable: bool,
    final_binding: bool,
) -> Result<(), String> {
    if configurable && final_binding {
        return Err(format!(
            "DI binding for '{}' cannot be both configurable and final",
            service
        ));
    }
    let raw_predicate = format!("type({})", service);
    let predicate = predicate_parser::parse_predicate(&raw_predicate)?;
    predicate
        .validate(PredicateContext::DependencyInjection)
        .map_err(|e| format!("invalid predicate for DI binding: {}", e))?;
    profile.bindings.push(DiBindingRule {
        predicate,
        impl_type: default_constructor_target(target),
        scope,
        priority,
        order: profile.bindings.len(),
        raw_predicate,
        configurable,
        final_binding,
        default_instance_class: if target.contains('.') {
            None
        } else {
            Some(target.to_string())
        },
    });
    Ok(())
}

fn sdn_table_field(fields: &[String], row: &[SdnValue], name: &str) -> Option<String> {
    fields
        .iter()
        .position(|field| field == name)
        .and_then(|idx| row.get(idx))
        .and_then(sdn_string)
}

fn sdn_string(value: &SdnValue) -> Option<String> {
    match value {
        SdnValue::String(s) => Some(s.clone()),
        SdnValue::Int(i) => Some(i.to_string()),
        SdnValue::Float(f) => Some(f.to_string()),
        SdnValue::Bool(b) => Some(b.to_string()),
        SdnValue::Null | SdnValue::Array(_) | SdnValue::Dict(_) | SdnValue::Table { .. } => None,
    }
}

fn parse_sdn_bool_text(value: &str, field: &str) -> Result<bool, String> {
    match value {
        "true" | "True" => Ok(true),
        "false" | "False" => Ok(false),
        _ => Err(format!("{} must be true or false", field)),
    }
}

pub fn validate_local_child_config_path(path: &str) -> Result<(), String> {
    if path.is_empty() {
        return Err("DI config load path cannot be empty".to_string());
    }
    if path.starts_with('/') || path.starts_with('\\') || path.starts_with('~') {
        return Err(format!("DI config load path '{}' must be relative", path));
    }
    if path.contains(':') {
        return Err(format!(
            "DI config load path '{}' must not contain a drive or scheme",
            path
        ));
    }
    for part in path.split(['/', '\\']) {
        if part == ".." {
            return Err(format!(
                "DI config load path '{}' cannot escape the current directory",
                path
            ));
        }
    }
    Ok(())
}

/// Runtime DI container for managing instances.
#[derive(Debug, Clone)]
pub struct DiContainer {
    /// Singleton instances (type name -> value)
    singletons: HashMap<String, crate::value::Value>,
    /// Runtime slot overrides keyed by `(slot type, optional qualifier)`.
    runtime_slot_overrides: HashMap<(String, Option<String>), String>,
    /// Configuration for bindings
    config: DiConfig,
    /// Active profile name
    active_profile: String,
}

impl DiContainer {
    /// Create a new DI container with the given configuration.
    pub fn new(config: DiConfig, active_profile: String) -> Self {
        Self {
            singletons: HashMap::new(),
            runtime_slot_overrides: HashMap::new(),
            config,
            active_profile,
        }
    }

    /// Register or replace a runtime slot implementation.
    pub fn set_runtime_slot(
        &mut self,
        type_name: impl Into<String>,
        qualifier: Option<String>,
        impl_type: impl Into<String>,
    ) {
        let impl_type = impl_type.into();
        self.runtime_slot_overrides
            .insert((type_name.into(), qualifier), default_constructor_target(&impl_type));
    }

    /// Resolve a dependency for the given type.
    ///
    /// Returns the implementation type name to instantiate.
    pub fn resolve_type(
        &self,
        type_name: &str,
        module_path: &str,
        attrs: &[String],
    ) -> Result<Option<(String, DiScope)>, DiResolveError> {
        let ctx = create_di_match_context(type_name, module_path, attrs);
        let binding = self.config.select_binding(&self.active_profile, &ctx)?;

        if let Some(binding) = binding {
            return Ok(Some((binding.impl_type.clone(), binding.scope)));
        }

        Ok(self.resolve_runtime_slot(type_name, None))
    }

    /// Resolve a runtime slot, honoring dynamic overrides before static defaults.
    pub fn resolve_runtime_slot(&self, type_name: &str, qualifier: Option<&str>) -> Option<(String, DiScope)> {
        let key = (type_name.to_string(), qualifier.map(|q| q.to_string()));
        if let Some(impl_type) = self.runtime_slot_overrides.get(&key) {
            return Some((impl_type.clone(), DiScope::Scoped));
        }

        if qualifier.is_some() {
            let unqualified_key = (type_name.to_string(), None);
            if let Some(impl_type) = self.runtime_slot_overrides.get(&unqualified_key) {
                return Some((impl_type.clone(), DiScope::Scoped));
            }
        }

        self.config
            .runtime_slots
            .iter()
            .find(|slot| {
                slot.type_name == type_name
                    && qualifier
                        .map(|q| slot.qualifier.as_deref() == Some(q))
                        .unwrap_or(slot.qualifier.is_none())
            })
            .or_else(|| {
                if qualifier.is_some() {
                    self.config
                        .runtime_slots
                        .iter()
                        .find(|slot| slot.type_name == type_name && slot.qualifier.is_none())
                } else {
                    None
                }
            })
            .and_then(|slot| slot.default_impl.as_deref())
            .map(|impl_type| (default_constructor_target(impl_type), DiScope::Scoped))
    }

    /// Get or create a singleton instance.
    ///
    /// For singleton scope, this manages the cached instance.
    /// For transient scope, this always returns None (caller creates new instance).
    pub fn get_or_create_singleton(
        &mut self,
        impl_type: &str,
        scope: DiScope,
        create_fn: impl FnOnce() -> crate::value::Value,
    ) -> crate::value::Value {
        match scope {
            DiScope::Singleton | DiScope::Static => self
                .singletons
                .entry(impl_type.to_string())
                .or_insert_with(create_fn)
                .clone(),
            DiScope::Transient
            | DiScope::Scoped
            | DiScope::Thread
            | DiScope::Task
            | DiScope::Arena
            | DiScope::Extern => create_fn(),
        }
    }

    /// Check if a type has a binding in the current profile.
    pub fn has_binding(&self, type_name: &str, module_path: &str, attrs: &[String]) -> bool {
        let ctx = create_di_match_context(type_name, module_path, attrs);
        self.config
            .select_binding(&self.active_profile, &ctx)
            .ok()
            .flatten()
            .is_some()
            || self.resolve_runtime_slot(type_name, None).is_some()
    }

    /// Get the active profile name.
    pub fn active_profile(&self) -> &str {
        &self.active_profile
    }
}

pub fn merge_di_config_with_hir_graphs(
    base: Option<DiConfig>,
    graphs: &[crate::hir::HirInjectGraph],
) -> Result<Option<DiConfig>, String> {
    let Some(source_config) = di_config_from_hir_inject_graphs(graphs)? else {
        return Ok(base.map(|mut config| {
            config.ensure_default_profile();
            config
        }));
    };
    let Some(base_config) = base else {
        return Ok(Some(source_config));
    };

    let mut merged = source_config;
    merged.conventions = base_config.conventions;
    if merged.graph.is_none() {
        merged.graph = base_config.graph.clone();
    }
    merged.roots.extend(base_config.roots.clone());
    merged.scans.extend(base_config.scans.clone());
    merged.loads.extend(base_config.loads.clone());
    merged.runtime_slots.extend(base_config.runtime_slots.clone());
    merged.concurrent_backend = base_config.concurrent_backend;

    for (profile_name, base_profile) in base_config.profiles {
        let profile = merged.profiles.entry(profile_name).or_default();
        for mut binding in base_profile.bindings {
            if let Some(source_binding) = find_overridden_source_binding(&profile.bindings, &binding) {
                if source_binding.final_binding || !source_binding.configurable {
                    return Err(format!(
                        "DI config cannot override final/non-configurable binding '{}' with '{}'",
                        source_binding.raw_predicate, binding.impl_type
                    ));
                }
                if binding.priority <= source_binding.priority {
                    binding.priority = source_binding.priority + 1;
                }
            }
            binding.order = profile.bindings.len();
            profile.bindings.push(binding);
        }
    }

    merged.ensure_default_profile();
    Ok(Some(merged))
}

fn find_overridden_source_binding<'a>(
    source_bindings: &'a [DiBindingRule],
    override_binding: &DiBindingRule,
) -> Option<&'a DiBindingRule> {
    let override_subject = binding_type_subject(&override_binding.raw_predicate)?;
    source_bindings
        .iter()
        .find(|binding| binding_type_subject(&binding.raw_predicate).as_deref() == Some(override_subject.as_str()))
}

fn binding_type_subject(raw_predicate: &str) -> Option<String> {
    let mut text = raw_predicate.trim();
    if text.starts_with("pc{") && text.ends_with('}') {
        text = text[3..text.len() - 1].trim();
    }
    let inner = text.strip_prefix("type(")?.strip_suffix(')')?;
    Some(inner.trim().to_string())
}

pub fn di_config_from_hir_inject_graphs(graphs: &[crate::hir::HirInjectGraph]) -> Result<Option<DiConfig>, String> {
    if graphs.is_empty() {
        return Ok(None);
    }

    let mut profiles: HashMap<String, DiProfile> = HashMap::new();
    let mut graph_name = None;
    let mut mode = DiMode::Mixed;
    let conventions = DiConventionConfig::default();
    let mut roots = Vec::new();
    let mut scans = Vec::new();
    let mut loads = Vec::new();
    let mut runtime_slots = Vec::new();

    for graph in graphs {
        if graph_name.is_none() {
            graph_name = Some(graph.name.clone());
        }
        if let Some(graph_mode) = graph.mode.as_deref() {
            mode = parse_graph_mode(graph_mode)?;
        }
        collect_inject_items(
            &graph.items,
            "default",
            &mut profiles,
            &mut roots,
            &mut scans,
            &mut loads,
            &mut runtime_slots,
        )?;
    }

    let mut config = DiConfig {
        mode,
        conventions,
        graph: graph_name,
        roots,
        scans,
        loads,
        runtime_slots,
        profiles,
        concurrent_backend: Default::default(),
    };
    config.ensure_default_profile();
    Ok(Some(config))
}

fn collect_inject_items(
    items: &[crate::hir::HirInjectItem],
    profile_name: &str,
    profiles: &mut HashMap<String, DiProfile>,
    roots: &mut Vec<String>,
    scans: &mut Vec<String>,
    loads: &mut Vec<String>,
    runtime_slots: &mut Vec<DiRuntimeSlot>,
) -> Result<(), String> {
    for item in items {
        match item {
            crate::hir::HirInjectItem::Root { type_ref } => roots.push(type_ref.clone()),
            crate::hir::HirInjectItem::Scan { pattern } => scans.push(pattern.clone()),
            crate::hir::HirInjectItem::Load { path } => {
                validate_local_child_config_path(path)?;
                loads.push(path.clone());
            }
            crate::hir::HirInjectItem::Bind {
                service,
                target,
                lifetime,
                configurable,
                final_binding,
            } => {
                if *configurable && *final_binding {
                    return Err(format!(
                        "DI binding for '{}' cannot be both configurable and final",
                        service
                    ));
                }
                let profile = profiles.entry(profile_name.to_string()).or_default();
                let raw_predicate = format!("type({})", service);
                let predicate = predicate_parser::parse_predicate(&raw_predicate)?;
                predicate
                    .validate(PredicateContext::DependencyInjection)
                    .map_err(|e| format!("invalid predicate for source DI binding: {}", e))?;
                profile.bindings.push(DiBindingRule {
                    predicate,
                    impl_type: default_constructor_target(target),
                    scope: lifetime
                        .as_deref()
                        .map(parse_graph_scope)
                        .transpose()?
                        .unwrap_or(DiScope::Transient),
                    priority: 0,
                    order: profile.bindings.len(),
                    raw_predicate,
                    configurable: *configurable,
                    final_binding: *final_binding,
                    default_instance_class: Some(target.clone()),
                });
            }
            crate::hir::HirInjectItem::Slot {
                service,
                qualifier,
                default_target,
            } => runtime_slots.push(DiRuntimeSlot {
                type_name: service.clone(),
                qualifier: qualifier.clone(),
                default_impl: default_target.clone(),
            }),
            crate::hir::HirInjectItem::Profile { name, items } => {
                collect_inject_items(items, name, profiles, roots, scans, loads, runtime_slots)?;
            }
        }
    }
    Ok(())
}

fn default_constructor_target(target: &str) -> String {
    if target.contains('.') {
        target.to_string()
    } else {
        format!("{}.new", target)
    }
}

fn parse_graph_mode(mode: &str) -> Result<DiMode, String> {
    match mode {
        "compile" => Ok(DiMode::Compile),
        "runtime" => Ok(DiMode::Runtime),
        "mixed" => Ok(DiMode::Mixed),
        "hybrid" => Ok(DiMode::Hybrid),
        "manual" => Ok(DiMode::Manual),
        _ => Err(format!("unknown inject graph mode '{}'", mode)),
    }
}

fn parse_graph_scope(scope: &str) -> Result<DiScope, String> {
    match scope {
        "singleton" => Ok(DiScope::Singleton),
        "transient" => Ok(DiScope::Transient),
        "scoped" | "request" => Ok(DiScope::Scoped),
        "thread" => Ok(DiScope::Thread),
        "task" => Ok(DiScope::Task),
        "arena" => Ok(DiScope::Arena),
        "static" => Ok(DiScope::Static),
        "extern" => Ok(DiScope::Extern),
        _ => Err(format!("unknown inject lifetime '{}'", scope)),
    }
}

/// Typed dependency graph for compile-time analysis.
#[derive(Debug, Clone, Default)]
pub struct DependencyGraph {
    /// Map of type name -> dependencies (parameter types)
    dependencies: HashMap<String, Vec<String>>,
    /// Map of type name -> implementations
    implementations: HashMap<String, Vec<String>>,
}

impl DependencyGraph {
    /// Add a dependency edge: `from_type` depends on `param_type`.
    pub fn add_dependency(&mut self, from_type: String, param_type: String) {
        self.dependencies.entry(from_type).or_default().push(param_type);
    }

    /// Add an implementation: `impl_type` implements `trait_type`.
    pub fn add_implementation(&mut self, trait_type: String, impl_type: String) {
        self.implementations.entry(trait_type).or_default().push(impl_type);
    }

    /// Get dependencies for a type.
    pub fn get_dependencies(&self, type_name: &str) -> Option<&[String]> {
        self.dependencies.get(type_name).map(|v| v.as_slice())
    }

    /// Get implementations for a trait/type.
    pub fn get_implementations(&self, trait_name: &str) -> Option<&[String]> {
        self.implementations.get(trait_name).map(|v| v.as_slice())
    }

    pub fn resolve_single_visible_implementation(&self, trait_name: &str) -> Result<Option<String>, Vec<String>> {
        let Some(impls) = self.implementations.get(trait_name) else {
            return Ok(None);
        };
        match impls.as_slice() {
            [] => Ok(None),
            [only] => Ok(Some(only.clone())),
            many => Err(many.to_vec()),
        }
    }

    /// Check for circular dependencies using DFS.
    pub fn check_circular(&self, start_type: &str) -> Option<Vec<String>> {
        let mut visited = HashMap::new();
        let mut path = Vec::new();
        self.dfs_check(start_type, &mut visited, &mut path)
    }

    fn dfs_check(
        &self,
        current: &str,
        visited: &mut HashMap<String, bool>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        // If we've seen this node in the current path, we have a cycle
        if path.contains(&current.to_string()) {
            path.push(current.to_string());
            return Some(path.clone());
        }

        // If we've already fully explored this node, skip it
        if visited.get(current) == Some(&true) {
            return None;
        }

        path.push(current.to_string());

        if let Some(deps) = self.dependencies.get(current) {
            for dep in deps {
                if let Some(cycle) = self.dfs_check(dep, visited, path) {
                    return Some(cycle);
                }
            }
        }

        path.pop();
        visited.insert(current.to_string(), true);
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_predicate_basic() {
        let pred = predicate_parser::parse_predicate("pc{ type(Foo) & !attr(test) }").unwrap();
        let attrs = vec!["release".to_string()];
        let ctx = create_di_match_context("Foo", "app.core", &attrs);
        assert!(pred.matches(&ctx));
    }

    #[test]
    fn parse_di_config_basic() {
        let toml: toml::Value = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
  { on = "pc{ type(Foo) }", impl = "Bar", scope = "Singleton", priority = 10 }
]
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        assert_eq!(config.mode, DiMode::Hybrid);
        assert!(config.loads.is_empty());
        let profile = config.profiles.get("default").unwrap();
        assert_eq!(profile.bindings.len(), 1);
        assert_eq!(profile.bindings[0].impl_type, "Bar");
        assert_eq!(profile.bindings[0].priority, 10);
        assert_eq!(profile.bindings[0].scope, DiScope::Singleton);
        assert!(!profile.bindings[0].configurable);
        assert_eq!(config.conventions, DiConventionConfig::default());
    }

    #[test]
    fn parse_di_config_convention_toggles() {
        let toml: toml::Value = r#"
[di]
conventions = { self_binding = false, single_visible_impl = true, naming_fallback = false, folder_fallback = false, std_defaults = true }
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        assert!(!config.conventions.self_binding);
        assert!(config.conventions.single_visible_impl);
        assert!(!config.conventions.naming_fallback);
        assert!(!config.conventions.folder_fallback);
        assert!(config.conventions.std_defaults);
        assert!(config.profiles.contains_key("default"));
    }

    #[test]
    fn parse_graph_first_di_config() {
        let toml: toml::Value = r#"
[di]
mode = "mixed"
graph = "AppGraph"
root = "App"
scan = ["app.*", "infra.*"]
load = ["config/di.sdn", "./profiles/dev.sdn"]
runtime_slots = [
  { type = "PaymentProvider", default = "StripePaymentProvider", named = "payments" }
]

[di.profiles.dev]
bindings = [
  { on = "pc{ type(UserRepo) }", impl = "SqlUserRepo", scope = "scoped", configurable = true, default = "SqlUserRepo" },
  { on = "pc{ type(CryptoRng) }", impl = "SystemCryptoRng", scope = "singleton", final = true }
]
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        assert_eq!(config.mode, DiMode::Mixed);
        assert_eq!(config.graph.as_deref(), Some("AppGraph"));
        assert_eq!(config.roots, vec!["App"]);
        assert_eq!(config.scans, vec!["app.*", "infra.*"]);
        assert_eq!(config.loads.len(), 2);
        assert_eq!(config.runtime_slots[0].type_name, "PaymentProvider");
        assert_eq!(
            config.runtime_slots[0].default_impl.as_deref(),
            Some("StripePaymentProvider")
        );

        let profile = config.profiles.get("dev").unwrap();
        assert_eq!(profile.bindings[0].scope, DiScope::Scoped);
        assert!(profile.bindings[0].configurable);
        assert_eq!(
            profile.bindings[0].default_instance_class.as_deref(),
            Some("SqlUserRepo")
        );
        assert!(profile.bindings[1].final_binding);
    }

    #[test]
    fn reject_di_load_paths_outside_current_tree() {
        for path in [
            "/tmp/di.sdn",
            "../di.sdn",
            "config/../secret.sdn",
            "C:\\temp\\di.sdn",
            "https://x/di.sdn",
        ] {
            assert!(
                validate_local_child_config_path(path).is_err(),
                "path should be rejected: {}",
                path
            );
        }
        assert!(validate_local_child_config_path("config/di.sdn").is_ok());
        assert!(validate_local_child_config_path("./config/di.sdn").is_ok());
    }

    #[test]
    fn configurable_final_bindings_are_invalid() {
        let toml: toml::Value = r#"
[di]

[di.profiles.dev]
bindings = [
  { on = "pc{ type(CryptoRng) }", impl = "SystemCryptoRng", configurable = true, final = true }
]
"#
        .parse()
        .unwrap();

        let err = parse_di_config(&toml).unwrap_err();
        assert!(err.contains("cannot be both configurable and final"));
    }

    #[test]
    fn match_pattern_segments() {
        use crate::predicate::match_pattern;
        assert!(match_pattern("app.**", "app.core.user"));
        assert!(match_pattern("app.*.user", "app.core.user"));
        assert!(!match_pattern("app.*.user", "app.core.auth.user"));
        assert!(match_pattern("app.service*", "app.service_v2"));
    }

    #[test]
    fn di_container_resolve_type() {
        let toml: toml::Value = r#"
[di]
mode = "hybrid"

[di.profiles.test]
bindings = [
  { on = "pc{ type(UserRepository) }", impl = "MockUserRepository", scope = "Singleton", priority = 10 }
]
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        let container = DiContainer::new(config, "test".to_string());

        let result = container.resolve_type("UserRepository", "app.domain", &[]).unwrap();

        assert!(result.is_some());
        let (impl_type, scope) = result.unwrap();
        assert_eq!(impl_type, "MockUserRepository");
        assert_eq!(scope, DiScope::Singleton);
    }

    #[test]
    fn di_container_no_binding() {
        let toml: toml::Value = r#"
[di]
mode = "hybrid"

[di.profiles.test]
bindings = []
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        let container = DiContainer::new(config, "test".to_string());

        let result = container.resolve_type("UserRepository", "app.domain", &[]).unwrap();

        assert!(result.is_none());
    }

    #[test]
    fn di_container_resolves_runtime_slot_default() {
        let toml: toml::Value = r#"
[di]
mode = "runtime"
runtime_slots = [
  { type = "PaymentProvider", default = "StripePaymentProvider", named = "payments" }
]
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        let container = DiContainer::new(config, "default".to_string());

        assert_eq!(
            container.resolve_runtime_slot("PaymentProvider", Some("payments")),
            Some(("StripePaymentProvider.new".to_string(), DiScope::Scoped))
        );
        assert_eq!(container.resolve_type("PaymentProvider", "app", &[]).unwrap(), None);
    }

    #[test]
    fn di_container_runtime_slot_override_wins_over_default() {
        let toml: toml::Value = r#"
[di]
mode = "runtime"
runtime_slots = [
  { type = "PaymentProvider", default = "StripePaymentProvider" }
]
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        let mut container = DiContainer::new(config, "default".to_string());
        container.set_runtime_slot("PaymentProvider", None, "SandboxPaymentProvider");

        assert_eq!(
            container.resolve_type("PaymentProvider", "app", &[]).unwrap(),
            Some(("SandboxPaymentProvider.new".to_string(), DiScope::Scoped))
        );
    }

    #[test]
    fn dependency_graph_circular_detection() {
        let mut graph = DependencyGraph::default();

        // Create a circular dependency: A -> B -> C -> A
        graph.add_dependency("A".to_string(), "B".to_string());
        graph.add_dependency("B".to_string(), "C".to_string());
        graph.add_dependency("C".to_string(), "A".to_string());

        let cycle = graph.check_circular("A");
        assert!(cycle.is_some());
        let cycle_path = cycle.unwrap();
        assert!(cycle_path.contains(&"A".to_string()));
        assert!(cycle_path.contains(&"B".to_string()));
        assert!(cycle_path.contains(&"C".to_string()));
    }

    #[test]
    fn dependency_graph_no_circular() {
        let mut graph = DependencyGraph::default();

        // Create a non-circular dependency: A -> B -> C
        graph.add_dependency("A".to_string(), "B".to_string());
        graph.add_dependency("B".to_string(), "C".to_string());

        let cycle = graph.check_circular("A");
        assert!(cycle.is_none());
    }

    #[test]
    fn dependency_graph_get_deps() {
        let mut graph = DependencyGraph::default();

        graph.add_dependency("OrderService".to_string(), "OrderRepository".to_string());
        graph.add_dependency("OrderService".to_string(), "Clock".to_string());

        let deps = graph.get_dependencies("OrderService").unwrap();
        assert_eq!(deps.len(), 2);
        assert!(deps.contains(&"OrderRepository".to_string()));
        assert!(deps.contains(&"Clock".to_string()));
    }

    #[test]
    fn dependency_graph_implementations() {
        let mut graph = DependencyGraph::default();

        graph.add_implementation("UserRepository".to_string(), "SqlUserRepository".to_string());
        graph.add_implementation("UserRepository".to_string(), "MockUserRepository".to_string());

        let impls = graph.get_implementations("UserRepository").unwrap();
        assert_eq!(impls.len(), 2);
        assert!(impls.contains(&"SqlUserRepository".to_string()));
        assert!(impls.contains(&"MockUserRepository".to_string()));
    }

    #[test]
    fn dependency_graph_single_implementation_convention() {
        let mut graph = DependencyGraph::default();
        graph.add_implementation("Clock".to_string(), "SystemClock".to_string());
        assert_eq!(
            graph.resolve_single_visible_implementation("Clock").unwrap(),
            Some("SystemClock".to_string())
        );

        graph.add_implementation("Clock".to_string(), "FakeClock".to_string());
        let err = graph.resolve_single_visible_implementation("Clock").unwrap_err();
        assert_eq!(err, vec!["SystemClock".to_string(), "FakeClock".to_string()]);
    }
}
