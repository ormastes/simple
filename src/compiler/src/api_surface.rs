//! API Surface Lock File Generator (#914)
//!
//! Generates a manifest of all public types, functions, and signatures.
//! This prevents accidental API changes and makes diffs reviewable.

use serde::{Deserialize, Serialize};
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef, Node, Parameter, StructDef, TraitDef, Type, Visibility};
use std::collections::BTreeMap;

/// Public API surface of a module
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiSurface {
    /// Module name
    pub module: String,
    /// Public functions
    pub functions: BTreeMap<String, FunctionSignature>,
    /// Public structs
    pub structs: BTreeMap<String, StructSignature>,
    /// Public classes
    pub classes: BTreeMap<String, ClassSignature>,
    /// Public enums
    pub enums: BTreeMap<String, EnumSignature>,
    /// Public traits
    pub traits: BTreeMap<String, TraitSignature>,
}

/// Function signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSignature {
    /// Function name
    pub name: String,
    /// Parameter types
    pub params: Vec<ParamSignature>,
    /// Return type
    pub return_type: Option<String>,
    /// Is async?
    pub is_async: bool,
    /// Is generator?
    pub is_generator: bool,
}

/// Parameter signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParamSignature {
    pub name: String,
    pub type_name: Option<String>,
}

/// Struct signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructSignature {
    pub name: String,
    pub fields: Vec<FieldSignature>,
}

/// Field signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldSignature {
    pub name: String,
    pub type_name: Option<String>,
    pub is_public: bool,
}

/// Class signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClassSignature {
    pub name: String,
    pub fields: Vec<FieldSignature>,
    pub methods: Vec<String>,
}

/// Enum signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnumSignature {
    pub name: String,
    pub variants: Vec<String>,
}

/// Trait signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitSignature {
    pub name: String,
    pub methods: Vec<String>,
}

impl ApiSurface {
    pub fn new(module: impl Into<String>) -> Self {
        Self {
            module: module.into(),
            functions: BTreeMap::new(),
            structs: BTreeMap::new(),
            classes: BTreeMap::new(),
            enums: BTreeMap::new(),
            traits: BTreeMap::new(),
        }
    }

    /// Extract API surface from AST nodes
    pub fn from_nodes(module: impl Into<String>, nodes: &[Node]) -> Self {
        let mut surface = Self::new(module);

        for node in nodes {
            match node {
                Node::Function(func) if func.visibility.is_public() => {
                    surface.add_function(func);
                }
                Node::Struct(s) if s.visibility.is_public() => {
                    surface.add_struct(s);
                }
                Node::Class(c) if c.visibility.is_public() => {
                    surface.add_class(c);
                }
                Node::Enum(e) if e.visibility.is_public() => {
                    surface.add_enum(e);
                }
                Node::Trait(t) if t.visibility.is_public() => {
                    surface.add_trait(t);
                }
                _ => {}
            }
        }

        surface
    }

    fn add_function(&mut self, func: &FunctionDef) {
        let is_async = func
            .effects
            .iter()
            .any(|e| matches!(e, simple_parser::ast::Effect::Async));

        let sig = FunctionSignature {
            name: func.name.clone(),
            params: func
                .params
                .iter()
                .map(|p| ParamSignature {
                    name: p.name.clone(),
                    type_name: p.ty.as_ref().map(|t| type_to_string(t)),
                })
                .collect(),
            return_type: func.return_type.as_ref().map(|t| type_to_string(t)),
            is_async,
            is_generator: false, // Generator detection would need more analysis
        };
        self.functions.insert(func.name.clone(), sig);
    }

    fn add_struct(&mut self, s: &StructDef) {
        let sig = StructSignature {
            name: s.name.clone(),
            fields: s
                .fields
                .iter()
                .map(|f| FieldSignature {
                    name: f.name.clone(),
                    type_name: Some(type_to_string(&f.ty)),
                    is_public: f.visibility.is_public(),
                })
                .collect(),
        };
        self.structs.insert(s.name.clone(), sig);
    }

    fn add_class(&mut self, c: &ClassDef) {
        let sig = ClassSignature {
            name: c.name.clone(),
            fields: c
                .fields
                .iter()
                .map(|f| FieldSignature {
                    name: f.name.clone(),
                    type_name: Some(type_to_string(&f.ty)),
                    is_public: f.visibility.is_public(),
                })
                .collect(),
            methods: c.methods.iter().map(|m| m.name.clone()).collect(),
        };
        self.classes.insert(c.name.clone(), sig);
    }

    fn add_enum(&mut self, e: &EnumDef) {
        let sig = EnumSignature {
            name: e.name.clone(),
            variants: e.variants.iter().map(|v| v.name.clone()).collect(),
        };
        self.enums.insert(e.name.clone(), sig);
    }

    fn add_trait(&mut self, t: &TraitDef) {
        let sig = TraitSignature {
            name: t.name.clone(),
            methods: t.methods.iter().map(|m| m.name.clone()).collect(),
        };
        self.traits.insert(t.name.clone(), sig);
    }

    /// Export as JSON
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Export as compact JSON
    pub fn to_json_compact(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Export as YAML (human-readable lock file)
    pub fn to_yaml(&self) -> String {
        let mut yaml = format!("# API Surface Lock File\n# Module: {}\n\n", self.module);

        if !self.functions.is_empty() {
            yaml.push_str("functions:\n");
            for (name, sig) in &self.functions {
                yaml.push_str(&format!("  - name: {}\n", name));
                if !sig.params.is_empty() {
                    yaml.push_str("    params:\n");
                    for param in &sig.params {
                        yaml.push_str(&format!(
                            "      - {}: {}\n",
                            param.name,
                            param.type_name.as_deref().unwrap_or("any")
                        ));
                    }
                }
                if let Some(ret) = &sig.return_type {
                    yaml.push_str(&format!("    returns: {}\n", ret));
                }
                if sig.is_async {
                    yaml.push_str("    async: true\n");
                }
            }
            yaml.push('\n');
        }

        if !self.structs.is_empty() {
            yaml.push_str("structs:\n");
            for (name, sig) in &self.structs {
                yaml.push_str(&format!("  - name: {}\n", name));
                if !sig.fields.is_empty() {
                    yaml.push_str("    fields:\n");
                    for field in &sig.fields {
                        if field.is_public {
                            yaml.push_str(&format!(
                                "      - {}: {}\n",
                                field.name,
                                field.type_name.as_deref().unwrap_or("any")
                            ));
                        }
                    }
                }
            }
            yaml.push('\n');
        }

        if !self.enums.is_empty() {
            yaml.push_str("enums:\n");
            for (name, sig) in &self.enums {
                yaml.push_str(&format!("  - name: {}\n", name));
                yaml.push_str("    variants:\n");
                for variant in &sig.variants {
                    yaml.push_str(&format!("      - {}\n", variant));
                }
            }
            yaml.push('\n');
        }

        yaml
    }

    /// Compare with another API surface to detect changes
    pub fn diff(&self, other: &ApiSurface) -> ApiDiff {
        let mut diff = ApiDiff::new();

        // Check for removed/modified functions
        for (name, sig) in &self.functions {
            match other.functions.get(name) {
                None => diff.removed_functions.push(name.clone()),
                Some(other_sig)
                    if sig.params.len() != other_sig.params.len() || sig.return_type != other_sig.return_type =>
                {
                    diff.modified_functions.push(name.clone())
                }
                _ => {}
            }
        }

        // Check for added functions
        for name in other.functions.keys() {
            if !self.functions.contains_key(name) {
                diff.added_functions.push(name.clone());
            }
        }

        // Similar checks for other types
        for name in self.structs.keys() {
            if !other.structs.contains_key(name) {
                diff.removed_structs.push(name.clone());
            }
        }
        for name in other.structs.keys() {
            if !self.structs.contains_key(name) {
                diff.added_structs.push(name.clone());
            }
        }

        diff
    }
}

/// Differences between two API surfaces
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct ApiDiff {
    pub added_functions: Vec<String>,
    pub removed_functions: Vec<String>,
    pub modified_functions: Vec<String>,
    pub added_structs: Vec<String>,
    pub removed_structs: Vec<String>,
}

impl ApiDiff {
    fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.added_functions.is_empty()
            && self.removed_functions.is_empty()
            && self.modified_functions.is_empty()
            && self.added_structs.is_empty()
            && self.removed_structs.is_empty()
    }

    pub fn has_breaking_changes(&self) -> bool {
        !self.removed_functions.is_empty() || !self.modified_functions.is_empty() || !self.removed_structs.is_empty()
    }
}

fn type_to_string(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Array { element, .. } => format!("[{}]", type_to_string(element)),
        Type::Optional(inner) => format!("Option[{}]", type_to_string(inner)),
        Type::Generic { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!(
                    "{}[{}]",
                    name,
                    args.iter().map(type_to_string).collect::<Vec<_>>().join(", ")
                )
            }
        }
        Type::Tuple(types) => format!("({})", types.iter().map(type_to_string).collect::<Vec<_>>().join(", ")),
        Type::Function { params, ret } => format!(
            "({}) -> {}",
            params.iter().map(type_to_string).collect::<Vec<_>>().join(", "),
            ret.as_ref()
                .map(|r| type_to_string(r))
                .unwrap_or_else(|| "void".to_string())
        ),
        Type::Pointer { inner, .. } => format!("*{}", type_to_string(inner)),
        Type::Union(types) => types.iter().map(type_to_string).collect::<Vec<_>>().join(" | "),
        Type::DynTrait(name) => format!("dyn {}", name),
        Type::Capability { inner, .. } => type_to_string(inner),
        _ => "unknown".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    fn parse_code(code: &str) -> Vec<Node> {
        let mut parser = Parser::new(code);
        let module = parser.parse().expect("parse failed");
        module.items
    }

    #[test]
    fn test_extract_public_function() {
        let code = r#"
pub fn calculate(x: i64, y: i64) -> i64:
    return x + y

fn internal():
    pass
"#;
        let nodes = parse_code(code);
        let surface = ApiSurface::from_nodes("test", &nodes);

        assert_eq!(surface.functions.len(), 1);
        assert!(surface.functions.contains_key("calculate"));

        let calc = &surface.functions["calculate"];
        assert_eq!(calc.params.len(), 2);
        assert_eq!(calc.return_type, Some("i64".to_string()));
    }

    #[test]
    fn test_extract_public_struct() {
        let code = r#"
pub struct User:
    pub name: str
    pub age: i64
    internal_id: i64
"#;
        let nodes = parse_code(code);
        let surface = ApiSurface::from_nodes("test", &nodes);

        assert_eq!(surface.structs.len(), 1);
        assert!(surface.structs.contains_key("User"));

        let user = &surface.structs["User"];
        assert_eq!(user.fields.len(), 3);
    }

    #[test]
    fn test_json_export() {
        let code = r#"
pub fn greet(name: str) -> str:
    return "Hello"

pub struct Point:
    pub x: i64
    pub y: i64
"#;
        let nodes = parse_code(code);
        let surface = ApiSurface::from_nodes("test", &nodes);

        let json = surface.to_json().unwrap();
        let parsed: ApiSurface = serde_json::from_str(&json).unwrap();

        assert_eq!(parsed.functions.len(), 1);
        assert_eq!(parsed.structs.len(), 1);
    }

    #[test]
    fn test_api_diff() {
        let code1 = r#"
pub fn foo() -> i64:
    return 42

pub fn bar() -> str:
    return "hello"
"#;
        let code2 = r#"
pub fn foo() -> i64:
    return 42

pub fn baz() -> i64:
    return 100
"#;
        let nodes1 = parse_code(code1);
        let nodes2 = parse_code(code2);
        let surface1 = ApiSurface::from_nodes("test", &nodes1);
        let surface2 = ApiSurface::from_nodes("test", &nodes2);

        let diff = surface1.diff(&surface2);

        assert_eq!(diff.removed_functions, vec!["bar"]);
        assert_eq!(diff.added_functions, vec!["baz"]);
        assert!(diff.has_breaking_changes());
    }

    #[test]
    fn test_yaml_export() {
        let code = r#"
pub fn test() -> i64:
    return 0
"#;
        let nodes = parse_code(code);
        let surface = ApiSurface::from_nodes("test", &nodes);

        let yaml = surface.to_yaml();
        assert!(yaml.contains("functions:"));
        assert!(yaml.contains("name: test"));
    }
}
