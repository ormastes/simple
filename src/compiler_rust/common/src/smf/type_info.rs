//! Bounded, versioned metadata carried by the SMF `TypeInfo` section.

use serde::{Deserialize, Serialize};
use std::collections::HashSet;

pub const SMF_TYPE_INFO_VERSION: u32 = 1;
pub const MAX_TYPE_INFO_PAYLOAD_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_TYPE_INFO_RECORDS: usize = 65_536;
pub const MAX_TYPE_INFO_FIELDS: usize = 4_096;
pub const MAX_TYPE_INFO_NAME_BYTES: usize = 4_096;
const MAX_TYPE_REF_DEPTH: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SmfTypeInfo {
    pub version: u32,
    pub types: Vec<SmfNamedType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SmfNamedType {
    pub name: String,
    pub is_public: bool,
    pub kind: SmfTypeKind,
    pub fields: Vec<SmfFieldType>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SmfTypeKind {
    Struct,
    Class,
    Enum,
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SmfFieldType {
    pub name: String,
    pub type_ref: SmfTypeRef,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SmfTypeRef {
    Primitive(String),
    Named(String),
    Array { element: Box<Self>, size: Option<usize> },
    Tuple(Vec<Self>),
    LabeledTuple(Vec<(String, Self)>),
    Dict { key: Box<Self>, value: Box<Self> },
    Pointer { inner: Box<Self>, kind: String, capability: Option<String> },
    Simd { lanes: u32, element: Box<Self> },
    Function { params: Vec<Self>, ret: Box<Self> },
    Union(Vec<Self>),
    Promise(Box<Self>),
    Unit { name: String, repr: String, bits: u16, signed: bool, is_float: bool },
    Unknown,
}

impl SmfTypeInfo {
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        let bytes = serde_json::to_vec(self)
            .map_err(|error| format!("SMF type info serialization failed: {error}"))?;
        if bytes.len() > MAX_TYPE_INFO_PAYLOAD_BYTES {
            return Err("SMF type info payload exceeds 16 MiB".to_string());
        }
        Ok(bytes)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > MAX_TYPE_INFO_PAYLOAD_BYTES {
            return Err("SMF type info payload exceeds 16 MiB".to_string());
        }
        let info: Self = serde_json::from_slice(bytes)
            .map_err(|error| format!("invalid SMF type info payload: {error}"))?;
        info.validate()?;
        Ok(info)
    }

    fn validate(&self) -> Result<(), String> {
        if self.version != SMF_TYPE_INFO_VERSION {
            return Err(format!("unsupported SMF type info version {}", self.version));
        }
        if self.types.len() > MAX_TYPE_INFO_RECORDS {
            return Err("SMF type info has too many named types".to_string());
        }

        let mut type_names = HashSet::with_capacity(self.types.len());
        for named in &self.types {
            validate_name(&named.name, "type")?;
            if !type_names.insert(named.name.as_str()) {
                return Err(format!("duplicate SMF type name {}", named.name));
            }
            if named.fields.len() > MAX_TYPE_INFO_FIELDS {
                return Err(format!("SMF type {} has too many fields", named.name));
            }
            let mut field_names = HashSet::with_capacity(named.fields.len());
            for field in &named.fields {
                validate_name(&field.name, "field")?;
                if !field_names.insert(field.name.as_str()) {
                    return Err(format!("duplicate SMF field {}.{}", named.name, field.name));
                }
                validate_type_ref(&field.type_ref, 0)?;
            }
        }
        Ok(())
    }
}

fn validate_name(name: &str, kind: &str) -> Result<(), String> {
    if name.is_empty() || name.len() > MAX_TYPE_INFO_NAME_BYTES {
        return Err(format!("invalid SMF {kind} name length"));
    }
    Ok(())
}

fn validate_type_ref(type_ref: &SmfTypeRef, depth: usize) -> Result<(), String> {
    if depth >= MAX_TYPE_REF_DEPTH {
        return Err("SMF type reference nesting is too deep".to_string());
    }
    match type_ref {
        SmfTypeRef::Primitive(name) | SmfTypeRef::Named(name) => validate_name(name, "type reference"),
        SmfTypeRef::Array { element, .. } | SmfTypeRef::Promise(element) => {
            validate_type_ref(element, depth + 1)
        }
        SmfTypeRef::Pointer { inner, kind, capability } => {
            validate_name(kind, "pointer kind")?;
            if let Some(capability) = capability {
                validate_name(capability, "pointer capability")?;
            }
            validate_type_ref(inner, depth + 1)
        }
        SmfTypeRef::Tuple(items) | SmfTypeRef::Union(items) => {
            validate_type_refs(items, depth + 1)
        }
        SmfTypeRef::LabeledTuple(items) => {
            if items.len() > MAX_TYPE_INFO_FIELDS {
                return Err("SMF labeled tuple has too many fields".to_string());
            }
            let mut labels = HashSet::with_capacity(items.len());
            for (label, item) in items {
                validate_name(label, "tuple label")?;
                if !labels.insert(label.as_str()) {
                    return Err(format!("duplicate SMF tuple label {label}"));
                }
                validate_type_ref(item, depth + 1)?;
            }
            Ok(())
        }
        SmfTypeRef::Dict { key, value } => {
            validate_type_ref(key, depth + 1)?;
            validate_type_ref(value, depth + 1)
        }
        SmfTypeRef::Simd { lanes, element } => {
            if *lanes == 0 {
                return Err("SMF SIMD lane count must be nonzero".to_string());
            }
            validate_type_ref(element, depth + 1)
        }
        SmfTypeRef::Function { params, ret } => {
            validate_type_refs(params, depth + 1)?;
            validate_type_ref(ret, depth + 1)
        }
        SmfTypeRef::Unit { name, repr, bits, .. } => {
            validate_name(name, "unit type")?;
            validate_name(repr, "unit representation")?;
            if *bits == 0 {
                return Err("SMF unit bit width must be nonzero".to_string());
            }
            Ok(())
        }
        SmfTypeRef::Unknown => Ok(()),
    }
}

fn validate_type_refs(items: &[SmfTypeRef], depth: usize) -> Result<(), String> {
    if items.len() > MAX_TYPE_INFO_FIELDS {
        return Err("SMF type reference list is too large".to_string());
    }
    for item in items {
        validate_type_ref(item, depth)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> SmfTypeInfo {
        SmfTypeInfo {
            version: SMF_TYPE_INFO_VERSION,
            types: vec![SmfNamedType {
                name: "Packet".to_string(),
                is_public: true,
                kind: SmfTypeKind::Struct,
                fields: vec![SmfFieldType {
                    name: "payload".to_string(),
                    type_ref: SmfTypeRef::Array {
                        element: Box::new(SmfTypeRef::Primitive("u8".to_string())),
                        size: None,
                    },
                }],
            }],
        }
    }

    #[test]
    fn round_trips_deterministically() {
        let info = sample();
        let first = info.to_bytes().unwrap();
        assert_eq!(first, info.to_bytes().unwrap());
        assert_eq!(SmfTypeInfo::from_bytes(&first).unwrap(), info);
    }

    #[test]
    fn rejects_unknown_version_and_malformed_json() {
        let mut info = sample();
        info.version = SMF_TYPE_INFO_VERSION + 1;
        assert!(info.to_bytes().is_err());
        assert!(SmfTypeInfo::from_bytes(br#"{"version":99,"types":[]}"#).is_err());
        assert!(SmfTypeInfo::from_bytes(b"not json").is_err());
    }

    #[test]
    fn rejects_duplicate_and_invalid_type_data() {
        let mut info = sample();
        info.types.push(info.types[0].clone());
        assert!(info.to_bytes().is_err());
        let bytes = br#"{"version":1,"types":[{"name":"X","is_public":false,"kind":"Class","fields":[{"name":"x","type_ref":{"Simd":{"lanes":0,"element":{"Primitive":"u8"}}}}]}]}"#;
        assert!(SmfTypeInfo::from_bytes(bytes).is_err());
    }
}
