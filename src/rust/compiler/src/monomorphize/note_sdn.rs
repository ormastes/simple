//! note.sdn section for SMF files - Instantiation metadata tracking.
//!
//! This module defines data structures and serialization for the note.sdn section,
//! which tracks generic instantiation relationships ("to/from") to enable:
//! - Lazy instantiation at link-time
//! - JIT instantiation at load-time
//! - Circular dependency detection
//! - Hot-reload updates
//!
//! The note.sdn section uses a zero-size trick: the section table entry shows size=0,
//! but the actual data is terminated with `\n# END_NOTE\n`. This allows hot-reload
//! updates without modifying the section table.

use std::collections::HashMap;

use super::types::ConcreteType;

/// Complete note.sdn metadata for an SMF file.
///
/// Tracks all instantiations (compiled), possible future instantiations,
/// type inferences, dependency graph, and circular dependency warnings/errors.
#[derive(Debug, Clone, Default)]
pub struct NoteSdnMetadata {
    /// Template instantiations that were compiled
    pub instantiations: Vec<InstantiationEntry>,
    /// Possible instantiations that can be lazily generated
    pub possible: Vec<PossibleInstantiationEntry>,
    /// Type inference events
    pub type_inferences: Vec<TypeInferenceEntry>,
    /// Dependency graph edges (from_inst -> to_inst)
    pub dependencies: Vec<DependencyEdge>,
    /// Circular dependency warnings (soft cycles)
    pub circular_warnings: Vec<CircularWarning>,
    /// Circular dependency errors (hard cycles)
    pub circular_errors: Vec<CircularError>,
}

impl NoteSdnMetadata {
    /// Create a new empty note.sdn metadata
    pub fn new() -> Self {
        Self::default()
    }

    /// Check if metadata is empty
    pub fn is_empty(&self) -> bool {
        self.instantiations.is_empty()
            && self.possible.is_empty()
            && self.type_inferences.is_empty()
            && self.dependencies.is_empty()
            && self.circular_warnings.is_empty()
            && self.circular_errors.is_empty()
    }

    /// Add an instantiation entry
    pub fn add_instantiation(&mut self, entry: InstantiationEntry) {
        self.instantiations.push(entry);
    }

    /// Add a possible instantiation entry
    pub fn add_possible(&mut self, entry: PossibleInstantiationEntry) {
        self.possible.push(entry);
    }

    /// Add a type inference entry
    pub fn add_type_inference(&mut self, entry: TypeInferenceEntry) {
        self.type_inferences.push(entry);
    }

    /// Add a dependency edge
    pub fn add_dependency(&mut self, edge: DependencyEdge) {
        self.dependencies.push(edge);
    }

    /// Add a circular warning
    pub fn add_circular_warning(&mut self, warning: CircularWarning) {
        self.circular_warnings.push(warning);
    }

    /// Add a circular error
    pub fn add_circular_error(&mut self, error: CircularError) {
        self.circular_errors.push(error);
    }

    /// Serialize to SDN format with terminator
    pub fn to_sdn(&self) -> String {
        let mut buf = String::new();

        // Header comment
        buf.push_str("# Instantiation To/From Metadata\n");
        buf.push_str("# Format version: 1.0\n\n");

        // instantiations table
        buf.push_str("# Template instantiations (what was compiled)\n");
        buf.push_str("instantiations |id, template, type_args, mangled_name, from_file, from_loc, to_obj, status|\n");
        for (idx, inst) in self.instantiations.iter().enumerate() {
            buf.push_str(&format!(
                "    {}, \"{}\", \"{}\", \"{}\", \"{}\", \"{}\", \"{}\", \"{}\"\n",
                idx,
                escape_sdn(&inst.template),
                escape_sdn(&inst.type_args),
                escape_sdn(&inst.mangled_name),
                escape_sdn(&inst.from_file),
                escape_sdn(&inst.from_loc),
                escape_sdn(&inst.to_obj),
                inst.status.as_str()
            ));
        }
        buf.push('\n');

        // possible table
        buf.push_str("# Possible instantiations (can be lazily generated)\n");
        buf.push_str("possible |id, template, type_args, mangled_name, required_by, can_defer|\n");
        for (idx, poss) in self.possible.iter().enumerate() {
            buf.push_str(&format!(
                "    {}, \"{}\", \"{}\", \"{}\", \"{}\", {}\n",
                idx,
                escape_sdn(&poss.template),
                escape_sdn(&poss.type_args),
                escape_sdn(&poss.mangled_name),
                escape_sdn(&poss.required_by),
                poss.can_defer
            ));
        }
        buf.push('\n');

        // type_inferences table
        buf.push_str("# Type inference instantiations\n");
        buf.push_str("type_inferences |id, inferred_type, expr, context, from_file, from_loc|\n");
        for (idx, inf) in self.type_inferences.iter().enumerate() {
            buf.push_str(&format!(
                "    {}, \"{}\", \"{}\", \"{}\", \"{}\", \"{}\"\n",
                idx,
                escape_sdn(&inf.inferred_type),
                escape_sdn(&inf.expr),
                escape_sdn(&inf.context),
                escape_sdn(&inf.from_file),
                escape_sdn(&inf.from_loc)
            ));
        }
        buf.push('\n');

        // dependencies table
        buf.push_str("# Instantiation graph (to/from relationships)\n");
        buf.push_str("dependencies |from_inst, to_inst, dep_kind|\n");
        for dep in &self.dependencies {
            buf.push_str(&format!(
                "    \"{}\", \"{}\", \"{}\"\n",
                escape_sdn(&dep.from_inst),
                escape_sdn(&dep.to_inst),
                dep.dep_kind.as_str()
            ));
        }
        buf.push('\n');

        // circular_warnings table
        buf.push_str("# Circular dependency detection results\n");
        buf.push_str("circular_warnings |id, cycle_path, severity|\n");
        for (idx, warn) in self.circular_warnings.iter().enumerate() {
            buf.push_str(&format!(
                "    {}, \"{}\", \"{}\"\n",
                idx,
                escape_sdn(&warn.cycle_path),
                escape_sdn(&warn.severity)
            ));
        }
        buf.push('\n');

        // circular_errors table
        buf.push_str("circular_errors |id, cycle_path, error_code|\n");
        for (idx, err) in self.circular_errors.iter().enumerate() {
            buf.push_str(&format!(
                "    {}, \"{}\", \"{}\"\n",
                idx,
                escape_sdn(&err.cycle_path),
                escape_sdn(&err.error_code)
            ));
        }
        buf.push('\n');

        // Terminator
        buf.push_str("# END_NOTE\n");

        buf
    }

    /// Parse from SDN format
    pub fn from_sdn(content: &str) -> Result<Self, String> {
        // TODO: Implement SDN parsing in Phase 2
        // For now, return empty metadata
        Err("SDN parsing not yet implemented".to_string())
    }
}

/// A template instantiation that was compiled.
#[derive(Debug, Clone)]
pub struct InstantiationEntry {
    /// Template base name (e.g., "List", "Option")
    pub template: String,
    /// Concrete type arguments (e.g., "Int", "String")
    pub type_args: String,
    /// Mangled symbol name (e.g., "List$Int")
    pub mangled_name: String,
    /// Source file that triggered instantiation
    pub from_file: String,
    /// Source location (file:line:col)
    pub from_loc: String,
    /// Object file where compiled code resides
    pub to_obj: String,
    /// Compilation status
    pub status: InstantiationStatus,
}

impl InstantiationEntry {
    pub fn new(
        template: String,
        type_args: Vec<ConcreteType>,
        mangled_name: String,
        from_file: String,
        from_loc: String,
        to_obj: String,
        status: InstantiationStatus,
    ) -> Self {
        let type_args_str = type_args
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join(",");

        Self {
            template,
            type_args: type_args_str,
            mangled_name,
            from_file,
            from_loc,
            to_obj,
            status,
        }
    }
}

/// Compilation status for an instantiation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstantiationStatus {
    /// Compiled to native code
    Compiled,
    /// Deferred for lazy compilation
    Deferred,
    /// JIT-compiled at runtime
    JitCompiled,
}

impl InstantiationStatus {
    pub fn as_str(&self) -> &'static str {
        match self {
            InstantiationStatus::Compiled => "compiled",
            InstantiationStatus::Deferred => "deferred",
            InstantiationStatus::JitCompiled => "jit_compiled",
        }
    }

    pub fn from_str(s: &str) -> Result<Self, String> {
        match s {
            "compiled" => Ok(InstantiationStatus::Compiled),
            "deferred" => Ok(InstantiationStatus::Deferred),
            "jit_compiled" => Ok(InstantiationStatus::JitCompiled),
            _ => Err(format!("Unknown instantiation status: {}", s)),
        }
    }
}

/// A possible instantiation that can be generated on-demand.
#[derive(Debug, Clone)]
pub struct PossibleInstantiationEntry {
    /// Template base name
    pub template: String,
    /// Concrete type arguments
    pub type_args: String,
    /// Mangled symbol name
    pub mangled_name: String,
    /// Which module needs this instantiation
    pub required_by: String,
    /// Can this be deferred to link/load time?
    pub can_defer: bool,
}

impl PossibleInstantiationEntry {
    pub fn new(
        template: String,
        type_args: Vec<ConcreteType>,
        mangled_name: String,
        required_by: String,
        can_defer: bool,
    ) -> Self {
        let type_args_str = type_args
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join(",");

        Self {
            template,
            type_args: type_args_str,
            mangled_name,
            required_by,
            can_defer,
        }
    }
}

/// A type inference event.
#[derive(Debug, Clone)]
pub struct TypeInferenceEntry {
    /// Inferred type (may be placeholder like "?T")
    pub inferred_type: String,
    /// Expression text
    pub expr: String,
    /// Inference context (e.g., "literal", "var_init", "depends_on_x")
    pub context: String,
    /// Source file
    pub from_file: String,
    /// Source location (file:line:col)
    pub from_loc: String,
}

impl TypeInferenceEntry {
    pub fn new(
        inferred_type: String,
        expr: String,
        context: String,
        from_file: String,
        from_loc: String,
    ) -> Self {
        Self {
            inferred_type,
            expr,
            context,
            from_file,
            from_loc,
        }
    }
}

/// A dependency edge in the instantiation graph.
#[derive(Debug, Clone)]
pub struct DependencyEdge {
    /// Source instantiation (e.g., "List$Int")
    pub from_inst: String,
    /// Target instantiation (e.g., "Int")
    pub to_inst: String,
    /// Dependency kind
    pub dep_kind: DependencyKind,
}

impl DependencyEdge {
    pub fn new(from_inst: String, to_inst: String, dep_kind: DependencyKind) -> Self {
        Self {
            from_inst,
            to_inst,
            dep_kind,
        }
    }
}

/// Kind of dependency between instantiations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DependencyKind {
    /// Type parameter dependency (e.g., List<T> depends on T)
    TypeParam,
    /// Field type dependency (e.g., struct with field of type T)
    FieldType,
    /// Inner type dependency (e.g., Option<T> wraps T)
    InnerType,
    /// Method dependency (e.g., method returns T)
    MethodDep,
}

impl DependencyKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            DependencyKind::TypeParam => "type_param",
            DependencyKind::FieldType => "field_type",
            DependencyKind::InnerType => "inner_type",
            DependencyKind::MethodDep => "method_dep",
        }
    }

    pub fn from_str(s: &str) -> Result<Self, String> {
        match s {
            "type_param" => Ok(DependencyKind::TypeParam),
            "field_type" => Ok(DependencyKind::FieldType),
            "inner_type" => Ok(DependencyKind::InnerType),
            "method_dep" => Ok(DependencyKind::MethodDep),
            _ => Err(format!("Unknown dependency kind: {}", s)),
        }
    }
}

/// A circular dependency warning (soft cycle, broken by indirection).
#[derive(Debug, Clone)]
pub struct CircularWarning {
    /// Cycle path (e.g., "Node$T->Option$Node$T->Node$T")
    pub cycle_path: String,
    /// Severity level
    pub severity: String,
}

impl CircularWarning {
    pub fn new(cycle_path: String, severity: String) -> Self {
        Self {
            cycle_path,
            severity,
        }
    }
}

/// A circular dependency error (hard cycle, not allowed).
#[derive(Debug, Clone)]
pub struct CircularError {
    /// Cycle path (e.g., "A$T->B$T->C$T->A$T")
    pub cycle_path: String,
    /// Error code (e.g., "E0420", "E0421")
    pub error_code: String,
}

impl CircularError {
    pub fn new(cycle_path: String, error_code: String) -> Self {
        Self {
            cycle_path,
            error_code,
        }
    }
}

/// Escape special characters for SDN format.
fn escape_sdn(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_note_sdn() {
        let note = NoteSdnMetadata::new();
        assert!(note.is_empty());

        let sdn = note.to_sdn();
        assert!(sdn.contains("# END_NOTE\n"));
        assert!(sdn.contains("instantiations |"));
        assert!(sdn.contains("possible |"));
    }

    #[test]
    fn test_instantiation_entry() {
        let mut note = NoteSdnMetadata::new();

        let entry = InstantiationEntry::new(
            "List".to_string(),
            vec![ConcreteType::Named("Int".to_string())],
            "List$Int".to_string(),
            "app.spl".to_string(),
            "app.spl:10:5".to_string(),
            "app.o".to_string(),
            InstantiationStatus::Compiled,
        );

        note.add_instantiation(entry);

        let sdn = note.to_sdn();
        assert!(sdn.contains("\"List\""));
        assert!(sdn.contains("\"Int\""));
        assert!(sdn.contains("\"List$Int\""));
        assert!(sdn.contains("\"compiled\""));
    }

    #[test]
    fn test_dependency_edge() {
        let mut note = NoteSdnMetadata::new();

        let edge = DependencyEdge::new(
            "List$Int".to_string(),
            "Int".to_string(),
            DependencyKind::TypeParam,
        );

        note.add_dependency(edge);

        let sdn = note.to_sdn();
        assert!(sdn.contains("\"List$Int\", \"Int\", \"type_param\""));
    }

    #[test]
    fn test_circular_warning() {
        let mut note = NoteSdnMetadata::new();

        let warning = CircularWarning::new(
            "Node$T->Option$Node$T->Node$T".to_string(),
            "warning".to_string(),
        );

        note.add_circular_warning(warning);

        let sdn = note.to_sdn();
        assert!(sdn.contains("\"Node$T->Option$Node$T->Node$T\""));
        assert!(sdn.contains("\"warning\""));
    }

    #[test]
    fn test_sdn_escape() {
        let s = "test\"with\\quotes\nand\nnewlines";
        let escaped = escape_sdn(s);
        assert!(escaped.contains("\\\""));
        assert!(escaped.contains("\\\\"));
        assert!(escaped.contains("\\n"));
    }
}
