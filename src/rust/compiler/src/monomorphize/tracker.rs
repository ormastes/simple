//! Compile-time tracking of generic instantiations.
//!
//! This module tracks instantiations during compilation to populate
//! the note.sdn section for lazy instantiation and dependency analysis.
//!
//! Phase 3: Compile-Time Tracking

use std::collections::{HashMap, HashSet};

use super::note_sdn::{
    CircularError, CircularWarning, DependencyEdge, DependencyKind, InstantiationEntry,
    InstantiationStatus, NoteSdnMetadata, PossibleInstantiationEntry, TypeInferenceEntry,
};
use super::cycle_detector::{detect_cycles, analyze_and_update_cycles};
use super::types::ConcreteType;

/// Tracks instantiations during compilation.
#[derive(Debug, Default)]
pub struct InstantiationTracker {
    /// Accumulated note.sdn metadata
    metadata: NoteSdnMetadata,
    /// Current instantiation ID counter
    next_inst_id: u32,
    /// Set of already-tracked mangled names (avoid duplicates)
    tracked_names: HashSet<String>,
    /// Current source file being compiled
    current_file: String,
    /// Current object file target
    current_obj: String,
    /// Pending dependencies to add after instantiation completes
    pending_deps: Vec<(String, String, DependencyKind)>,
}

impl InstantiationTracker {
    /// Create a new tracker for a compilation unit.
    pub fn new(source_file: String, obj_file: String) -> Self {
        Self {
            metadata: NoteSdnMetadata::new(),
            next_inst_id: 0,
            tracked_names: HashSet::new(),
            current_file: source_file,
            current_obj: obj_file,
            pending_deps: Vec::new(),
        }
    }

    /// Get the current source file.
    pub fn current_file(&self) -> &str {
        &self.current_file
    }

    /// Set the current source file.
    pub fn set_current_file(&mut self, file: String) {
        self.current_file = file;
    }

    /// Track a compiled instantiation.
    pub fn track_instantiation(
        &mut self,
        template: &str,
        type_args: &[ConcreteType],
        mangled_name: &str,
        source_loc: &str,
        status: InstantiationStatus,
    ) {
        // Skip if already tracked
        if self.tracked_names.contains(mangled_name) {
            return;
        }

        let entry = InstantiationEntry::new(
            template.to_string(),
            type_args.to_vec(),
            mangled_name.to_string(),
            self.current_file.clone(),
            source_loc.to_string(),
            self.current_obj.clone(),
            status,
        );

        self.metadata.add_instantiation(entry);
        self.tracked_names.insert(mangled_name.to_string());
        self.next_inst_id += 1;

        // Process pending dependencies
        self.flush_pending_deps();
    }

    /// Track a possible (deferrable) instantiation.
    pub fn track_possible(
        &mut self,
        template: &str,
        type_args: &[ConcreteType],
        mangled_name: &str,
        required_by: &str,
        can_defer: bool,
    ) {
        // Skip if already tracked as compiled
        if self.tracked_names.contains(mangled_name) {
            return;
        }

        let entry = PossibleInstantiationEntry::new(
            template.to_string(),
            type_args.to_vec(),
            mangled_name.to_string(),
            required_by.to_string(),
            can_defer,
        );

        self.metadata.add_possible(entry);
    }

    /// Track a type inference event.
    pub fn track_type_inference(
        &mut self,
        inferred_type: &str,
        expr: &str,
        context: &str,
        source_loc: &str,
    ) {
        let entry = TypeInferenceEntry::new(
            inferred_type.to_string(),
            expr.to_string(),
            context.to_string(),
            self.current_file.clone(),
            source_loc.to_string(),
        );

        self.metadata.add_type_inference(entry);
    }

    /// Track a dependency between instantiations.
    pub fn track_dependency(
        &mut self,
        from_inst: &str,
        to_inst: &str,
        dep_kind: DependencyKind,
    ) {
        // If from_inst is not yet tracked, queue the dependency
        if !self.tracked_names.contains(from_inst) {
            self.pending_deps.push((
                from_inst.to_string(),
                to_inst.to_string(),
                dep_kind,
            ));
            return;
        }

        let edge = DependencyEdge::new(
            from_inst.to_string(),
            to_inst.to_string(),
            dep_kind,
        );

        self.metadata.add_dependency(edge);
    }

    /// Flush pending dependencies that can now be added.
    fn flush_pending_deps(&mut self) {
        let mut remaining = Vec::new();

        for (from, to, kind) in std::mem::take(&mut self.pending_deps) {
            if self.tracked_names.contains(&from) {
                let edge = DependencyEdge::new(from, to, kind);
                self.metadata.add_dependency(edge);
            } else {
                remaining.push((from, to, kind));
            }
        }

        self.pending_deps = remaining;
    }

    /// Analyze for circular dependencies and update metadata.
    pub fn analyze_cycles(&mut self) {
        analyze_and_update_cycles(&mut self.metadata);
    }

    /// Check if there are any circular errors.
    pub fn has_circular_errors(&self) -> bool {
        !self.metadata.circular_errors.is_empty()
    }

    /// Get circular errors.
    pub fn circular_errors(&self) -> &[CircularError] {
        &self.metadata.circular_errors
    }

    /// Get circular warnings.
    pub fn circular_warnings(&self) -> &[CircularWarning] {
        &self.metadata.circular_warnings
    }

    /// Finalize tracking and return the metadata.
    pub fn finalize(mut self) -> NoteSdnMetadata {
        // Flush any remaining pending deps
        self.flush_pending_deps();
        // Analyze cycles
        self.analyze_cycles();
        self.metadata
    }

    /// Get a reference to the current metadata (for inspection).
    pub fn metadata(&self) -> &NoteSdnMetadata {
        &self.metadata
    }

    /// Merge metadata from another tracker (for multi-file compilation).
    pub fn merge(&mut self, other: NoteSdnMetadata) {
        for inst in other.instantiations {
            if !self.tracked_names.contains(&inst.mangled_name) {
                self.tracked_names.insert(inst.mangled_name.clone());
                self.metadata.add_instantiation(inst);
            }
        }

        for poss in other.possible {
            if !self.tracked_names.contains(&poss.mangled_name) {
                self.metadata.add_possible(poss);
            }
        }

        for inf in other.type_inferences {
            self.metadata.add_type_inference(inf);
        }

        for dep in other.dependencies {
            self.metadata.add_dependency(dep);
        }

        // Re-analyze cycles after merge
        self.analyze_cycles();
    }
}

/// Builder for tracking instantiations during monomorphization.
pub struct TrackingContext<'a> {
    tracker: &'a mut InstantiationTracker,
    current_template: String,
    current_type_args: Vec<ConcreteType>,
    current_mangled: String,
}

impl<'a> TrackingContext<'a> {
    /// Start tracking a new instantiation.
    pub fn start(
        tracker: &'a mut InstantiationTracker,
        template: &str,
        type_args: Vec<ConcreteType>,
        mangled_name: &str,
    ) -> Self {
        Self {
            tracker,
            current_template: template.to_string(),
            current_type_args: type_args,
            current_mangled: mangled_name.to_string(),
        }
    }

    /// Record that this instantiation depends on another type.
    pub fn depends_on(&mut self, to_inst: &str, kind: DependencyKind) {
        self.tracker.track_dependency(&self.current_mangled, to_inst, kind);
    }

    /// Record a type parameter dependency.
    pub fn depends_on_type_param(&mut self, type_name: &str) {
        self.depends_on(type_name, DependencyKind::TypeParam);
    }

    /// Record a field type dependency.
    pub fn depends_on_field_type(&mut self, type_name: &str) {
        self.depends_on(type_name, DependencyKind::FieldType);
    }

    /// Complete the instantiation tracking.
    pub fn complete(self, source_loc: &str, status: InstantiationStatus) {
        self.tracker.track_instantiation(
            &self.current_template,
            &self.current_type_args,
            &self.current_mangled,
            source_loc,
            status,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tracker_basic() {
        let mut tracker = InstantiationTracker::new(
            "test.spl".to_string(),
            "test.o".to_string(),
        );

        tracker.track_instantiation(
            "List",
            &[ConcreteType::Named("Int".to_string())],
            "List$Int",
            "test.spl:10:5",
            InstantiationStatus::Compiled,
        );

        let metadata = tracker.finalize();
        assert_eq!(metadata.instantiations.len(), 1);
        assert_eq!(metadata.instantiations[0].template, "List");
        assert_eq!(metadata.instantiations[0].mangled_name, "List$Int");
    }

    #[test]
    fn test_tracker_dependencies() {
        let mut tracker = InstantiationTracker::new(
            "test.spl".to_string(),
            "test.o".to_string(),
        );

        tracker.track_instantiation(
            "List",
            &[ConcreteType::Named("Int".to_string())],
            "List$Int",
            "test.spl:10:5",
            InstantiationStatus::Compiled,
        );

        tracker.track_dependency("List$Int", "Int", DependencyKind::TypeParam);

        let metadata = tracker.finalize();
        assert_eq!(metadata.dependencies.len(), 1);
        assert_eq!(metadata.dependencies[0].from_inst, "List$Int");
        assert_eq!(metadata.dependencies[0].to_inst, "Int");
    }

    #[test]
    fn test_tracker_possible() {
        let mut tracker = InstantiationTracker::new(
            "test.spl".to_string(),
            "test.o".to_string(),
        );

        tracker.track_possible(
            "List",
            &[ConcreteType::Named("Float".to_string())],
            "List$Float",
            "math_module",
            true,
        );

        let metadata = tracker.finalize();
        assert_eq!(metadata.possible.len(), 1);
        assert_eq!(metadata.possible[0].template, "List");
        assert!(metadata.possible[0].can_defer);
    }

    #[test]
    fn test_tracking_context() {
        let mut tracker = InstantiationTracker::new(
            "test.spl".to_string(),
            "test.o".to_string(),
        );

        {
            let mut ctx = TrackingContext::start(
                &mut tracker,
                "Container",
                vec![ConcreteType::Named("Int".to_string())],
                "Container$Int",
            );
            ctx.depends_on_type_param("Int");
            ctx.depends_on_field_type("List$Int");
            ctx.complete("test.spl:20:3", InstantiationStatus::Compiled);
        }

        let metadata = tracker.finalize();
        assert_eq!(metadata.instantiations.len(), 1);
        assert_eq!(metadata.dependencies.len(), 2);
    }

    #[test]
    fn test_no_duplicates() {
        let mut tracker = InstantiationTracker::new(
            "test.spl".to_string(),
            "test.o".to_string(),
        );

        tracker.track_instantiation(
            "List",
            &[ConcreteType::Named("Int".to_string())],
            "List$Int",
            "test.spl:10:5",
            InstantiationStatus::Compiled,
        );

        // Try to track same thing again
        tracker.track_instantiation(
            "List",
            &[ConcreteType::Named("Int".to_string())],
            "List$Int",
            "test.spl:15:5",
            InstantiationStatus::Compiled,
        );

        let metadata = tracker.finalize();
        assert_eq!(metadata.instantiations.len(), 1);
    }
}
