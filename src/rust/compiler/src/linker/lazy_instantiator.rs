//! Lazy instantiation at link-time.
//!
//! This module handles on-demand instantiation of generic templates
//! when resolving missing symbols during linking.
//!
//! Phase 4: Link-Time Lazy Instantiation

use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::monomorphize::{
    DependencyEdge, DependencyKind, InstantiationEntry, InstantiationStatus,
    NoteSdnMetadata, PossibleInstantiationEntry,
};

/// Result of lazy instantiation attempt.
#[derive(Debug)]
pub enum LazyInstantiationResult {
    /// Successfully instantiated
    Success {
        /// Generated code (MIR or machine code)
        code: Vec<u8>,
        /// Symbol name
        symbol: String,
        /// Updated metadata
        metadata: NoteSdnMetadata,
    },
    /// Template not found in any input SMF
    NotFound {
        /// Missing symbol name
        symbol: String,
    },
    /// Instantiation would create circular dependency
    CircularDependency {
        /// Cycle path
        cycle: Vec<String>,
    },
    /// Instantiation deferred (can be done at load-time)
    Deferred {
        /// Symbol name
        symbol: String,
    },
    /// Error during instantiation
    Error {
        /// Error message
        message: String,
    },
}

/// Configuration for lazy instantiation.
#[derive(Debug, Clone)]
pub struct LazyInstantiatorConfig {
    /// Allow deferring instantiation to load-time
    pub allow_defer: bool,
    /// Maximum instantiation depth (prevent runaway recursion)
    pub max_depth: usize,
    /// Verbose logging
    pub verbose: bool,
}

impl Default for LazyInstantiatorConfig {
    fn default() -> Self {
        Self {
            allow_defer: true,
            max_depth: 100,
            verbose: false,
        }
    }
}

/// Lazy instantiator for link-time instantiation.
pub struct LazyInstantiator {
    /// Configuration
    config: LazyInstantiatorConfig,
    /// note.sdn metadata from all input SMFs, keyed by file path
    input_metadata: HashMap<String, NoteSdnMetadata>,
    /// Merged metadata for output
    output_metadata: NoteSdnMetadata,
    /// Set of symbols being instantiated (for cycle detection)
    in_progress: HashSet<String>,
    /// Current instantiation depth
    depth: usize,
    /// Cache of instantiated symbols
    instantiated: HashMap<String, Vec<u8>>,
}

impl LazyInstantiator {
    /// Create a new lazy instantiator.
    pub fn new(config: LazyInstantiatorConfig) -> Self {
        Self {
            config,
            input_metadata: HashMap::new(),
            output_metadata: NoteSdnMetadata::new(),
            in_progress: HashSet::new(),
            depth: 0,
            instantiated: HashMap::new(),
        }
    }

    /// Load note.sdn metadata from an input SMF file.
    pub fn load_metadata(&mut self, smf_path: &Path, metadata: NoteSdnMetadata) {
        let path_str = smf_path.to_string_lossy().to_string();

        // Merge instantiations into output
        for inst in &metadata.instantiations {
            self.output_metadata.add_instantiation(inst.clone());
        }

        // Keep possible entries for lookup
        self.input_metadata.insert(path_str, metadata);
    }

    /// Check if a symbol can be lazily instantiated.
    pub fn can_instantiate(&self, symbol: &str) -> bool {
        for metadata in self.input_metadata.values() {
            if metadata.possible.iter().any(|p| p.mangled_name == symbol) {
                return true;
            }
        }
        false
    }

    /// Find possible instantiation entry for a symbol.
    fn find_possible(&self, symbol: &str) -> Option<(&str, &PossibleInstantiationEntry)> {
        for (path, metadata) in &self.input_metadata {
            if let Some(entry) = metadata.possible.iter().find(|p| p.mangled_name == symbol) {
                return Some((path.as_str(), entry));
            }
        }
        None
    }

    /// Try to instantiate a missing symbol.
    pub fn try_instantiate(&mut self, symbol: &str) -> LazyInstantiationResult {
        // Check depth limit
        if self.depth >= self.config.max_depth {
            return LazyInstantiationResult::Error {
                message: format!("Maximum instantiation depth ({}) exceeded", self.config.max_depth),
            };
        }

        // Check if already instantiated
        if let Some(code) = self.instantiated.get(symbol) {
            return LazyInstantiationResult::Success {
                code: code.clone(),
                symbol: symbol.to_string(),
                metadata: self.output_metadata.clone(),
            };
        }

        // Check for cycle
        if self.in_progress.contains(symbol) {
            let cycle: Vec<String> = self.in_progress.iter().cloned().collect();
            return LazyInstantiationResult::CircularDependency { cycle };
        }

        // Find possible entry
        let (source_path, entry) = match self.find_possible(symbol) {
            Some((path, entry)) => (path.to_string(), entry.clone()),
            None => {
                return LazyInstantiationResult::NotFound {
                    symbol: symbol.to_string(),
                };
            }
        };

        // Check if can defer
        if entry.can_defer && self.config.allow_defer {
            return LazyInstantiationResult::Deferred {
                symbol: symbol.to_string(),
            };
        }

        // Start instantiation
        self.in_progress.insert(symbol.to_string());
        self.depth += 1;

        if self.config.verbose {
            eprintln!("[lazy-inst] Instantiating {} from {}", symbol, source_path);
        }

        // TODO: Actual instantiation logic
        // This would:
        // 1. Load template code from TemplateCode section
        // 2. Parse type arguments from mangled name
        // 3. Apply type substitution
        // 4. Compile to MIR/machine code
        // 5. Resolve any transitive dependencies recursively

        let result = self.do_instantiate(&entry, &source_path);

        // Cleanup
        self.in_progress.remove(symbol);
        self.depth -= 1;

        result
    }

    /// Perform the actual instantiation.
    fn do_instantiate(
        &mut self,
        entry: &PossibleInstantiationEntry,
        source_path: &str,
    ) -> LazyInstantiationResult {
        // Create instantiation entry
        let inst_entry = InstantiationEntry::new(
            entry.template.clone(),
            vec![], // TODO: Parse type args
            entry.mangled_name.clone(),
            source_path.to_string(),
            format!("{}:0:0", source_path),
            "link_output.o".to_string(),
            InstantiationStatus::Compiled,
        );

        // Add to output metadata
        self.output_metadata.add_instantiation(inst_entry);

        // Add dependency edge
        let dep = DependencyEdge::new(
            entry.required_by.clone(),
            entry.mangled_name.clone(),
            DependencyKind::TypeParam,
        );
        self.output_metadata.add_dependency(dep);

        // TODO: Generate actual code
        let placeholder_code = vec![0u8; 0];
        self.instantiated.insert(entry.mangled_name.clone(), placeholder_code.clone());

        LazyInstantiationResult::Success {
            code: placeholder_code,
            symbol: entry.mangled_name.clone(),
            metadata: self.output_metadata.clone(),
        }
    }

    /// Get all missing symbols that could be instantiated.
    pub fn get_instantiable_missing(&self, missing_symbols: &[String]) -> Vec<String> {
        missing_symbols
            .iter()
            .filter(|s| self.can_instantiate(s))
            .cloned()
            .collect()
    }

    /// Instantiate all missing symbols that can be instantiated.
    pub fn instantiate_all_missing(
        &mut self,
        missing_symbols: &[String],
    ) -> Vec<LazyInstantiationResult> {
        let instantiable = self.get_instantiable_missing(missing_symbols);
        let mut results = Vec::new();

        for symbol in instantiable {
            let result = self.try_instantiate(&symbol);
            results.push(result);
        }

        results
    }

    /// Get the output metadata.
    pub fn output_metadata(&self) -> &NoteSdnMetadata {
        &self.output_metadata
    }

    /// Finalize and return the output metadata.
    pub fn finalize(self) -> NoteSdnMetadata {
        self.output_metadata
    }
}

/// Statistics from lazy instantiation.
#[derive(Debug, Default)]
pub struct LazyInstantiationStats {
    /// Number of symbols instantiated
    pub instantiated: usize,
    /// Number of symbols deferred
    pub deferred: usize,
    /// Number of symbols not found
    pub not_found: usize,
    /// Number of errors
    pub errors: usize,
}

impl LazyInstantiationStats {
    pub fn from_results(results: &[LazyInstantiationResult]) -> Self {
        let mut stats = Self::default();
        for result in results {
            match result {
                LazyInstantiationResult::Success { .. } => stats.instantiated += 1,
                LazyInstantiationResult::Deferred { .. } => stats.deferred += 1,
                LazyInstantiationResult::NotFound { .. } => stats.not_found += 1,
                LazyInstantiationResult::Error { .. } => stats.errors += 1,
                LazyInstantiationResult::CircularDependency { .. } => stats.errors += 1,
            }
        }
        stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazy_instantiator_basic() {
        let config = LazyInstantiatorConfig::default();
        let mut instantiator = LazyInstantiator::new(config);

        // Create test metadata with a possible instantiation
        let mut metadata = NoteSdnMetadata::new();
        metadata.add_possible(PossibleInstantiationEntry::new(
            "List".to_string(),
            vec![],
            "List$Float".to_string(),
            "app_module".to_string(),
            false, // can't defer
        ));

        instantiator.load_metadata(Path::new("lib.smf"), metadata);

        assert!(instantiator.can_instantiate("List$Float"));
        assert!(!instantiator.can_instantiate("List$Double"));
    }

    #[test]
    fn test_lazy_instantiator_defer() {
        let config = LazyInstantiatorConfig {
            allow_defer: true,
            ..Default::default()
        };
        let mut instantiator = LazyInstantiator::new(config);

        let mut metadata = NoteSdnMetadata::new();
        metadata.add_possible(PossibleInstantiationEntry::new(
            "Option".to_string(),
            vec![],
            "Option$Int".to_string(),
            "app_module".to_string(),
            true, // can defer
        ));

        instantiator.load_metadata(Path::new("lib.smf"), metadata);

        let result = instantiator.try_instantiate("Option$Int");
        assert!(matches!(result, LazyInstantiationResult::Deferred { .. }));
    }

    #[test]
    fn test_lazy_instantiator_not_found() {
        let config = LazyInstantiatorConfig::default();
        let mut instantiator = LazyInstantiator::new(config);

        let result = instantiator.try_instantiate("NonExistent$Type");
        assert!(matches!(result, LazyInstantiationResult::NotFound { .. }));
    }

    #[test]
    fn test_stats() {
        let results = vec![
            LazyInstantiationResult::Success {
                code: vec![],
                symbol: "A".to_string(),
                metadata: NoteSdnMetadata::new(),
            },
            LazyInstantiationResult::Deferred {
                symbol: "B".to_string(),
            },
            LazyInstantiationResult::NotFound {
                symbol: "C".to_string(),
            },
        ];

        let stats = LazyInstantiationStats::from_results(&results);
        assert_eq!(stats.instantiated, 1);
        assert_eq!(stats.deferred, 1);
        assert_eq!(stats.not_found, 1);
    }
}
