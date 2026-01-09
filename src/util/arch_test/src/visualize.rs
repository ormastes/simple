//! Dependency graph visualization
//!
//! Generates DOT format output for visualizing layer dependencies.
//!
//! ## Example
//!
//! ```rust,ignore
//! use arch_test::{Architecture, visualize};
//!
//! let arch = Architecture::new()
//!     .layer("ui", &["src/ui/**"])
//!     .layer("service", &["src/service/**"])
//!     .layer("data", &["src/data/**"]);
//!
//! let dot = visualize::to_dot(&arch, &module_tree);
//! println!("{}", dot);
//! ```

use crate::{Layer, ModuleTree};
use std::collections::{HashMap, HashSet};

/// Graph output format
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputFormat {
    /// DOT format for Graphviz
    Dot,
    /// Mermaid diagram format
    Mermaid,
    /// Plain text format
    Text,
}

/// Options for graph visualization
#[derive(Debug, Clone)]
pub struct VisualizeOptions {
    /// Output format
    pub format: OutputFormat,
    /// Show module-level dependencies (vs layer-level only)
    pub show_modules: bool,
    /// Cluster modules by layer
    pub cluster_by_layer: bool,
    /// Highlight violations
    pub highlight_violations: bool,
    /// Include external dependencies
    pub include_external: bool,
}

impl Default for VisualizeOptions {
    fn default() -> Self {
        Self {
            format: OutputFormat::Dot,
            show_modules: false,
            cluster_by_layer: true,
            highlight_violations: true,
            include_external: false,
        }
    }
}

/// Generate a DOT format graph of layer dependencies
pub fn to_dot(layers: &HashMap<String, Layer>, module_tree: &ModuleTree) -> String {
    to_dot_with_options(layers, module_tree, &VisualizeOptions::default())
}

/// Generate a DOT format graph with custom options
pub fn to_dot_with_options(
    layers: &HashMap<String, Layer>,
    module_tree: &ModuleTree,
    options: &VisualizeOptions,
) -> String {
    match options.format {
        OutputFormat::Dot => generate_dot(layers, module_tree, options),
        OutputFormat::Mermaid => generate_mermaid(layers, module_tree, options),
        OutputFormat::Text => generate_text(layers, module_tree, options),
    }
}

/// Find which layer a module belongs to
fn find_layer<'a>(module: &str, layers: &'a HashMap<String, Layer>) -> Option<&'a str> {
    for (name, layer) in layers {
        if layer.contains_module(module) {
            return Some(name.as_str());
        }
    }
    None
}

/// Build layer-level dependency graph
fn build_layer_graph(
    layers: &HashMap<String, Layer>,
    module_tree: &ModuleTree,
) -> HashMap<String, HashSet<String>> {
    let mut layer_deps: HashMap<String, HashSet<String>> = HashMap::new();

    // Initialize all layers
    for name in layers.keys() {
        layer_deps.insert(name.clone(), HashSet::new());
    }

    // Build dependencies
    for (module, deps) in &module_tree.dependencies {
        if let Some(src_layer) = find_layer(module, layers) {
            for dep in deps {
                if let Some(tgt_layer) = find_layer(dep, layers) {
                    if src_layer != tgt_layer {
                        layer_deps
                            .entry(src_layer.to_string())
                            .or_default()
                            .insert(tgt_layer.to_string());
                    }
                }
            }
        }
    }

    layer_deps
}

/// Generate DOT format output
fn generate_dot(
    layers: &HashMap<String, Layer>,
    module_tree: &ModuleTree,
    options: &VisualizeOptions,
) -> String {
    let mut output = String::new();
    output.push_str("digraph architecture {\n");
    output.push_str("    rankdir=TB;\n");
    output.push_str("    node [shape=box, style=filled];\n");
    output.push_str("    \n");

    if options.show_modules && options.cluster_by_layer {
        // Generate subgraphs for each layer containing modules
        for (layer_name, layer) in layers {
            output.push_str(&format!("    subgraph cluster_{} {{\n", layer_name));
            output.push_str(&format!("        label=\"{}\";\n", layer_name));
            output.push_str("        style=filled;\n");
            output.push_str("        color=lightgrey;\n");
            output.push_str("        \n");

            // Add modules in this layer
            for module in module_tree.modules() {
                if layer.contains_module(module) {
                    let node_id = module.replace(['/', '.', '-'], "_");
                    let label = module.split('/').last().unwrap_or(module);
                    output.push_str(&format!(
                        "        {} [label=\"{}\", fillcolor=white];\n",
                        node_id, label
                    ));
                }
            }

            output.push_str("    }\n");
            output.push_str("    \n");
        }

        // Add module-level edges
        for (module, deps) in &module_tree.dependencies {
            let src_id = module.replace(['/', '.', '-'], "_");
            for dep in deps {
                if options.include_external || find_layer(dep, layers).is_some() {
                    let tgt_id = dep.replace(['/', '.', '-'], "_");
                    output.push_str(&format!("    {} -> {};\n", src_id, tgt_id));
                }
            }
        }
    } else {
        // Layer-level graph only
        let layer_deps = build_layer_graph(layers, module_tree);

        // Layer colors
        let colors = [
            "#a6cee3", "#b2df8a", "#fb9a99", "#fdbf6f", "#cab2d6", "#ffff99",
        ];

        // Add layer nodes
        for (i, layer_name) in layers.keys().enumerate() {
            let color = colors.get(i % colors.len()).unwrap_or(&"#ffffff");
            output.push_str(&format!(
                "    {} [label=\"{}\", fillcolor=\"{}\"];\n",
                layer_name, layer_name, color
            ));
        }

        output.push_str("    \n");

        // Add layer edges
        for (src, targets) in &layer_deps {
            for tgt in targets {
                output.push_str(&format!("    {} -> {};\n", src, tgt));
            }
        }
    }

    output.push_str("}\n");
    output
}

/// Generate Mermaid diagram format
fn generate_mermaid(
    layers: &HashMap<String, Layer>,
    module_tree: &ModuleTree,
    _options: &VisualizeOptions,
) -> String {
    let mut output = String::new();
    output.push_str("graph TD\n");

    let layer_deps = build_layer_graph(layers, module_tree);

    // Add layer nodes
    for layer_name in layers.keys() {
        output.push_str(&format!("    {}[{}]\n", layer_name, layer_name));
    }

    output.push_str("\n");

    // Add edges
    for (src, targets) in &layer_deps {
        for tgt in targets {
            output.push_str(&format!("    {} --> {}\n", src, tgt));
        }
    }

    output
}

/// Generate plain text format
fn generate_text(
    layers: &HashMap<String, Layer>,
    module_tree: &ModuleTree,
    _options: &VisualizeOptions,
) -> String {
    let mut output = String::new();
    output.push_str("Layer Dependencies:\n");
    output.push_str("==================\n\n");

    let layer_deps = build_layer_graph(layers, module_tree);

    for (src, targets) in &layer_deps {
        if targets.is_empty() {
            output.push_str(&format!("{} -> (no dependencies)\n", src));
        } else {
            let targets_str: Vec<_> = targets.iter().map(|s| s.as_str()).collect();
            output.push_str(&format!("{} -> {}\n", src, targets_str.join(", ")));
        }
    }

    output.push_str("\nModules by Layer:\n");
    output.push_str("=================\n\n");

    for (layer_name, layer) in layers {
        output.push_str(&format!("{}:\n", layer_name));
        for module in module_tree.modules() {
            if layer.contains_module(module) {
                output.push_str(&format!("  - {}\n", module));
            }
        }
        output.push('\n');
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_layers() -> HashMap<String, Layer> {
        let mut layers = HashMap::new();
        layers.insert(
            "ui".to_string(),
            Layer::new("ui", vec!["src/ui/**".to_string()]),
        );
        layers.insert(
            "service".to_string(),
            Layer::new("service", vec!["src/service/**".to_string()]),
        );
        layers.insert(
            "data".to_string(),
            Layer::new("data", vec!["src/data/**".to_string()]),
        );
        layers
    }

    fn create_test_module_tree() -> ModuleTree {
        let mut tree = ModuleTree::new();
        tree.add_dependency("src/ui/view", "src/service/auth");
        tree.add_dependency("src/service/auth", "src/data/user");
        tree
    }

    #[test]
    fn test_dot_output() {
        let layers = create_test_layers();
        let tree = create_test_module_tree();
        let dot = to_dot(&layers, &tree);

        assert!(dot.contains("digraph architecture"));
        assert!(dot.contains("ui"));
        assert!(dot.contains("service"));
        assert!(dot.contains("data"));
        assert!(dot.contains("->"));
    }

    #[test]
    fn test_mermaid_output() {
        let layers = create_test_layers();
        let tree = create_test_module_tree();
        let options = VisualizeOptions {
            format: OutputFormat::Mermaid,
            ..Default::default()
        };
        let mermaid = to_dot_with_options(&layers, &tree, &options);

        assert!(mermaid.contains("graph TD"));
        assert!(mermaid.contains("-->"));
    }

    #[test]
    fn test_text_output() {
        let layers = create_test_layers();
        let tree = create_test_module_tree();
        let options = VisualizeOptions {
            format: OutputFormat::Text,
            ..Default::default()
        };
        let text = to_dot_with_options(&layers, &tree, &options);

        assert!(text.contains("Layer Dependencies:"));
        assert!(text.contains("Modules by Layer:"));
    }

    #[test]
    fn test_layer_graph_building() {
        let layers = create_test_layers();
        let tree = create_test_module_tree();
        let graph = build_layer_graph(&layers, &tree);

        assert!(graph.get("ui").unwrap().contains("service"));
        assert!(graph.get("service").unwrap().contains("data"));
        assert!(graph.get("data").unwrap().is_empty());
    }
}
