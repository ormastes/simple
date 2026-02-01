//! WebAssembly Bindgen Code Generation
//!
//! Generates wasm-bindgen bindings for browser FFI functions marked with @extern("browser", "function_name").
//! This enables Simple code compiled to WASM to call JavaScript browser APIs.
//!
//! # Example
//!
//! Simple code:
//! ```text
//! @extern("browser", "console_log")
//! fn log(message: str):
//!     pass
//! ```
//!
//! Usage:
//! ```
//! use simple_compiler::codegen::wasm_bindgen_gen::{BindingExtractor, BrowserBinding};
//! use simple_parser::ast::Module;
//!
//! let mut extractor = BindingExtractor::new();
//! # let module = Module::default();
//! let bindings = extractor.extract(&module);
//! // Process extracted browser FFI bindings
//! ```
//!
//! Generated wasm-bindgen output:
//! ```text
//! #[wasm_bindgen]
//! extern "C" {
//!     #[wasm_bindgen(js_namespace = console, js_name = log)]
//!     fn console_log(message: &str);
//! }
//! ```

use simple_parser::ast::{Argument, Expr, FunctionDef, Module, Node, Type};
use simple_parser::token::Span;
use std::collections::HashMap;

/// Represents a browser FFI binding extracted from @extern decorator
#[derive(Debug, Clone, PartialEq)]
pub struct BrowserBinding {
    /// Simple function name
    pub simple_name: String,
    /// Browser module (e.g., "browser", "console", "dom")
    pub module: String,
    /// JavaScript function name
    pub js_name: String,
    /// Function parameters
    pub params: Vec<(String, Type)>,
    /// Return type
    pub return_type: Option<Type>,
    /// Whether the function is async
    pub is_async: bool,
}

/// Extracts browser FFI bindings from an AST module
pub struct BindingExtractor {
    bindings: Vec<BrowserBinding>,
}

impl BindingExtractor {
    pub fn new() -> Self {
        Self { bindings: Vec::new() }
    }

    /// Extract all @extern("browser", ...) bindings from a module
    pub fn extract(&mut self, module: &Module) -> &[BrowserBinding] {
        for item in &module.items {
            if let Node::Function(func_def) = item {
                if let Some(binding) = self.extract_from_function(func_def) {
                    self.bindings.push(binding);
                }
            } else if let Node::Class(class_def) = item {
                // Extract from class methods
                for func_def in &class_def.methods {
                    if let Some(binding) = self.extract_from_function(func_def) {
                        self.bindings.push(binding);
                    }
                }
            }
        }

        &self.bindings
    }

    /// Extract binding from a single function definition
    fn extract_from_function(&self, func_def: &FunctionDef) -> Option<BrowserBinding> {
        // Check for @extern decorator
        let extern_decorator = func_def
            .decorators
            .iter()
            .find(|d| matches!(&d.name, Expr::Identifier(name) if name == "extern"))?;

        // Extract arguments: @extern("browser", "console_log")
        let args = extern_decorator.args.as_ref()?;
        if args.len() < 2 {
            return None;
        }

        // First arg: module name
        let module = match &args[0].value {
            Expr::String(s) => s.clone(),
            _ => return None,
        };

        // Second arg: JS function name
        let js_name = match &args[1].value {
            Expr::String(s) => s.clone(),
            _ => return None,
        };

        // Extract parameters
        let params = func_def
            .params
            .iter()
            .map(|p| {
                (
                    p.name.clone(),
                    p.ty.clone().unwrap_or(Type::Simple("JsValue".to_string())),
                )
            })
            .collect();

        Some(BrowserBinding {
            simple_name: func_def.name.clone(),
            module,
            js_name,
            params,
            return_type: func_def.return_type.clone(),
            is_async: func_def.is_async(),
        })
    }

    /// Get all extracted bindings
    pub fn bindings(&self) -> &[BrowserBinding] {
        &self.bindings
    }
}

/// Generates wasm-bindgen code from browser bindings
pub struct BindgenCodeGenerator {
    bindings: Vec<BrowserBinding>,
}

impl BindgenCodeGenerator {
    pub fn new(bindings: Vec<BrowserBinding>) -> Self {
        Self { bindings }
    }

    /// Generate complete wasm-bindgen module
    pub fn generate(&self) -> String {
        let mut code = String::new();

        code.push_str("// Generated wasm-bindgen bindings for Simple browser FFI\n");
        code.push_str("use wasm_bindgen::prelude::*;\n\n");

        // Group bindings by module
        let mut by_module: HashMap<String, Vec<&BrowserBinding>> = HashMap::new();
        for binding in &self.bindings {
            by_module
                .entry(binding.module.clone())
                .or_insert_with(Vec::new)
                .push(binding);
        }

        // Generate extern blocks per module
        for (module, bindings) in by_module {
            code.push_str(&format!("// {} module bindings\n", module));
            code.push_str("#[wasm_bindgen]\n");
            code.push_str("extern \"C\" {\n");

            for binding in bindings {
                code.push_str(&self.generate_binding(binding));
                code.push('\n');
            }

            code.push_str("}\n\n");
        }

        code
    }

    /// Generate a single binding
    fn generate_binding(&self, binding: &BrowserBinding) -> String {
        let mut code = String::new();

        // Parse module path (e.g., "browser.console" -> namespace = console)
        let js_namespace = if binding.module.contains('.') {
            binding.module.split('.').last().unwrap()
        } else {
            &binding.module
        };

        // Add wasm_bindgen attribute
        code.push_str("    #[wasm_bindgen(");

        if js_namespace != "browser" {
            code.push_str(&format!("js_namespace = {}", js_namespace));
        }

        if binding.simple_name != binding.js_name {
            if js_namespace != "browser" {
                code.push_str(", ");
            }
            code.push_str(&format!("js_name = \"{}\"", binding.js_name));
        }

        code.push_str(")]\n");

        // Add async if needed
        if binding.is_async {
            code.push_str("    async ");
        }

        // Function signature
        code.push_str(&format!("    fn {}(", binding.simple_name));

        // Parameters
        let params: Vec<String> = binding
            .params
            .iter()
            .map(|(name, ty)| format!("{}: {}", name, self.type_to_js(ty)))
            .collect();
        code.push_str(&params.join(", "));

        code.push(')');

        // Return type
        if let Some(ret_ty) = &binding.return_type {
            code.push_str(" -> ");
            code.push_str(&self.type_to_js(ret_ty));
        }

        code.push(';');

        code
    }

    /// Convert Simple type to JavaScript/wasm-bindgen type
    fn type_to_js(&self, ty: &Type) -> String {
        match ty {
            Type::Simple(name) if name == "str" => "&str".to_string(),
            Type::Simple(name) if name == "i32" => "i32".to_string(),
            Type::Simple(name) if name == "i64" => "i64".to_string(),
            Type::Simple(name) if name == "f32" => "f32".to_string(),
            Type::Simple(name) if name == "f64" => "f64".to_string(),
            Type::Simple(name) if name == "bool" => "bool".to_string(),
            Type::Simple(name) if name == "Value" => "JsValue".to_string(),
            Type::Simple(name) if name == "()" => "()".to_string(),
            Type::Simple(name) => format!("&{}", name), // Reference for class types
            Type::Tuple(types) if types.is_empty() => "()".to_string(), // Empty tuple is unit type
            _ => "JsValue".to_string(),                 // Default to JsValue for complex types
        }
    }
}

/// JavaScript glue code generator for WASM module loading
pub struct JsGlueGenerator {
    wasm_module_name: String,
}

impl JsGlueGenerator {
    pub fn new(wasm_module_name: String) -> Self {
        Self { wasm_module_name }
    }

    /// Generate JavaScript loader code
    pub fn generate(&self) -> String {
        format!(
            r#"// Generated JavaScript glue code for Simple WASM module
// Load and initialize the WASM module

async function init() {{
    const wasm = await import('./{}.js');
    await wasm.default();
    return wasm;
}}

// Auto-initialize when loaded as module
const wasmPromise = init();

export default wasmPromise;
export {{ init }};
"#,
            self.wasm_module_name
        )
    }

    /// Generate HTML script tag for loading WASM
    pub fn generate_html_loader(&self) -> String {
        format!(
            r#"<script type="module">
    import init from './{}.js';

    async function run() {{
        const wasm = await init();
        console.log('WASM module loaded successfully');

        // Call exported main function if it exists
        if (wasm.main) {{
            wasm.main();
        }}
    }}

    run().catch(console.error);
</script>"#,
            self.wasm_module_name
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::*;
    use simple_parser::enums::*;
    use simple_parser::token::Span;

    fn create_extern_function(name: &str, module: &str, js_name: &str, is_async: bool) -> FunctionDef {
        let span = Span::new(0, 0, 0, 0);
        FunctionDef {
            span,
            name: name.to_string(),
            generic_params: vec![],
            params: vec![Parameter {
                span,
                name: "message".to_string(),
                ty: Some(Type::Simple("str".to_string())),
                default: None,
                mutability: Mutability::Immutable,
                inject: false,
                variadic: false,
                call_site_label: None,
            }],
            return_type: None,
            where_clause: WhereClause::default(),
            body: Block {
                statements: vec![],
                span,
            },
            visibility: Visibility::Public,
            effects: if is_async { vec![Effect::Async] } else { vec![] },
            decorators: vec![Decorator {
                span,
                name: Expr::Identifier("extern".to_string()),
                args: Some(vec![
                    Argument {
                        name: None,
                        value: Expr::String(module.to_string()),
                        span,
                        label: None,
                    },
                    Argument {
                        name: None,
                        value: Expr::String(js_name.to_string()),
                        span,
                        label: None,
                    },
                ]),
            }],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            is_me_method: false,
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: false,
            is_static: false,
            specialization_of: None,
            type_bindings: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn test_extract_browser_binding() {
        let func = create_extern_function("log", "browser", "console_log", false);
        let extractor = BindingExtractor::new();

        let binding = extractor.extract_from_function(&func).unwrap();

        assert_eq!(binding.simple_name, "log");
        assert_eq!(binding.module, "browser");
        assert_eq!(binding.js_name, "console_log");
        assert_eq!(binding.params.len(), 1);
        assert_eq!(binding.params[0].0, "message");
        assert!(!binding.is_async);
    }

    #[test]
    fn test_extract_async_binding() {
        let func = create_extern_function("fetch_get", "browser", "fetch", true);
        let extractor = BindingExtractor::new();

        let binding = extractor.extract_from_function(&func).unwrap();

        assert_eq!(binding.simple_name, "fetch_get");
        assert!(binding.is_async);
    }

    #[test]
    fn test_generate_bindgen_code() {
        let bindings = vec![BrowserBinding {
            simple_name: "log".to_string(),
            module: "browser".to_string(),
            js_name: "console_log".to_string(),
            params: vec![("message".to_string(), Type::Simple("str".to_string()))],
            return_type: None,
            is_async: false,
        }];

        let generator = BindgenCodeGenerator::new(bindings);
        let code = generator.generate();

        assert!(code.contains("#[wasm_bindgen]"));
        assert!(code.contains("fn log(message: &str);"));
    }

    #[test]
    fn test_type_conversion() {
        let generator = BindgenCodeGenerator::new(vec![]);

        assert_eq!(generator.type_to_js(&Type::Simple("str".to_string())), "&str");
        assert_eq!(generator.type_to_js(&Type::Simple("i32".to_string())), "i32");
        assert_eq!(generator.type_to_js(&Type::Simple("bool".to_string())), "bool");
        assert_eq!(generator.type_to_js(&Type::Simple("Value".to_string())), "JsValue");
        assert_eq!(generator.type_to_js(&Type::Simple("()".to_string())), "()");
        assert_eq!(generator.type_to_js(&Type::Tuple(vec![])), "()");
    }

    #[test]
    fn test_js_glue_generation() {
        let generator = JsGlueGenerator::new("my_app".to_string());
        let glue = generator.generate();

        assert!(glue.contains("import('./my_app.js')"));
        assert!(glue.contains("export default wasmPromise"));
    }

    #[test]
    fn test_html_loader_generation() {
        let generator = JsGlueGenerator::new("my_app".to_string());
        let html = generator.generate_html_loader();

        assert!(html.contains("<script type=\"module\">"));
        assert!(html.contains("import init from './my_app.js'"));
        assert!(html.contains("wasm.main()"));
    }
}
