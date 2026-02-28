#[test]
fn test_as_cast_in_func_args() {
    // Test parsing the actual failing files with minimal reproduction
    let base = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let test_files = [
        "src/compiler/35.semantics/semantics/cast_rules.spl",
        "src/compiler/99.loader/loader/compiler_ffi.spl",
        "src/compiler/30.types/type_system/effects.spl",
        "src/compiler/70.backend/inline_asm.spl",
        "src/compiler/99.loader/loader/smf_mmap_native.spl",
        "src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl",
        "src/compiler/90.tools/aop_proceed.spl",
        "src/compiler/55.borrow/gc_analysis/roots.spl",
        "src/compiler/60.mir_opt/optimization_passes.spl",
        "src/compiler/40.mono/monomorphize/deferred_deserialize.spl",
        "src/compiler/40.mono/monomorphize/deferred.spl",
        "src/compiler/00.common/predicate_parser.spl",
    ];
    for f in &test_files {
        let path = base.join(f);
        let src = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("  {f}: READ ERROR: {e}");
                continue;
            }
        };
        let mut parser = simple_parser::Parser::new(&src);
        match parser.parse() {
            Ok(_) => eprintln!("  {f}: OK"),
            Err(e) => {
                let (line, col) = match &e {
                    simple_parser::ParseError::UnexpectedToken { span, .. } => (span.line, span.column),
                    simple_parser::ParseError::SyntaxError { line, column, .. } => (*line, *column),
                    _ => (0, 0),
                };
                eprintln!("  {f}:{line}:{col}: {e}");
            }
        }
    }
}

#[test]
fn debug_match_in_val() {
    // Test: match as expression in val binding with multi-line args
    let src = r#"fn foo(intro):
    val sym = match intro.kind:
        case "fn":
            do_fn(name: name, params: [],
                return_type: intro.type_pattern)
        case "field":
            do_field()
    print sym
"#;
    let mut parser = simple_parser::Parser::new(src);
    match parser.parse() {
        Ok(_) => eprintln!("match_in_val: OK"),
        Err(e) => {
            let (line, col) = match &e {
                simple_parser::ParseError::UnexpectedToken { span, .. } => (span.line, span.column),
                simple_parser::ParseError::SyntaxError { line, column, .. } => (*line, *column),
                _ => (0, 0),
            };
            eprintln!("match_in_val ERROR at {line}:{col}: {e}");
        }
    }
}

#[test]
fn debug_specific_files() {
    let base = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();

    let files = [
        "src/compiler/70.backend/inline_asm.spl",
        "src/compiler/70.backend/irdsl/codegen.spl",
        "src/compiler/70.backend/backend/x86_asm.spl",
        "src/compiler/90.tools/verify/main.spl",
        "src/compiler/90.tools/verify/project_gen.spl",
        "src/compiler/00.common/error.spl",
        "src/compiler/10.frontend/parser/doc_gen.spl",
        "src/compiler/10.frontend/parser/test_analyzer.spl",
        "src/compiler/90.tools/depgraph/scanner.spl",
        "src/compiler/10.frontend/core/interpreter/hashmap.spl",
        "src/compiler/99.loader/module_resolver/types.spl",
        "src/compiler/70.backend/backend/c_backend.spl",
        "src/compiler/80.driver/driver/incremental.spl",
        "src/compiler/70.backend/backend/backend_factory_full.spl",
        "src/compiler/70.backend/backend/common/expression_evaluator.spl",
        "src/compiler/10.frontend/core/interpreter/jit.spl",
        "src/compiler/90.tools/ffi_gen/specs/cranelift_core.spl",
        "src/compiler/90.tools/ffi_gen/types.spl",
        "src/compiler/90.tools/perf/benchmark.spl",
        "src/compiler/90.tools/perf/profiler.spl",
        "src/compiler/00.common/parallel.spl",
        "src/compiler/80.driver/build_log.spl",
        "src/compiler/10.frontend/parser/partial.spl",
        "src/compiler/10.frontend/parser/recovery.spl",
        "src/compiler/10.frontend/parser/macro_registry.spl",
        "src/compiler/80.driver/driver_types.spl",
        "src/compiler/10.frontend/desugar/placeholder_lambda.spl",
        "src/compiler/99.loader/loader/module_loader.spl",
        "src/compiler/99.loader/loader/compiler_ffi.spl",
        "src/compiler/35.semantics/error_formatter.spl",
        "src/compiler/90.tools/fix/rules/rules.spl",
        "src/compiler/40.mono/monomorphize/deferred.spl",
        "src/compiler/90.tools/fix/main.spl",
        "src/compiler/90.tools/fix/rules/helpers.spl",
        "src/compiler/90.tools/fix/rules/impl/lint_spec.spl",
        "src/compiler/95.interp/interpreter/pattern.spl",
        "src/compiler/99.loader/loader/smf_cache.spl",
        "src/compiler/99.loader/loader/smf_mmap_native.spl",
        "src/compiler/30.types/bidirectional_types.spl",
        "src/compiler/30.types/type_system/effects.spl",
        "src/compiler/35.semantics/semantics/binary_ops.spl",
        "src/compiler/35.semantics/semantics/cast_rules.spl",
        "src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl",
        "src/compiler/80.driver/compilability.spl",
        "src/compiler/50.mir/mir/ghost_erasure.spl",
        "src/compiler/90.tools/aop_proceed.spl",
        "src/compiler/70.backend/codegen_enhanced.spl",
        "src/compiler/55.borrow/gc_analysis/roots.spl",
        "src/compiler/60.mir_opt/optimization_passes.spl",
        "src/compiler/40.mono/monomorphize/deferred_deserialize.spl",
    ];

    for f in &files {
        let path = base.join(f);
        let src = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("  {f}: READ ERROR: {e}");
                continue;
            }
        };
        let mut parser = simple_parser::Parser::new(&src);
        match parser.parse() {
            Ok(_) => eprintln!("  {f}: OK"),
            Err(e) => {
                let (line, col) = match &e {
                    simple_parser::ParseError::UnexpectedToken { span, .. } => (span.line, span.column),
                    simple_parser::ParseError::SyntaxError { line, column, .. } => (*line, *column),
                    _ => (0, 0),
                };
                eprintln!("  {f}:{line}:{col}: {e}");
            }
        }
    }
}

#[test]
fn debug_timeout_files() {
    use std::time::Instant;
    use simple_compiler::codegen::Codegen;
    use simple_compiler::hir::Lowerer;
    use simple_compiler::module_resolver::ModuleResolver;
    use simple_compiler::monomorphize::monomorphize_module;

    let base = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();

    let files = ["src/compiler/30.types/const_keys.spl"];

    for f in &files {
        let path = base.join(f);
        let src = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("  {f}: READ ERROR: {e}");
                continue;
            }
        };

        eprintln!("  {f}: starting parse...");
        let t0 = Instant::now();
        let mut parser = simple_parser::Parser::new(&src);
        let ast = match parser.parse() {
            Ok(a) => a,
            Err(e) => {
                eprintln!("  {f}: PARSE ERROR: {e}");
                continue;
            }
        };
        let parse_ms = t0.elapsed().as_millis();

        eprintln!("  {f}: parse done ({parse_ms}ms), starting mono...");
        let t1 = Instant::now();
        let ast = monomorphize_module(&ast);
        let mono_ms = t1.elapsed().as_millis();

        eprintln!("  {f}: mono done ({mono_ms}ms), starting hir...");
        let t2 = Instant::now();
        let source_root = base.join("src");
        let resolver = ModuleResolver::new(base.clone(), source_root);
        let mut lowerer = Lowerer::with_module_resolver(resolver, path.clone());
        lowerer.set_strict_mode(false);
        lowerer.set_lenient_types(true);
        let hir = match lowerer.lower_module(&ast) {
            Ok(h) => h,
            Err(e) => {
                eprintln!("  {f}: parse={parse_ms}ms mono={mono_ms}ms HIR ERROR: {e}");
                continue;
            }
        };
        let hir_ms = t2.elapsed().as_millis();

        eprintln!("  {f}: hir done ({hir_ms}ms), starting mir...");
        let t3 = Instant::now();
        let mir = match simple_compiler::mir::lower_to_mir(&hir) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("  {f}: parse={parse_ms}ms mono={mono_ms}ms hir={hir_ms}ms MIR ERROR: {e}");
                continue;
            }
        };
        let mir_ms = t3.elapsed().as_millis();

        eprintln!("  {f}: mir done ({mir_ms}ms), starting codegen...");
        let t4 = Instant::now();
        let codegen = match Codegen::new() {
            Ok(c) => c,
            Err(e) => {
                eprintln!("  {f}: codegen init error: {e}");
                continue;
            }
        };
        let obj = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| codegen.compile_module(&mir)));
        let codegen_ms = t4.elapsed().as_millis();

        match obj {
            Ok(Ok(bytes)) => eprintln!("  {f}: parse={parse_ms}ms mono={mono_ms}ms hir={hir_ms}ms mir={mir_ms}ms codegen={codegen_ms}ms obj={}KB OK", bytes.len()/1024),
            Ok(Err(e)) => eprintln!("  {f}: parse={parse_ms}ms mono={mono_ms}ms hir={hir_ms}ms mir={mir_ms}ms codegen={codegen_ms}ms ERROR: {e}"),
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<String>() { s.clone() }
                    else if let Some(s) = e.downcast_ref::<&str>() { s.to_string() }
                    else { "unknown panic".to_string() };
                eprintln!("  {f}: parse={parse_ms}ms mono={mono_ms}ms hir={hir_ms}ms mir={mir_ms}ms codegen={codegen_ms}ms PANIC: {msg}");
            }
        }
    }
}
