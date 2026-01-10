# Simple Specification Catalog

**Generated:** $(date -u +"%Y-%m-%d %H:%M UTC")  
**Total Specs:** $(find "$TEST_DIR" -name "*_spec.spl" | wc -l)  
**Status:** ✅ All Passing

## Specification Index

### System Specifications

- **[Interpreter Bug Regressions](system/bugs/interpreter_bugs_spec.spl)** - 17 tests
- **[Doctest Advanced Parser](system/doctest/doctest_advanced_spec.spl)** - 3 tests
- **[DoctestMatcher](system/doctest/matcher/matcher_spec.spl)** - 1 tests
- **[DoctestParser](system/doctest/parser/parser_spec.spl)** - 1 tests
- **[DoctestRunner](system/doctest/runner/runner_spec.spl)** - 1 tests
- **[Feature Documentation Framework](system/feature_doc_spec.spl)** - 0 tests
- **[Gherkin DSL](system/gherkin/gherkin_spec.spl)** - 0 tests
- **[Parser Improvements - Working Features](system/improvements/parser_improvements_spec.spl)** - 13 tests
- **[String Method Improvements](system/improvements/stdlib_improvements_spec.spl)** - 17 tests
- **[Advanced Macro Features](system/macros/macro_advanced_spec.spl)** - 0 tests
- **[Basic Macros](system/macros/macro_basic_spec.spl)** - 0 tests
- **[Const-Eval Engine](system/macros/macro_consteval_simple_spec.spl)** - 0 tests
- **[Const-Eval Engine](system/macros/macro_consteval_spec.spl)** - 0 tests
- **[Macro Contracts](system/macros/macro_contracts_spec.spl)** - 0 tests
- **[Macro Edge Cases](system/macros/macro_errors_spec.spl)** - 0 tests
- **[Macro Hygiene](system/macros/macro_hygiene_spec.spl)** - 0 tests
- **[Intro Contracts](system/macros/macro_intro_spec.spl)** - 0 tests
- **[Macro System](system/macros/macro_system_spec.spl)** - 0 tests
- **[Template Substitution](system/macros/macro_templates_spec.spl)** - 0 tests
- **[Advanced Mixin Features](system/mixins/mixin_advanced_spec.spl)** - 10 tests
- **[Basic Mixin Declaration and Application](system/mixins/mixin_basic_spec.spl)** - 9 tests
- **[Mixin Composition](system/mixins/mixin_composition_spec.spl)** - 10 tests
- **[Generic Mixins](system/mixins/mixin_generic_spec.spl)** - 8 tests
- **[Mixin Type Inference](system/mixins/mixin_type_inference_spec.spl)** - 8 tests
- **[Generator Framework](system/property/generators_spec.spl)** - 0 tests
- **[Property Test Runner](system/property/runner_spec.spl)** - 0 tests
- **[Shrinking Algorithm](system/property/shrinking_spec.spl)** - 0 tests
- **[SDN CLI System Tests](system/sdn/cli_spec.spl)** - 0 tests
- **[SDN File I/O System Tests](system/sdn/file_io_spec.spl)** - 0 tests
- **[SDN Fixtures System Tests](system/sdn/fixtures_spec.spl)** - 11 tests
- **[SDN Workflow System Tests](system/sdn/workflow_spec.spl)** - 0 tests
- **[Snapshot Testing Framework](system/snapshot/basic_spec.spl)** - 0 tests
- **[Snapshot Comparison](system/snapshot/comparison_spec.spl)** - 0 tests
- **[Snapshot Formats](system/snapshot/formats_spec.spl)** - 0 tests
- **[Snapshot Test Runner](system/snapshot/runner_spec.spl)** - 0 tests
- **[Architecture Testing](system/spec/arch_spec.spl)** - 0 tests
- **[](system/spec/feature_doc_spec.spl)** - 0 tests
- **[BDD Matchers](system/spec/matchers/spec_matchers_spec.spl)** - 17 tests
- **[BDD Spec Framework](system/spec/spec_framework_spec.spl)** - 31 tests
- **[Mixin + Static Polymorphism Integration](system/static_poly/mixin_integration_spec.spl)** - 10 tests
- **[Static Polymorphism](system/static_poly/static_polymorphism_spec.spl)** - 12 tests
- **[DAP Event Handling](system/tools/dap_spec.spl)** - 25 tests
- **[LSP Protocol Basics](system/tools/lsp_spec.spl)** - 20 tests

### Integration Specifications

- **[Console Framework](integration/console/console_basic_spec.spl)** - 0 tests
- **[Call Flow Profiling](integration/diagram/call_flow_profiling_spec.spl)** - 1 tests
- **[Diagram Generation](integration/diagram/diagram_gen_spec.spl)** - 9 tests
- **[Diagram Integration](integration/diagram/diagram_integration_spec.spl)** - 11 tests
- **[Doctest Discovery](integration/doctest/discovery_spec.spl)** - 1 tests
- **[Macro Integration](integration/macros/macro_integration_spec.spl)** - 0 tests
- **[Simple Math: @ matrix multiplication operator](integration/ml/simple_math_integration_spec.spl)** - 0 tests
- **[Screenshot FFI](integration/screenshot/screenshot_ffi_spec.spl)** - 11 tests
- **[Ratatui Backend FFI](integration/ui/tui/ratatui_backend_spec.spl)** - 0 tests
- **[Vulkan Window Management](integration/ui/vulkan_window_spec.spl)** - 31 tests

### Unit Specifications

- **[CLI Library](unit/cli_spec.spl)** - 0 tests
- **[Actor Body Execution](unit/concurrency/actor_body_spec.spl)** - 3 tests
- **[Concurrency](unit/concurrency/concurrency_spec.spl)** - 32 tests
- **[Manual Mode Execution](unit/concurrency/manual_mode_spec.spl)** - 8 tests
- **[Promise[T] - Basic Operations](unit/concurrency/promise_spec.spl)** - 30 tests
- **[Contract System](unit/contracts/contracts_spec.spl)** - 1 tests
- **[Arithmetic](unit/core/arithmetic_spec.spl)** - 10 tests
- **[#[inline] attribute](unit/core/attributes_spec.spl)** - 0 tests
- **[Option Type](unit/core/collections_spec.spl)** - 33 tests
- **[Comparisons](unit/core/comparison_spec.spl)** - 14 tests
- **[ContextManager trait](unit/core/context_spec.spl)** - 0 tests
- **[@cached decorator](unit/core/decorators_spec.spl)** - 0 tests
- **[Context blocks](unit/core/dsl_spec.spl)** - 0 tests
- **[Fluent Interface Support](unit/core/fluent_interface_spec.spl)** - 0 tests
- **[Hello](unit/core/hello_spec.spl)** - 0 tests
- **[JSON module](unit/core/json_spec.spl)** - 29 tests
- **[Math module](unit/core/math_spec.spl)** - 0 tests
- **[Exhaustiveness checking](unit/core/pattern_analysis_spec.spl)** - 0 tests
- **[Pattern Matching](unit/core/pattern_matching_spec.spl)** - 79 tests
- **[Primitives](unit/core/primitives_spec.spl)** - 6 tests
