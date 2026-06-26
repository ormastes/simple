# Test Specification Index

*Generated: 2026-04-07 06:36:11*

## Quick Stats

- **Total Features:** 238
- **Complete Documentation:** 238 (100%)
- **Stubs Remaining:** 0
- **Total Lines:** 7365
- **Warnings:** 421

---

## Bare-Metal / Architecture (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Target Architecture Specification](target_arch_spec.md) | In Progress | Thin | 2/5 | 56 | Multi-architecture support for bare-metal development including: |

## Bare-Metal / Drivers (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Serial Port Driver Specification](serial_driver_spec.md) | In Progress | Thin | 2/5 | 40 | UART serial driver for bare-metal systems supporting: |

## Bare-Metal / x86 (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [x86 Bare-Metal Boot Specification](x86_boot_spec.md) | In Progress | Thin | N/A | 21 | Tests for the x86 bare-metal boot infrastructure including: |

## Codegen (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Generator State Machine Codegen Specification](generator_state_machine_codegen_spec.md) | In Progress | Needs detail | 4/5 | 8 | Generator state machine codegen provides optimized code generation for generator functions that implement explicit stat… |

## Compiler (13 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Aop Debug Log Specification](aop_debug_log_spec.md) | Active | Thin | N/A | 16 | AOP Debug Logger |
| [DI Error Cases](di_error_cases_spec.md) | In Progress | Thin | N/A | 22 | Tests the failure paths and edge cases of the DiContainer dependency injection system. Covers locked container behavior… |
| [DI Extensions Feature](di_extensions_feature_spec.md) | In Progress | Thin | N/A | 31 | Tests the DI Extension Container (CompileContext.extensions) which provides a dynamic plugin/extension registration poi… |
| [DI Lock Feature](di_lock_feature_spec.md) | Active | Thin | N/A | 29 | Tests the DiContainer lock/unlock mechanism across all phases: lock state transitions, locked behavior that rejects new… |
| [DI System Test Lock - All Phases](di_lock_all_phases_spec.md) | Active | Thin | N/A | 31 | Comprehensive phase tests for the DI system test lock feature covering all five phases: lock state transitions (lock/un… |
| [Generic Template Bytecode in SMF](generic_bytecode_spec.md) | In Progress | Thin | N/A | 1 | Tests storage of generic function templates in the SMF (Simple Module Format) bytecode format. |
| [Hindley-Milner Type Inference](hm_type_inference_spec.md) | In Progress | Thin | N/A | 15 | Tests core Hindley-Milner type inference with level-based generalization. Implements simplified type variables, substit… |
| [Multi-Architecture Support](architecture_spec.md) | In Progress | Thin | N/A | 27 | Tests multi-architecture support across 8-bit, 16-bit, 32-bit, and 64-bit targets including AVR, MCS51, MSP430, x86, AR… |
| [SMF note.sdn Instantiation Tracking](note_sdn_feature_spec.md) | In Progress | Thin | N/A | 1 | Tests the note.sdn section in SMF (Simple Module Format) for tracking generic instantiation metadata. The feature enabl… |
| [Static Method Resolution](static_method_resolution_spec.md) | Active | Thin | N/A | 11 | Tests static method resolution and calling in interpreter mode. Uses ClassName.method() dot-access syntax which works i… |
| [VHDL Backend Toolchain](vhdl_spec.md) | In Progress | Thin | N/A | 12 | Tests VHDL backend toolchain integration with GHDL and Yosys. Covers GHDL availability detection, VHDL source analysis… |
| [VHDL Golden File Tests](vhdl_golden_spec.md) | Active | Thin | N/A | 5 | Generates VHDL output from the VhdlBuilder and compares against checked-in reference .vhd golden files for regression t… |
| [WASM Compilation Integration](wasm_compile_spec.md) | Active | Thin | N/A | 36 | End-to-end tests for compiling Simple programs to WebAssembly. Tests backend selection for wasm32/wasm64 targets, WasmB… |

## Compiler Backend (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [GPU PTX Code Generation Specification](gpu_ptx_gen_spec.md) | In Progress | Thin | 4/5 | 81 | PTX code generation tests verify that the CUDA backend correctly translates MIR instructions to NVIDIA PTX assembly. Th… |

## Concurrency (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Concurrency Primitives Specification](concurrency_primitives_spec.md) | In Progress | Thin | N/A | 5 | Concurrency Primitives Specification |

## Functional Programming (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Curry Partial Specification](curry_partial_spec.md) | Active | Thin | N/A | 10 | Curry and Partial Application |

## GPU & SIMD (2 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [GPU Kernel Compilation](gpu_kernel_compilation_spec.md) | In Progress | Thin | N/A | 23 | Tests that @gpu_kernel functions are properly lowered through HIR -> MIR and compiled to PTX with .entry directives. Va… |
| [GPU Kernel Launch](gpu_kernel_launch_spec.md) | In Progress | Thin | N/A | 8 | Tests actual GPU kernel launch, device memory allocation, data transfer, and result verification. Covers CUDA device av… |

## Infrastructure (13 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Contract Persistence - File I/O](contract_persistence_feature_spec.md) | Active | Thin | N/A | 6 | Tests consumer-driven contract persistence including serialization to Pact-compatible JSON format, saving contracts to… |
| [Extended File I/O Specification](file_io_extended_spec.md) | Implemented | Thin | N/A | 20 | Extended File I/O operations including line-based reading, append operations, |
| [Feature Completion Tracking Specification](feature_done_spec.md) | Implemented | Thin | N/A | 8 | This specification documents the living documentation pattern where features |
| [Interpreter Interface Specification](interpreter_interface_spec.md) | Implemented | Thin | N/A | 9 | The interpreter interface defines how the Simple language runtime executes code, manages |
| [LLVM Backend AArch64 Specification](llvm_backend_aarch64_spec.md) | In Progress | Thin | 3/5 | 10 | Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets. |
| [LLVM Backend ARM 32-bit Specification](llvm_backend_arm32_spec.md) | In Progress | Thin | 3/5 | 10 | Validates that the LLVM backend correctly generates code for ARM 32-bit (ARMv7) targets. |
| [LLVM Backend Codegen Specification](llvm_backend_spec.md) | In Progress | Thin | 5/5 | 32 | The LLVM backend provides high-performance native code generation for the Simple language |
| [LLVM Backend RISC-V 32-bit Specification](llvm_backend_riscv32_spec.md) | In Progress | Thin | 3/5 | 8 | Validates that the LLVM backend correctly generates code for RISC-V 32-bit targets. |
| [LLVM Backend RISC-V 64-bit Specification](llvm_backend_riscv64_spec.md) | In Progress | Thin | 3/5 | 8 | Validates that the LLVM backend correctly generates code for RISC-V 64-bit targets. |
| [LLVM Backend i686 (x86 32-bit) Specification](llvm_backend_i686_spec.md) | In Progress | Thin | 3/5 | 10 | Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets. |
| [Minimal Test Spec](minimal_spec.md) | Active | Thin | N/A | 2 | A minimal smoke test that verifies the test runner can load a spec file with a basic describe/it block and execute a tr… |
| [Pipeline Components Specification](pipeline_components_spec.md) | Implemented | Thin | N/A | 17 | Pipeline components provide a composable way to build data processing pipelines. |
| [Resource Cleanup Framework](resource_cleanup_spec.md) | In Progress | Thin | N/A | 15 | Tests the unified resource cleanup framework including the Resource trait (close, is_open, resource_name), ResourceRegi… |

## Infrastructure | Macros (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Macro Validation Specification](macro_validation_spec.md) | Implemented | Thin | N/A | 14 | Tests that macros can be validated without full expansion in LL(1) parsing: |

## Infrastructure | Parser (17 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Match Expression Separator Specification](parser_match_expression_spec.md) | In Progress | Thin | N/A | 9 | The runtime has two match parsers: |
| [Parser Declaration Specification](parser_declarations_spec.md) | Implemented | Thin | N/A | 38 | Tests that the parser correctly parses declaration statements including |
| [Parser Deprecation Warnings Specification](parser_deprecation_warnings_spec.md) | Implemented | Thin | N/A | 31 | Tests that the parser correctly emits deprecation warnings for |
| [Parser Error Recovery Specification](parser_error_recovery_spec.md) | Implemented | Thin | N/A | 38 | Tests the parser's ability to detect common mistakes from other |
| [Parser Expression Specification](parser_expressions_spec.md) | Implemented | Thin | N/A | 55 | Tests that the parser correctly parses various expression forms including |
| [Parser Function Definition Specification](parser_functions_spec.md) | Implemented | Thin | N/A | 33 | Tests that the parser correctly parses function definitions including |
| [Parser Keywords Specification](parser_keywords_spec.md) | Implemented | Thin | N/A | 22 | Tests that all Simple language keywords are correctly recognized and |
| [Parser Literal Tokenization Specification](parser_literals_spec.md) | Implemented | Thin | N/A | 55 | Tests that the parser correctly tokenizes and parses various literal types |
| [Parser Operator Specification](parser_operators_spec.md) | Implemented | Thin | N/A | 48 | Tests that the parser correctly tokenizes and parses all operators |
| [Parser Syntax Validation Specification](parser_syntax_validation_spec.md) | Implemented | Thin | N/A | 36 | Tests that the parser correctly validates syntax and provides helpful |
| [Parser Type Annotations Specification](parser_type_annotations_spec.md) | Implemented | Thin | N/A | 33 | Tests that the parser correctly parses type annotations including |
| [TreeSitter Advanced Outline Parsing Specification](treesitter_query_spec.md) | Implemented | Thin | N/A | 10 | Tests advanced outline features: type parameters, traits, impls, |
| [TreeSitter Error Handling and Edge Cases Specification](treesitter_error_recovery_spec.md) | Implemented | Thin | N/A | 15 | Tests error handling and edge cases in the compiler.treesitter outline parser, |
| [TreeSitter Heuristic Mode Specification](treesitter_cursor_spec.md) | Implemented | Thin | N/A | 13 | Tests heuristic (line-based) parsing mode of the TreeSitter parser. |
| [TreeSitter Lexer Specification](treesitter_lexer_spec.md) | Implemented | Thin | N/A | 29 | Tests the core.lexer tokenization used by compiler.treesitter, |
| [TreeSitter OutlineModule Structure Specification](treesitter_tree_spec.md) | Implemented | Thin | N/A | 14 | Tests that TreeSitter parses source into correct OutlineModule structure, |
| [TreeSitter Parser Specification](treesitter_parser_spec.md) | Implemented | Thin | N/A | 13 | Tests the basic TreeSitter.new(source).parse_outline() workflow, |

## Language (42 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [AOP Architecture Rules Specification](aop_architecture_rules_spec.md) | Implemented | Thin | N/A | 27 | Architecture rules enforce structural constraints on the codebase using the same |
| [AOP Pointcut Expression Specification](aop_pointcut_spec.md) | In Progress | Thin | N/A | 12 | Pointcut expressions define where advice should be applied. The `pc{...}` syntactic |
| [Access Control with Visibility Modifiers](visibility_modifiers_spec.md) | Planned | Thin | N/A | 1 | Visibility modifiers (`public`, `private`, `protected`) control which scopes may access a given struct field, class met… |
| [Array Type System and Operations](array_types_spec.md) | Active | Thin | N/A | 30 | Arrays are Simple's primary ordered collection type, supporting literal construction, positive and negative indexing, s… |
| [Aspect-Oriented Programming (AOP) Specification](aop_spec.md) | In Progress | Thin | N/A | 21 | Aspect-Oriented Programming (AOP) enables cross-cutting concern separation through |
| [Automatic Type Annotation Conversion](type_conversion_spec.md) | In Progress | Thin | N/A | 1 | Type annotation conversion allows a value to be automatically converted to a specified target type when the annotation… |
| [Context Managers Specification](context_managers_spec.md) | Implemented | Thin | N/A | 14 | Context managers provide a way to safely acquire and release resources using |
| [Control Flow - If/Else Specification](control_flow_if_else_spec.md) | In Progress | Thin | N/A | 11 | Tests for conditional control flow using if/else statements. |
| [Dictionary Types Specification](dictionary_types_spec.md) | In Progress | Thin | N/A | 23 | Tests for dictionary (map) types and their operations. |
| [Elif Val/Var Pattern Binding Specification](elif_val_pattern_binding_spec.md) | Implemented | Thin | N/A | 20 | Tests for `elif val`/`elif var` pattern binding in conditional branches. Verifies that pattern matching works correctly… |
| [Enum Types Specification](enums_spec.md) | Complete | Thin | N/A | 21 | Tests for enumeration types and pattern matching on enums. |
| [Fixed-Size Array Edge Cases and Boundary Conditions](fixed_size_edge_cases_spec.md) | Active | Thin | N/A | 10 | This spec exercises the boundary conditions and edge cases of fixed-size arrays that go beyond typical usage. It tests… |
| [Fixed-Size Array Types](fixed_size_arrays_spec.md) | Active | Thin | N/A | 13 | Fixed-size arrays use the `[T; N]` syntax to declare arrays whose length is known at declaration time and enforced at r… |
| [Format String Instantiation Specification](format_string_with_spec.md) | Implemented | Needs detail | 3/5 | 11 | Format strings allow defining reusable string patterns with placeholders that are filled in later using the `.with` met… |
| [Freeze and Unfreeze Collections for Immutability](freeze_unfreeze_spec.md) | Active | Thin | N/A | 21 | The `freeze()` function converts mutable collections (arrays and dicts) into immutable snapshots that support read oper… |
| [Function Definitions Specification](functions_spec.md) | In Progress | Thin | N/A | 19 | Tests for function definition and invocation. |
| [Generic Types Specification](generics_spec.md) | In Progress | Thin | N/A | 28 | Tests for generic type parameters and constraints. |
| [Handle Pointers Specification](handle_pointers_spec.md) | Implemented | Thin | N/A | 9 | Handle pointers provide safe, reusable references to i64 values via a slot table with generation counters. Freed slots… |
| [Implementation Blocks Specification](impl_blocks_spec.md) | Implemented | Thin | 2/5 | 6 | Implementation blocks (`impl`) provide a flexible way to define methods for types outside of the type definition. This… |
| [Implicit Context Parameters](implicit_context_spec.md) | Active | Thin | N/A | 8 | Tests implicit context parameters declared with `context val` and bound with `with_context`. Verifies that context vari… |
| [In-Place Functional Update with the Arrow Operator](functional_update_spec.md) | Active | Thin | N/A | 11 | The functional update operator `->` applies transformations to collections in place, enabling fluent data processing pi… |
| [Lambdas and Closures Specification](lambdas_closures_spec.md) | Implemented | Thin | N/A | 13 | Lambdas (anonymous functions) and closures enable functional programming patterns. |
| [Macros Specification](macros_spec.md) | Planned | Thin | 4/5 | 3 | Tests for the macro system including macro definitions, expansions, hygiene, and integration with the compiler's metapr… |
| [Method Missing Handler Specification](method_missing_spec.md) | Planned | Thin | 3/5 | 3 | Tests for the method_missing dynamic dispatch mechanism that allows objects to handle calls to undefined methods at run… |
| [Module Visibility Specification](module_visibility_spec.md) | In Progress (Core Complete, Integration Pending) | Needs detail | 3/5 | 26 | Module visibility system with filename-based auto-public rule. Types matching the filename are automatically public; al… |
| [Mutability Control Specification](mutability_control_spec.md) | Planned | Thin | 3/5 | 3 | Tests for mutability control mechanisms including mutable and immutable references, capability-based access control, an… |
| [Mutable Collections by Default](mutable_by_default_spec.md) | Active | Thin | N/A | 24 | Simple follows the design decision that collections (arrays and dicts) are mutable by default, consistent with Python,… |
| [Option Type Specification](option_type_spec.md) | Implemented | Thin | 2/5 | 8 | Tests for the Option type representing values that may or may not be present, including constructors, pattern matching,… |
| [Pass Keyword Variants](pass_variants_spec.md) | Active | Thin | N/A | 20 | Tests the enhanced pass keyword with semantic distinctions: `pass_todo` for unimplemented code markers, `pass_do_nothin… |
| [Pass Statement and Unit Value Equivalence](pass_unit_equivalence_spec.md) | Active | Thin | N/A | 5 | In Simple, the `pass` keyword and the unit literal `()` are semantically equivalent -- both represent a deliberate no-o… |
| [Pattern Matching Specification](pattern_matching_spec.md) | Implemented | Thin | N/A | 11 | Pattern matching provides a way to extract and deconstruct values using patterns. |
| [Scoped Context Blocks for Resource Management](context_blocks_spec.md) | In Progress | Thin | N/A | 8 | Context blocks provide scoped execution environments that guarantee setup and teardown semantics, similar to Python's `… |
| [Structs Specification](structs_spec.md) | Implemented | Thin | 2/5 | 10 | Structs are user-defined data types that group related fields together. They support named fields with type annotations… |
| [Target-Based Mutability Defaults](target_defaults_spec.md) | In Progress | Thin | N/A | 2 | Simple supports target-based compilation modes that change the default mutability of collections. In the general (defau… |
| [Trait Alias Forwarding](trait_forwarding_spec.md) | Active | Thin | N/A | 8 | Tests the delegation pattern generated by the desugar pass from `alias TraitName = field_name` inside class bodies. Val… |
| [Trait Keyword - All Phases](trait_keyword_all_phases_spec.md) | Active | Thin | N/A | 39 | Comprehensive phase tests for the trait keyword feature covering all five phases: trait definition with method signatur… |
| [Traits Specification](traits_spec.md) | Implemented | Thin | 3/5 | 17 | Traits define shared behavior that types can implement, enabling polymorphism and code reuse. They are similar to inter… |
| [Tuple Types Specification](tuple_types_spec.md) | Implemented | Thin | 2/5 | 8 | Tuple types are ordered collections of heterogeneous values with fixed length. They allow grouping multiple values of d… |
| [Type Aliases Specification](type_aliases_spec.md) | Implemented | Thin | 2/5 | 11 | Type aliases allow creating alternative names for existing types, improving code readability and maintainability. They… |
| [Type Inference Specification](type_inference_spec.md) | Implemented | Needs detail | 4/5 | 29 | Type inference automatically deduces types for variables, function parameters, and return values without explicit type… |
| [Union Type Declarations and Discrimination](union_types_spec.md) | Planned | Thin | N/A | 1 | Union types allow a variable to hold a value of one of several specified types, written as `A \| B`. At runtime the lang… |
| [Variables and Bindings Specification](variables_let_bindings_spec.md) | Implemented | Thin | N/A | 23 | Tests for variable declarations including val (immutable) and var (mutable) bindings, type inference, and scoping rules. |

## Language Features (7 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Bitfield Feature Plan](bitfield_spec.md) | In Progress | Thin | N/A | 4 | Tests the bitfield feature plan by verifying parser phase scope, validation phase scope, and coverage path tracking. En… |
| [Bitfield Runtime Compatibility](bitfield_runtime_compat_spec.md) | In Progress | Thin | N/A | 1 | Tests that real bitfield syntax is accepted and parsed correctly in the feature test path. Validates a basic bitfield d… |
| [Custom Literal Syntax](custom_literal_spec.md) | In Progress | Thin | N/A | 3 | Tests the custom collection literal syntax, specifically the `s{...}` prefix for set literals. Verifies that set litera… |
| [Dual Argument Syntax](parser_dual_argument_syntax_spec.md) | In Progress | Thin | N/A | 32 | Tests support for both ':' and '=' as argument assignment syntax in all contexts. Covers function calls (colon, equals,… |
| [Method Reference Syntax](method_reference_spec.md) | In Progress | Thin | N/A | 8 | Tests the `&:method` syntax which creates a lambda that calls the given method on its argument (inspired by Ruby's Symb… |
| [Nested Placeholder Scoping](nested_placeholder_spec.md) | In Progress | Thin | N/A | 9 | Tests that placeholder lambdas in nested call arguments maintain independent scoping at each nesting level. Verifies th… |
| [Numbered Placeholder Lambda Expressions](numbered_placeholder_spec.md) | In Progress | Thin | N/A | 13 | Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit parameter ordering in lambda shorthand.… |

## Language | CLI (11 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [CLI Args Basic Specification](cli_args_basic_spec.md) | Draft | Thin | N/A | 8 | Tests for the `cli` keyword basic functionality: bool flags, string options, int options, and default values. The `cli`… |
| [CLI Args Default Command Specification](cli_args_default_spec.md) | Draft | Thin | N/A | 4 | Tests default command behavior when no subcommand is specified. A cli block can define a default action that runs when… |
| [CLI Args Error Handling Specification](cli_args_error_spec.md) | Draft | Thin | N/A | 8 | Tests compile-time and runtime error cases for the cli keyword. The compiler should catch invalid cli blocks at compile… |
| [CLI Args File Extension Detection Specification](cli_args_file_spec.md) | Draft | Thin | N/A | 6 | Tests file extension detection and the prefetch directive in the cli keyword. When a positional argument ends with a re… |
| [CLI Args Help Text Specification](cli_args_help_spec.md) | Draft | Thin | N/A | 6 | Tests automatic help text generation from docstrings and option metadata. The cli keyword generates --help output inclu… |
| [CLI Args Inference Rules Specification](cli_args_inference_spec.md) | Draft | Thin | N/A | 6 | Tests the type inference rules and struct shape validation for the cli keyword. The compiler generates a typed struct f… |
| [CLI Args Migration Compatibility Specification](cli_args_migration_spec.md) | Draft | Thin | N/A | 4 | Tests compatibility between the new cli keyword and the existing manual argument parsing pattern. Projects using manual… |
| [CLI Args Short Names Specification](cli_args_short_spec.md) | Draft | Thin | N/A | 8 | Tests short name generation and explicit short name overrides for CLI options. The cli keyword auto-generates single-ch… |
| [CLI Args Subcommand Specification](cli_args_subcommand_spec.md) | Draft | Thin | N/A | 10 | Tests subcommand dispatch with the `cli` keyword. Subcommands allow grouping related functionality under named commands… |
| [CLI Args Type Inference Specification](cli_args_types_spec.md) | Draft | Thin | N/A | 10 | Tests type inference from default values in the `cli` keyword block. The compiler infers the type of each option from i… |
| [CLI Args mod.spl Embedding Specification](cli_args_modspl_spec.md) | Draft | Thin | N/A | 4 | Tests embedding the cli keyword in mod.spl module files. When a module's mod.spl contains a cli block, the module becom… |

## Language | Classes (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Classes and Object-Oriented Programming Specification](classes_spec.md) | Implemented | Thin | N/A | 23 | Tests for class definitions, instance creation, field access, methods, impl blocks, context blocks, method_missing, aut… |

## Language | Collections (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Collections Specification](collections_spec.md) | Implemented | Thin | N/A | 54 | Tests for collection types including arrays, tuples, dictionaries, and strings. Covers basic operations, functional met… |

## Language | Contracts (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Assert Statement Specification](assert_spec.md) | Implemented | Thin | N/A | 10 | Tests assert statement support including: |

## Language | Declarations (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Static and Const Declarations Specification](static_const_declarations_spec.md) | Planned | Healthy | 2/5 | 53 | Static and const declarations provide compile-time and runtime constants with different scoping and initialization rule… |

## Language | Functions (3 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Decorators Specification](decorators_spec.md) | Implemented | Thin | N/A | 10 | Decorators are functions that transform other functions, enabling aspect-oriented programming patterns like logging, ca… |
| [Default Arguments Specification](default_arguments_spec.md) | Implemented | Thin | N/A | 4 | Tests for function default argument values. |
| [Named Arguments Specification](named_arguments_spec.md) | Implemented | Thin | N/A | 17 | Tests for named argument support allowing function calls with explicit parameter names, improving code clarity and enab… |

## Language | Literals (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Numeric Literals Specification](numeric_literals_spec.md) | Implemented | Thin | N/A | 16 | Tests for various numeric literal formats including hexadecimal, binary, octal, and numeric separators with underscores. |

## Language | Macros (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Macro Hygiene Specification](macro_hygiene_spec.md) | Implemented | Thin | N/A | 20 | Tests for macro hygiene system that prevents variable capture through gensym renaming. Covers variable isolation, neste… |

## Language | Operators (2 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Advanced Operators Specification](operators_advanced_spec.md) | Implemented | Thin | N/A | 52 | Tests advanced operators and language features including: |
| [Arithmetic Operations Specification](arithmetic_spec.md) | Implemented | Needs detail | 1/5 | 83 | Arithmetic operations provide basic mathematical computations on numeric types. Simple supports integer and floating-po… |

## Language | Pattern Matching (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Advanced Pattern Matching Specification](pattern_matching_advanced_spec.md) | Implemented | Thin | N/A | 20 | Tests advanced pattern matching features including: |

## Language | Syntax (3 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Alias and Deprecated Feature Specification](alias_deprecated_spec.md) | In Progress | Healthy | 2/5 | 56 | This specification covers the alias and deprecation features: 1. Type alias: `alias NewName = OldName` for classes/stru… |
| [Multi-line Syntax Specification](multiline_syntax_spec.md) | Implemented | Thin | N/A | 11 | Tests for multi-line syntax patterns including function calls spanning multiple lines, array literals, and continuation… |
| [String Interpolation Specification](string_interpolation_spec.md) | Implemented | Thin | N/A | 14 | String interpolation allows embedding expressions directly in string literals using curly braces. Simple treats interpo… |

## Language | Types (4 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Primitive Types Specification](primitive_types_spec.md) | Implemented | Thin | N/A | 21 | Tests for primitive types, type suffixes, union types, type aliases, and generic types. |
| [Result Type Specification](result_type_spec.md) | Implemented | Thin | N/A | 16 | Tests for the Result type representing success or error outcomes, including constructors, pattern matching, and safe un… |
| [Symbols and Atoms Specification](symbols_atoms_spec.md) | Implemented | Thin | N/A | 11 | Symbols (also called atoms) are immutable, interned identifiers that are compared by identity rather than value. They p… |
| [Unit Types Specification](unit_types_spec.md) | Implemented | Thin | N/A | 21 | Tests for semantic unit types that add compile-time dimensional safety to numeric values. |

## Language, Collections (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Advanced Indexing and Slicing Specification](advanced_indexing_spec.md) | Complete | Thin | N/A | 21 | Tests for advanced indexing features including: |

## Language, Syntax (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Dictionary Grammar and Syntax Specification](dict_grammar_spec.md) | Complete | Thin | N/A | 18 | Tests for dictionary literal syntax, ensuring correct grammar is used. |

## Lint (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Unnamed Duplicate Typed Arguments Warning Specification](unnamed_duplicate_typed_args_spec.md) | Implemented | Thin | N/A | 9 | This lint warns when a function has multiple parameters of the same type that |

## ML, Collections, API (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Tensor Interface Consistency Specification](tensor_interface_spec.md) | Complete | Thin | N/A | 21 | Tests that tensor interfaces are consistent between core and torch. |

## Memory Management (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Borrowing Specification](borrowing_spec.md) | In Progress | Thin | N/A | 4 | Reference Capabilities and Borrowing Specification |

## Operators | Arithmetic (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Floor Division (.fdiv) Method](floor_division_fdiv_spec.md) | Implemented | Needs detail | N/A | 53 | The `.fdiv()` method provides floor division functionality, replacing the old `//` operator |

## Operators | Linear Algebra (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Matrix Multiplication Operator (@)](matrix_multiplication_spec.md) | Implemented | Thin | N/A | 37 | The `@` operator performs matrix multiplication following NumPy semantics: |

## Other (4 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Sandboxing & Isolation](sandboxing_spec.md) | Runtime Complete (#916-919), Environment Planned (#920-923) | Needs detail | N/A | 14 | Simple provides two complementary isolation models for secure code execution: |
| [Simple Language Metaprogramming - Test Specification](metaprogramming.md) | Partial Implementation | Thin | N/A | 8 | This file contains executable test cases for metaprogramming features that are currently implemented in Simple's runtim… |
| [Simple Language Syntax Specification - Test Specification](syntax_spec.md) | Stable | Thin | N/A | 15 | Comprehensive tests for Simple's syntax, including literals, string interpolation, operators, and indentation-based par… |
| [Simple Language Type System - Test Specification](types_spec.md) | Stable (Basic Features) | Thin | N/A | 5 | Executable tests for Simple's type system basics: primitives, mutability, generics, and type inference. |

## Parser / Operators (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Null Coalescing and Try Operator Parser Specification](null_coalescing_try_operator_spec.md) | In Progress | Thin | 3/5 | 15 | Tests for the `??` (null coalescing) and `?` (try) operators in various contexts. These operators should work correctly… |

## Runtime (18 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Actor Model Concurrency](actors_spec.md) | In Progress | Thin | N/A | 0 | The actor model provides a message-passing concurrency primitive where isolated actors communicate exclusively through… |
| [Asynchronous Effects and Async/Await](async_effects_spec.md) | In Progress | Thin | N/A | 0 | Asynchronous effects integrate Simple's effect system with async/await concurrency, allowing effectful computations to… |
| [CUDA Backend](cuda_spec.md) | In Progress | Thin | N/A | 18 | Tests NVIDIA CUDA backend functionality including device detection and selection, memory allocation and transfer operat… |
| [Custom Collection Backends](custom_backend_spec.md) | Active | Thin | N/A | 7 | Tests custom collection backend implementations including ArrayList and HashMap. Validates that array literals can be t… |
| [External FFI Function Calls and Native Interoperability](extern_functions_spec.md) | Active | Thin | N/A | 9 | Simple's Foreign Function Interface (FFI) enables calling native runtime functions declared with the `extern fn` keywor… |
| [Future Body Execution and Deferred Evaluation](future_body_execution_spec.md) | In Progress | Thin | N/A | 11 | Futures in Simple wrap deferred computations created with `future(expr)` and forced with `await`. This spec focuses on… |
| [Futures and Promises for Asynchronous Programming](futures_promises_spec.md) | In Progress | Thin | N/A | 15 | This spec validates the full Promises API for asynchronous programming in Simple. Promises represent eventual values wi… |
| [GPU Basic Operations](gpu_basic_spec.md) | In Progress | Thin | N/A | 18 | Tests GPU device detection and basic operations across all backends. Validates backend detection, preferred backend sel… |
| [GPU Kernels Specification](gpu_kernels_spec.md) | Planned | Needs detail | 5/5 | 10 | GPU kernel support enables compute-intensive operations to run on GPU hardware through a high-level interface. This fea… |
| [Garbage-Collected Memory Management as the Default Strategy](gc_managed_default_spec.md) | In Progress | Thin | N/A | 16 | In Simple, all heap-allocated objects default to garbage-collected (GC) memory management unless an explicit capability… |
| [Math Blocks Autograd Runtime](math_autograd_runtime_spec.md) | In Progress | Thin | N/A | 9 | Compiled-mode proof tests for m{}, loss{}, and nograd{} runtime semantics. Verifies that MIR lowering emits real runtim… |
| [Reference Counted Pointers Specification](shared_pointers_spec.md) | Implemented | Thin | N/A | 9 | Reference counted pointers provide safe sharing of data with automatic |
| [Rust-to-Simple FFI Specification](rust_simple_ffi_spec.md) | Implemented | Thin | 4/5 | 32 | The Simple language provides a comprehensive Foreign Function Interface (FFI) system that enables bidirectional communi… |
| [Stackless Coroutines](stackless_coroutines_spec.md) | In Progress | Thin | N/A | 24 | Tests stackless coroutines which provide lightweight concurrency without allocating stack space for each coroutine. Cov… |
| [Tensor Bridge Batch Conversion](tensor_bridge_spec.md) | Active | Thin | N/A | 5 | Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor arrays. Validates flattening Vec3 lists… |
| [Unique Pointers Specification](unique_pointers_spec.md) | Implemented | Thin | N/A | 5 | UniquePtr provides exclusive ownership semantics via cooperative move tracking. Since Simple copies on assignment, uniq… |
| [Vulkan Compute Backend](vulkan_spec.md) | In Progress | Thin | N/A | 22 | Tests Vulkan compute backend functionality including initialization and shutdown, device selection and info retrieval,… |
| [Weak Pointers Specification](weak_pointers_spec.md) | Implemented | Thin | N/A | 5 | Weak references provide non-owning references to values managed by a global weak reference table. When the target is in… |

## Runtime | Async (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Async Features Specification](async_features_spec.md) | Implemented | Thin | N/A | 42 | async features - runtime parser cannot handle async/await/spawn/yield/generator syntax |

## Runtime | Collections (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Collection Utilities Specification](collection_utilities_spec.md) | Implemented | Needs detail | N/A | 40 | Tests collection utility functions including: |

## Runtime | Dependency Injection (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Dependency Injection Specification](di_injection_spec.md) | Implemented | Thin | N/A | 14 | Integration tests for DI Container with realistic service patterns. |

## Runtime | File I/O (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Async File I/O Specification](async_file_io_spec.md) | Implemented | Thin | N/A | 14 | Tests async file I/O functionality including: |

## Runtime | Memory Management (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Capture Buffer and Virtual Register Remapping Specification](capture_buffer_vreg_remapping_spec.md) | Planned | Thin | 4/5 | 46 | This specification covers advanced virtual register (vreg) remapping and capture buffer management at the runtime level… |

## Runtime | Module System (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Module Loader Specification](module_loader_spec.md) | Implemented | Thin | N/A | 32 | Tests the SMF module loader and registry including: |

## Runtime | Networking (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Networking Specification](networking_spec.md) | Implemented | Thin | N/A | 12 | Tests networking functionality including: |

## Standard Library (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [HashSet Basic Operations](hashset_basic_spec.md) | In Progress | Thin | N/A | 7 | Tests HashSet basic operations using a self-contained implementation. Covers set creation and initialization, element i… |

## Stdlib (10 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Experiment Tracking Integration Specification](experiment_tracking_spec.md) | In Progress | Thin | 3/5 | 6 | Integration tests for the full experiment tracking workflow: config loading, run lifecycle, metric logging, artifact st… |
| [Game Engine Actor Model Specification](actor_model_spec.md) | Implemented | Thin | 2/5 | 16 | Actor model for game entities with Vec3 positions and message-passing. |
| [Game Engine Component Specification](component_spec.md) | Implemented | Thin | 2/5 | 6 | Component system with ComponentType enum, Component trait, and ComponentManager. |
| [Game Engine SceneNode Specification](scene_node_spec.md) | Implemented | Thin | 2/5 | 3 | SceneNode trait using Transformd for transform hierarchy. |
| [HashMap Basic Operations Specification](hashmap_basic_spec.md) | Implemented | Thin | N/A | 8 | System tests for basic HashMap operations through the FFI layer. |
| [Mat4 Specification](mat4_spec.md) | Implemented | Thin | 3/5 | 10 | Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage. |
| [Quaternion Specification](quat_spec.md) | Implemented | Thin | 3/5 | 10 | Quat (f32) and Quatd (f64) quaternion types for 3D rotations. |
| [Table (DataFrame) Specification](table_spec.md) | Implemented | Thin | N/A | 25 | Table/DataFrame-like data structure for tabular data: |
| [Transform Specification](transform_spec.md) | Implemented | Thin | 3/5 | 9 | Transform (f32) and Transformd (f64) combining position, rotation, and scale. |
| [Vec3 Specification](vec3_spec.md) | Implemented | Thin | 2/5 | 23 | Vec3 (f32) and Vec3d (f64) 3D vector types with arithmetic, geometric, and utility methods. |

## Syntax (34 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Arithmetic Operators Specification](operators_arithmetic_spec.md) | Implemented | Healthy | 2/5 | 59 | Arithmetic operators in Simple provide standard mathematical operations on numeric types (Int and Float). The language… |
| [Call-Site Argument Labels](call_site_label_spec.md) | Active | Thin | N/A | 9 | Call-site labels are postfix keywords attached to arguments at the call site that improve readability of function calls… |
| [Comments Specification](comments_spec.md) | Implemented | Healthy | 1/5 | 23 | Simple supports multiple comment styles for different purposes: line comments for quick notes, block comments for longe… |
| [Contextual Keyword Disambiguation](parser_contextual_keywords_simple_spec.md) | Active | Thin | N/A | 12 | Simple treats `skip`, `static`, and `default` as contextual keywords rather than fully reserved words. This means each… |
| [Default Parameter Values](parser_default_keyword_spec.md) | Active | Thin | N/A | 18 | Tests the `default` keyword for function parameter default values using `=` syntax. Covers basic defaults, typed parame… |
| [Existence Check Operator (.?) Specification](exists_check_spec.md) | Implemented | Needs detail | 3/5 | 17 | The `.?` operator checks if a value is "present" (non-nil AND non-empty). Returns `T?` — the value itself if present, `… |
| [Existence Check Value Return (.? → T?) Specification](exists_check_value_return_spec.md) | Implemented (requires compiler rebuild) | Needs detail | 3/5 | 18 | After the `.?` return-type change, the operator returns `T?` instead of `bool`. This enables pattern binding (`if val x… |
| [Function Alias (Deprecated Delegation)](function_alias_spec.md) | Active | Thin | N/A | 10 | Tests the deprecated `fn name = target` function alias syntax that the desugar pipeline transforms into explicit delega… |
| [Guard Clause Specification](guard_clause_spec.md) | Implemented | Thin | N/A | 10 | Guard clauses (pattern guards) allow conditional matching within pattern match arms. |
| [Implicit Multiplication Specification](implicit_mul_spec.md) | Implemented | Thin | N/A | 22 | Implicit multiplication in m{} math blocks: |
| [Indentation-Based Blocks Specification](indentation_blocks_spec.md) | Implemented | Needs detail | 2/5 | 15 | Indentation-based blocks use Python-style significant whitespace to delimit code blocks instead of braces. This feature… |
| [Integer Literals Specification](basic_types_integer_literals_spec.md) | Implemented | Healthy | 1/5 | 49 | Integer literals in Simple support multiple base formats (decimal, hexadecimal, binary, octal), underscore separators f… |
| [Line Continuation Specification](line_continuation_spec.md) | Implemented | Thin | N/A | 11 | Line continuation allows long expressions and function calls to span multiple lines |
| [Loop Constructs Specification](loops_spec.md) | Implemented | Needs detail | N/A | 21 | The Simple language provides several loop constructs for iterating over collections and |
| [Math Language Specification](math_language_spec.md) | Implemented | Thin | N/A | 22 | Math language features for Simple: |
| [Method Alias Forwarding Specification](method_alias_spec.md) | In Progress | Thin | 3/5 | 7 | Tests that `alias fn` and `alias me` in class bodies desugar into correct forwarding methods. The desugar transforms: `… |
| [Multiple Assignment (Destructuring) Specification](multiple_assignment_spec.md) | Implemented | Thin | N/A | 18 | Multiple assignment (destructuring) allows binding multiple variables from |
| [Named Argument with Equals Syntax Specification](named_arg_equals_spec.md) | Implemented | Thin | N/A | 20 | Named arguments allow passing function arguments by name rather than position. |
| [No-Parentheses Function Calls Specification](no_paren_calls_spec.md) | Implemented | Healthy | 2/5 | 26 | No-parentheses function calls allow calling functions without wrapping arguments in parentheses, providing Ruby-style s… |
| [Optional Chaining Specification](optional_chaining_spec.md) | Implemented | Thin | N/A | 20 | Optional chaining (`?.`) provides safe navigation through potentially-nil |
| [Parser Edge Cases for Operators, Keywords, and Type Syntax](parser_edge_cases_spec.md) | In Progress | Thin | N/A | 9 | The Simple parser must handle several non-trivial syntactic forms that are easy to mis-parse: the matrix-multiplication… |
| [Placeholder Lambda Expressions](placeholder_lambda_spec.md) | Active | Thin | N/A | 22 | Placeholder lambdas let the programmer write concise anonymous functions by using `_` as a stand-in for each successive… |
| [Range Step Specification](range_step_by_spec.md) | Implemented | Thin | N/A | 25 | Ranges in Simple can be iterated with custom step values. This is primarily |
| [Safe Unwrap Operators Specification](safe_unwrap_operators_spec.md) | Implemented | Thin | N/A | 23 | Safe unwrap operators provide ergonomic ways to extract values from Option<T> |
| [Set Literal Syntax](set_literal_spec.md) | In Progress | Thin | N/A | 13 | Tests the `s{...}` set literal syntax for creating sets with automatic duplicate removal. Covers empty sets, integer an… |
| [Single-Line Function Definitions Specification](single_line_functions_spec.md) | Implemented | Thin | N/A | 19 | Single-line (inline) function definitions allow functions to be defined with |
| [Skip Keyword - Basic Functionality](parser_skip_basic_spec.md) | Active | Thin | N/A | 10 | Tests basic parsing and runtime behavior of the `skip` keyword as a standalone statement. Verifies that skip can be use… |
| [Skip Keyword - Comprehensive](parser_skip_keyword_spec.md) | Active | Thin | N/A | 42 | Comprehensive tests for the `skip` keyword covering lexer token recognition, statement parsing, control flow interactio… |
| [Static Keyword Parsing](parser_static_keyword_spec.md) | Active | Thin | N/A | 21 | Tests parsing and resolution of the `static` keyword for class and struct methods. Uses ClassName.method() dot-access s… |
| [Struct Field Shorthand Specification](struct_shorthand_spec.md) | Implemented | Thin | N/A | 15 | Struct field shorthand allows omitting the field name when the variable name |
| [Trailing Blocks Specification](trailing_blocks_spec.md) | Implemented | Needs detail | 3/5 | 17 | Trailing blocks (also called "trailing lambdas") provide Ruby-style syntax for passing lambda functions as the last arg… |
| [UFCS (Uniform Function Call Syntax) Specification](ufcs_spec.md) | Implemented | Thin | 4/5 | 17 | UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax. When `x.method()` is called, the… |
| [Underscore Wildcard Specification](underscore_wildcard_spec.md) | Implemented | Thin | N/A | 7 | Tests for underscore (_) as a wildcard placeholder in various contexts: |
| [Walrus Operator](walrus_operator_spec.md) | Active | Thin | N/A | 25 | Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating immutable bindings. Covers basic bind… |

## Syntax / Math DSL (3 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Deep Learning Equation Tests for m{} Math Blocks](math_dl_equations_spec.md) | Implemented | Thin | 3/5 | 72 | Tests that composite DL equations parse, evaluate correctly, render to LaTeX, and render to nvim-friendly Unicode. Cove… |
| [Math Block Tensor Operations Specification](math_blocks_spec.md) | Implemented | Thin | 4/5 | 28 | The `m{}` math block supports torch-compatible tensor operations for numerical computing. Each math block is a self-con… |
| [loss{} and nograd{} Block Tests](loss_nograd_blocks_spec.md) | Implemented | Thin | 2/5 | 27 | Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the same supported math-expression subset as `m{}… |

## Syntax / Math DSL / Rendering (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Math Block Rendering Specification](math_render_spec.md) | Implemented | Thin | 3/5 | 129 | Intensive tests for the math expression rendering pipeline: |

## Syntax / Stdlib (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Tensor Operations Specification](tensor_spec.md) | Implemented | Thin | N/A | 55 | Tensor operations for mathematical computing: |

## System/Collections (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Btree Basic Specification](btree_basic_spec.md) | Active | Thin | N/A | 7 | BTreeMap Basic Operations System Test |

## Tooling (9 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Architecture Check Error Cases](arch_check_error_cases_spec.md) | Active | Thin | N/A | 43 | Tests failure paths and edge cases in the architecture validation system. Covers boundary conditions for string trimmin… |
| [Bulk Validate Path Handling Specification](bulk_validate_spec.md) | Implemented | Needs detail | N/A | 80 | Tests for path normalization, dot-directory handling, file extension detection, and CMM file identification in the bulk… |
| [CMM Expression Parser Specification](cmm_parser_expr_spec.md) | Implemented | Thin | N/A | 80 | Summary not provided in the doc blocks. |
| [CMM Lexer Specification](cmm_lexer_spec.md) | Implemented | Thin | N/A | 95 | Tests for the CMM (PRACTICE Script) lexer. Validates tokenization of all CMM lexical elements: comments, labels, macros… |
| [CMM Parser Specification](cmm_parser_spec.md) | Implemented | Thin | N/A | 82 | Summary not provided in the doc blocks. |
| [CMM Parser V4 Fixes Specification](cmm_parse_v4_fixes_spec.md) | Implemented | Thin | N/A | 19 | Summary not provided in the doc blocks. |
| [CMM v2025 Version Support](cmm_v2025_spec.md) | In Progress | Thin | N/A | 16 | Tests for CMM v2025 version support and command database updates. |
| [Registry Index Specification](index_spec.md) | In Progress | Thin | 2/5 | 16 | Tests for the sparse package index: parsing SDN entries, computing index paths, and searching. |
| [String Operation Efficiency Specification](string_efficiency_spec.md) | Implemented | Thin | N/A | 58 | Tests that string operations in the CMM LSP toolchain produce correct results after being rewritten from O(n²) characte… |

## Tools | Development (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [File Watcher Specification](file_watcher_spec.md) | Implemented | Thin | N/A | 3 | Tests the file watcher for automatic rebuilds including: |

## Tools | Web Framework (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Web Framework Specification](web_framework_spec.md) | Planned | Thin | N/A | 16 | Tests the Simple web framework (.sui files) including: |

## Type System | Capabilities (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Reference Capability System Specification](capability_system_spec.md) | Implemented | Thin | N/A | 40 | Tests the reference capability system for memory safety: |

## Type System | Contracts (2 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Class Invariant Specification](class_invariant_spec.md) | Implemented | Thin | N/A | 15 | Tests that class invariants are properly checked: |
| [Contract Runtime Specification](contract_runtime_spec.md) | Implemented | Thin | N/A | 25 | Tests that contract checks execute correctly at runtime, including |

## Type System | Effects (2 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Effect Annotations Specification](effect_annotations_spec.md) | Implemented | Thin | N/A | 35 | Tests that effect annotations (@pure, @io, @net, @fs, @unsafe, @async) |
| [Effect System Specification](effect_system_spec.md) | Implemented | Thin | N/A | 32 | Tests the effect system including: |

## Type System | Generics (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Advanced Generics Specification](generics_advanced_spec.md) | Implemented | Thin | N/A | 8 | Tests advanced generic features including: |

## Type System | Traits (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Trait Coherence Specification](trait_coherence_spec.md) | Implemented | Thin | N/A | 20 | Tests trait coherence rules including: |

## Residual Files

These files are present in `doc/06_spec` but were not regenerated in this run.

| File | Type |
|------|------|
| _temp_di5_test_spec.md | Legacy markdown |
| _temp_diag10_spec.md | Legacy markdown |
| _temp_diag2_spec.md | Legacy markdown |
| _temp_diag3_spec.md | Legacy markdown |
| _temp_diag4_spec.md | Legacy markdown |
| _temp_diag5_spec.md | Legacy markdown |
| _temp_diag6_spec.md | Legacy markdown |
| _temp_diag7_spec.md | Legacy markdown |
| _temp_diag8_spec.md | Legacy markdown |
| _temp_diag9_spec.md | Legacy markdown |
| _temp_diag_spec.md | Legacy markdown |
| null_coalescing_try_operator.md | Legacy markdown |
| parser_control_flow_spec.md | Legacy markdown |

