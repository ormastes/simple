# Incomplete Feature Audit

Rows with non-complete status from feature_part1.md and feature_part2.md.
This audit checks whether doc/test paths referenced in each row exist on disk.

## Summary
- total non-complete rows: 183
- rows with missing doc/test refs: 181

## Missing References

### #802 LLVM backend integration
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/compiler/tests/

### #805 RISC-V 32-bit cross-compile
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/linker/tests/

### #880 `module requires[cap]`
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/compiler/tests/

### #881 `@pure` / `@io` / `@net`
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/compiler/tests/

### #882 Capability propagation
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/compiler/tests/

### #883 Forbidden effect errors
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/compiler/tests/

### #884 Stdlib effect annotations
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/effects/

### #885 `--emit-ast`
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #886 `--emit-hir`
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #887 `--emit-mir`
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #888 `--error-format=json`
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #889 Semantic diff tool
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #890 `simple context` command
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #891 Dependency symbol extraction
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/compiler/tests/

### #892 Markdown context format
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #893 JSON context format
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #894 `@property_test` decorator
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/property/
- missing r-test: src/compiler/tests/

### #895 Input generators
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/property/

### #896 Shrinking on failure
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/property/
- missing r-test: src/runtime/tests/

### #897 Configurable iterations
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/property/

### #898 Generator combinators
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/property/

### #899 `@snapshot_test` decorator
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/snapshot/
- missing r-test: src/compiler/tests/

### #900 Snapshot storage
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/driver/tests/

### #901 `--snapshot-update` flag
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #902 Multi-format snapshots
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/snapshot/
- missing r-test: src/driver/tests/

### #903 Lint rule trait
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/lint/

### #904 Built-in rules
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/compiler/tests/

### #905 Configurable severity
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/driver/tests/

### #906 `simple lint` command
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #907 Auto-fix suggestions
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #908 `simple fmt` command
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #909 Single correct style
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/parser/tests/

### #910 Format-on-save integration
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/driver/tests/

### #911 Deterministic build mode
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/compiler/tests/

### #912 Replay logs
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/driver/tests/

### #913 `@generated_by` provenance
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: std_lib/test/system/audit/
- missing r-test: src/compiler/tests/

### #914 API surface lock file
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/driver/tests/

### #915 Spec coverage metric
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/driver/tests/

### #916 Resource limits
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/runtime/tests/

### #917 Network isolation
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/runtime/tests/

### #918 Filesystem isolation
- status: 📋
- source: doc/features/feature_part1.md
- missing r-test: src/runtime/tests/

### #919 `simple run --sandbox`
- status: 📋
- source: doc/features/feature_part1.md
- missing s-test: system/cli/
- missing r-test: src/driver/tests/

### #1000 `pc{...}` syntactic island (lexer mode)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1001 Predicate operators (!, &, \
- status: , grouping)
- source: doc/features/feature_part2.md
- missing doc: R

### #1002 Pattern wildcards (*, **, prefix*, *suffix)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1003 Signature pattern `ret_pat qname_pat(arg_pats)`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1004 `..` argument wildcard
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1005 Allowed introducer validation (`on`, `bind on`, `forbid`, `allow`)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1006 Weaving selector set (execution/within/attr/effect/test/decision/condition)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1007 DI/Mock selector set (type/within/attr only)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1008 Illegal selector in context diagnostic
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1009 Typed dependency graph (compiler-built)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1010 SDN `di:` section with profiles
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/sdn/tests/

### #1011 `bind on pc{...} -> Impl scope priority` syntax
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1012 `@sys.inject` constructor injection
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/system/di/
- missing r-test: src/compiler/tests/

### #1013 Per-parameter `@sys.inject`
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/system/di/
- missing r-test: src/compiler/tests/

### #1014 Priority/specificity/stable-order resolution
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1015 Ambiguous binding diagnostic
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1016 Release profile freeze (direct wiring)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1017 All-params-injectable rule for constructor `@sys.inject`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1018 Parameter-level diagnostic for unresolvable deps
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1019 No mixing constructor vs per-param injection
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1020 `mock Name implements Trait:` syntax
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/system/mock/
- missing r-test: src/parser/tests/

### #1021 `expect method() -> Type:` syntax
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/system/mock/
- missing r-test: src/parser/tests/

### #1022 `@sys.test_only` decorator enforcement
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1023 Mock binding via DI predicates (test profile)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1024 Illegal mock in non-test diagnostic
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1025 Illegal Mock* binding outside test profile
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1026 `arch_rules:` block syntax
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1027 `forbid pc{...}` rule
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1028 `allow pc{...}` rule
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1029 `import(from_pattern, to_pattern)` selector
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1030 `depend(from_pattern, to_pattern)` selector
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1031 `use(pattern)` selector
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1032 `export(pattern)` selector
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1033 `config(STRING)` selector
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1034 Release build MUST NOT select test profile
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1035 Release MUST NOT enable runtime interceptors
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1036 `execution(signature)` join point
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1037 `within(pattern)` join point
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1038 `attr(IDENT)` join point
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1039 `effect(effect_set)` join point
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1040 `test(IDENT)` join point
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1041 `decision()`/`condition()` join points (coverage)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1042 Zero-overhead when aspects.enabled = []
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1043 `before` advice
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1044 `after_success` advice
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1045 `after_error` advice
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1046 Advice priority ordering
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1047 `call(signature)` link-time selector
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1048 `init(pattern)` runtime selector (DI-controlled)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/runtime/tests/

### #1049 `around` advice with `proceed()` (runtime only)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/runtime/tests/

### #1050 Proceed exactly-once enforcement
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/runtime/tests/

### #1051 `simple.sdn` manifest parsing
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/pkg/tests/

### #1052 Manifest format auto-detection
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/pkg/tests/

### #1053 `simple pkg migrate` command
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/pkg/tests/

### #1054 `simple init` generates `.sdn`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/pkg/tests/

### #1055 TOML deprecation warning
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/pkg/tests/

### #1056 Lock file as SDN (`simple-lock.sdn`)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/pkg/tests/

### #1058 SDN for all config files
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/driver/tests/

### #1059 SDN for AOP/DI config
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1060 SDN CLI improvements
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/sdn/tests/

### #1061 `macro` keyword
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1062 `gen_code` block
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1063 Hygienic macro expansion
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1064 AST manipulation in macros
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1065 Macro-as-decorator
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1066 `context obj:` block
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/compiler/tests/

### #1067 `method_missing` handler
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/compiler/tests/

### #1068 Fluent interface support
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/

### #1069 `@cached` decorator
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/

### #1070 `@logged` decorator
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/

### #1071 `@deprecated(message)`
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/compiler/tests/

### #1072 `@timeout(seconds)`
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/

### #1073 `#[inline]` hint
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1074 `#[derive(...)]` auto-impl
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1075 `#[cfg(...)]` conditional
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1076 `#[allow(...)]`/`#[deny(...)]`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1077 `#[test]` marker
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1078 List comprehension
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/parser/tests/

### #1079 Dict comprehension
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/parser/tests/

### #1080 Negative indexing `arr[-1]`
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/runtime/tests/

### #1081 Slicing `arr[2:5]`, `arr[::2]`
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/runtime/tests/

### #1082 Spread `[*a, *b]`, `{**d1, **d2}`
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/parser/tests/

### #1083 Match guards `case x if x > 0:`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1084 Or patterns `case "a" \
- status: "b":`
- source: doc/features/feature_part2.md
- missing doc: R

### #1085 Range patterns `case 1..10:`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1086 `if let Some(x) = ...`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1087 `while let Some(x) = ...`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1088 Chained comparisons `0 < x < 10`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1089 Exhaustiveness checking
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1090 Unreachable arm detection
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1091 `with open(...) as f:`
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/
- missing r-test: src/parser/tests/

### #1092 `ContextManager` trait
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/

### #1093 `move \:` closures
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1094 `?` operator for Result
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1095 `?` operator for Option
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1096 `mut T` exclusive writer capability
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1097 `iso T` isolated capability
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1098 Capability conversions
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1099 Happens-before memory model
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/runtime/tests/

### #1100 Data-race-free guarantee
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/runtime/tests/

### #1101 `Atomic[T]` wrapper
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/src/infra/
- missing r-test: src/runtime/tests/

### #1102 `Mutex[T]` wrapper
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/src/infra/
- missing r-test: src/runtime/tests/

### #1103 `RwLock[T]` wrapper
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/src/infra/
- missing r-test: src/runtime/tests/

### #1104 `#[concurrency_mode(actor)]` (default)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1105 `#[concurrency_mode(lock_base)]`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1106 `#[concurrency_mode(unsafe)]`
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1107 `unsafe:` block syntax
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1108 GC write barriers in concurrent collections
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/runtime/tests/

### #1109 `ConcurrentMap[K, V]` with GC objects
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/src/infra/
- missing r-test: src/runtime/tests/

### #1110 `ConcurrentQueue[T]` with GC objects
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/src/infra/
- missing r-test: src/runtime/tests/

### #1111 `ConcurrentStack[T]` with GC objects
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/src/infra/
- missing r-test: src/runtime/tests/

### #1112 Object tracing through collection handles
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/runtime/tests/

### #1113 Compile error for `mut T` in actor mode
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1114 Compile error for `Mutex` in actor mode
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1115 Warning for unsafe in release build
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1131 Canonical formatter (no config)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/driver/tests/

### #1132 Formatter CLI (`simple fmt`)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/driver/tests/

### #1134 Safety lint set
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1135 Correctness lint set
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1136 Warning lint set
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1137 Style lint set
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1138 Concurrency lint set
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1139 `#[allow]`/`#[deny]`/`#[warn]` attributes
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/parser/tests/

### #1140 Lint groups
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1141 Fix-it hints in diagnostics
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1142 Auto-fix CLI (`simple fix`)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/driver/tests/

### #1143 Error code stability
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1144 Lint configuration in simple.sdn
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/driver/tests/

### #1145 `--explain` for error codes
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/driver/tests/

### #1146 Orphan rule enforcement
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1147 Overlap detection
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1148 Associated type coherence
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1149 Blanket impl conflict detection
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1150 Specialization (`#[default]` impl)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1151 Negative trait bounds (`!Trait`)
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1152 Coherence error messages
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1153 Newtype pattern support
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1154 Extension traits
- status: 📋
- source: doc/features/feature_part2.md
- missing r-test: src/compiler/tests/

### #1155 Delegation pattern
- status: 📋
- source: doc/features/feature_part2.md
- missing s-test: std_lib/test/

