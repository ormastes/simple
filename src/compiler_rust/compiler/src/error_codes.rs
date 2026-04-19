/// Error codes for compiler errors.
///
/// Format: E1xxx for semantic, E2xxx for codegen, E3xxx for runtime
pub mod codes {
    // Semantic errors (E10xx)
    pub const UNDEFINED_VARIABLE: &str = "E1001";
    pub const UNDEFINED_FUNCTION: &str = "E1002";
    pub const TYPE_MISMATCH: &str = "E1003";
    pub const INVALID_ASSIGNMENT: &str = "E1004";
    pub const INVALID_OPERATION: &str = "E1005";
    pub const INVALID_PATTERN: &str = "E1006";
    pub const MISSING_FIELD: &str = "E1007";
    pub const DUPLICATE_DEFINITION: &str = "E1008";
    pub const CIRCULAR_DEPENDENCY: &str = "E1009";
    pub const MODULE_NOT_FOUND: &str = "E1010";
    pub const UNDEFINED_TYPE: &str = "E1011";
    pub const UNDEFINED_FIELD: &str = "E1012";
    pub const UNKNOWN_METHOD: &str = "E1013";
    pub const UNKNOWN_CLASS: &str = "E1014";
    pub const UNKNOWN_ENUM: &str = "E1015";
    pub const LET_BINDING_FAILED: &str = "E1016";
    pub const IMPURE_FUNCTION_IN_CONTRACT: &str = "E1017";
    pub const EFFECT_DECLARATION_FAILED: &str = "E1018";
    pub const DUPLICATE_BINDING: &str = "E1019";
    pub const ARGUMENT_COUNT_MISMATCH: &str = "E1020";
    pub const MISSING_STRUCT_FIELDS: &str = "E1021";
    pub const INVALID_LHS_ASSIGNMENT: &str = "E1022";
    pub const INVALID_STRUCT_LITERAL: &str = "E1023";
    pub const CONST_EVAL_FAILED: &str = "E1024";
    pub const DUPLICATE_METHOD: &str = "E1025";
    pub const UNKNOWN_ASSOC_TYPE: &str = "E1026";
    pub const UNCONSTRAINED_TYPE_PARAM: &str = "E1027";
    pub const UNKNOWN_ASSOC_TYPE_NAME: &str = "E1028";
    pub const CONFLICTING_TRAIT_BOUNDS: &str = "E1029";
    pub const INVALID_LIFETIME_ON_TRAIT: &str = "E1030";
    pub const MISSING_TRAIT_METHOD: &str = "E1031";
    pub const SELF_IN_STATIC: &str = "E1032";
    pub const INVALID_SELF_IMPORT: &str = "E1033";
    pub const UNRESOLVED_IMPORT: &str = "E1034";
    pub const INVALID_SELF_CONTEXT: &str = "E1035";
    pub const CLOSURE_CAPTURE_FAILED: &str = "E1036";
    pub const INVALID_SELF_PARAM: &str = "E1037";
    pub const PRIVATE_IN_PUBLIC: &str = "E1038";
    pub const INVALID_VISIBILITY: &str = "E1039";
    pub const PRIVATE_FIELD_ACCESS: &str = "E1040";
    pub const INVALID_UNARY_OP: &str = "E1041";
    pub const INVALID_SELF_TYPE: &str = "E1042";
    pub const INVALID_INDEX_TYPE: &str = "E1043";
    pub const TUPLE_INDEX_OOB: &str = "E1044";
    pub const INVALID_FIELD_ASSIGN: &str = "E1045";
    pub const PRIVATE_FIELD: &str = "E1046";
    pub const CANNOT_BORROW_MUT_FIELD: &str = "E1047";
    pub const NOT_CALLABLE: &str = "E1048";
    pub const CANNOT_CALL_NON_FUNCTION: &str = "E1049";
    pub const DISALLOWED_COERCION: &str = "E1050";
    pub const CLOSURE_SIGNATURE_MISMATCH: &str = "E1051";
    pub const INVALID_LET_ELSE_PATTERN: &str = "E1052";
    pub const CANNOT_BORROW_IMMUTABLE: &str = "E1053";
    pub const INVALID_DEREFERENCE: &str = "E1054";
    pub const TYPE_ALIAS_BOUNDS: &str = "E1055";
    pub const INVALID_RANGE: &str = "E1056";
    pub const YIELD_OUTSIDE_GENERATOR: &str = "E1057";
    pub const INVALID_DOC_COMMENT: &str = "E1058";
    pub const INVALID_IMPLICIT_DEREFERENCE: &str = "E1059";
    pub const INVALID_CONST_EXPRESSION: &str = "E1060";
    pub const EMPTY_ENUM: &str = "E1061";
    pub const RECURSION_LIMIT_EXCEEDED: &str = "E1062";
    pub const TYPE_SIZE_LIMIT_EXCEEDED: &str = "E1063";
    pub const WRONG_INTRINSIC_TYPE: &str = "E1064";
    pub const INVALID_RETURN_TYPE: &str = "E1065";
    pub const INVALID_MAIN_SIGNATURE: &str = "E1066";
    pub const INVALID_BUILTIN_ATTRIBUTE: &str = "E1067";
    pub const INCONSISTENT_BINDINGS: &str = "E1068";
    pub const MISMATCHED_BINDING: &str = "E1069";
    pub const INVALID_DEFAULT_VARIANT: &str = "E1070";
    pub const INVALID_ATTRIBUTE_POSITION: &str = "E1071";
    pub const INVALID_DESTRUCTURING: &str = "E1072";
    pub const NON_EXHAUSTIVE_TYPE: &str = "E1073";
    pub const CONFLICTING_REPRESENTATION: &str = "E1074";
    pub const DISCRIMINANT_OVERFLOW: &str = "E1075";
    pub const UNKNOWN_INTRINSIC: &str = "E1076";
    pub const WRONG_INTRINSIC_SIGNATURE: &str = "E1077";
    pub const INVALID_INTRINSIC_RETURN: &str = "E1078";
    pub const MISSING_GENERIC_ARGUMENTS: &str = "E1079";
    pub const TYPE_TOO_COMPLEX: &str = "E1080";

    // Control flow errors (E11xx)
    pub const BREAK_OUTSIDE_LOOP: &str = "E1101";
    pub const CONTINUE_OUTSIDE_LOOP: &str = "E1102";
    pub const RETURN_OUTSIDE_FUNCTION: &str = "E1103";
    pub const RETURN_IN_CLOSURE: &str = "E1104";
    pub const INVALID_CONTROL_FLOW: &str = "E1105";

    // Actor/concurrency errors (E12xx)
    pub const ACTOR_SEND_FAILED: &str = "E1201";
    pub const ACTOR_RECV_FAILED: &str = "E1202";
    pub const CHANNEL_CLOSED: &str = "E1203";
    pub const DEADLOCK_DETECTED: &str = "E1204";
    pub const ACTOR_JOIN_FAILED: &str = "E1205";

    // Context errors (E10xx continued)
    pub const INVALID_CONTEXT: &str = "E1081";

    // Capability errors (E13xx)
    pub const CAPABILITY_VIOLATION: &str = "E1301";
    pub const ISOLATION_VIOLATION: &str = "E1302";
    pub const BORROW_VIOLATION: &str = "E1303";
    pub const USE_AFTER_FREE: &str = "E1304";

    // Macro errors (E14xx)
    pub const MACRO_UNDEFINED: &str = "E1401";
    pub const MACRO_USED_BEFORE_DEFINITION: &str = "E1402";
    pub const KEYWORD_IN_MACRO: &str = "E1403";
    pub const MACRO_SHADOWING: &str = "E1403"; // Alias for backward compatibility
    pub const MACRO_INVALID_BLOCK_POSITION: &str = "E1404";
    pub const MACRO_MISSING_TYPE_ANNOTATION: &str = "E1405";
    pub const MACRO_INVALID_QIDENT: &str = "E1406";

    // AOP errors (E15xx)
    pub const INVALID_POINTCUT_SYNTAX: &str = "E1501";
    pub const UNDEFINED_JOINPOINT: &str = "E1502";
    pub const INVALID_ADVICE_TYPE: &str = "E1503";
    pub const CONFLICTING_ADVICE_ORDER: &str = "E1504";
    pub const INVALID_WEAVING_TARGET: &str = "E1505";
    pub const ASPECT_CIRCULAR_DEPENDENCY: &str = "E1506";
    pub const INVALID_POINTCUT_SELECTOR: &str = "E1507";
    pub const ASPECT_NOT_ENABLED: &str = "E1508";

    // Custom block errors (E16xx)
    pub const UNKNOWN_BLOCK_TYPE: &str = "E1601";
    pub const INVALID_BLOCK_SYNTAX: &str = "E1602";
    pub const MATH_BLOCK_INVALID_EXPR: &str = "E1603";
    pub const MATH_BLOCK_UNDEFINED_VAR: &str = "E1604";
    pub const SHELL_BLOCK_INVALID_CMD: &str = "E1605";
    pub const SHELL_BLOCK_UNSAFE_OP: &str = "E1606";
    pub const SQL_BLOCK_SYNTAX_ERROR: &str = "E1607";
    pub const SQL_BLOCK_INVALID_PARAM: &str = "E1608";
    pub const REGEX_BLOCK_INVALID: &str = "E1609";
    pub const REGEX_BLOCK_UNKNOWN_FLAG: &str = "E1610";
    pub const BLOCK_MISSING_CLOSING: &str = "E1611";
    pub const BLOCK_TYPE_MISMATCH: &str = "E1612";

    // Mixin errors (E17xx)
    pub const MIXIN_NOT_FOUND: &str = "E1701";
    pub const MIXIN_METHOD_CONFLICT: &str = "E1702";
    pub const MIXIN_MISSING_REQUIRED: &str = "E1703";
    pub const MIXIN_CIRCULAR_DEPENDENCY: &str = "E1704";
    pub const MIXIN_INVALID_USE: &str = "E1705";
    pub const MIXIN_FIELD_CONFLICT: &str = "E1706";
    pub const MIXIN_SELF_REFERENCE: &str = "E1707";
    pub const MIXIN_TYPE_MISMATCH: &str = "E1708";

    // SDN errors (E18xx)
    pub const SDN_SYNTAX_ERROR: &str = "E1801";
    pub const SDN_UNKNOWN_KEY: &str = "E1802";
    pub const SDN_TYPE_MISMATCH: &str = "E1803";
    pub const SDN_MISSING_REQUIRED: &str = "E1804";
    pub const SDN_DUPLICATE_KEY: &str = "E1805";
    pub const SDN_INVALID_VALUE: &str = "E1806";
    pub const SDN_NESTING_LIMIT: &str = "E1807";
    pub const SDN_CIRCULAR_REFERENCE: &str = "E1808";

    // DI errors (E19xx)
    pub const DI_MISSING_BINDING: &str = "E1901";
    pub const DI_AMBIGUOUS_BINDING: &str = "E1902";
    pub const DI_CIRCULAR_DEPENDENCY: &str = "E1903";
    pub const DI_INVALID_SCOPE: &str = "E1904";
    pub const DI_INJECT_FAILED: &str = "E1905";
    pub const DI_INVALID_ATTRIBUTE: &str = "E1906";
    pub const DI_SCOPE_MISMATCH: &str = "E1907";
    pub const DI_MOCK_NOT_TEST: &str = "E1908";

    // Architecture rule errors (E1Axx)
    pub const ARCH_FORBIDDEN_IMPORT: &str = "E1A01";
    pub const ARCH_FORBIDDEN_DEPEND: &str = "E1A02";
    pub const ARCH_LAYER_VIOLATION: &str = "E1A03";
    pub const ARCH_INVALID_RULE: &str = "E1A04";
    pub const ARCH_CONFLICTING_RULES: &str = "E1A05";
    pub const ARCH_CIRCULAR_MODULES: &str = "E1A06";

    // Codegen errors (E20xx)
    pub const UNSUPPORTED_FEATURE: &str = "E2001";
    pub const FFI_ERROR: &str = "E2002";
    pub const FAILED_BUILD_LOAD: &str = "E2003";
    pub const FAILED_BUILD_STORE: &str = "E2004";
    pub const FAILED_BUILD_ALLOCA: &str = "E2005";
    pub const FAILED_BUILD_CALL: &str = "E2006";
    pub const FAILED_TO_CAST: &str = "E2007";
    pub const FAILED_BUILD_GEP: &str = "E2008";
    pub const UNSUPPORTED_RETURN_TYPE: &str = "E2009";
    pub const IMMUTABLE_ASSIGNMENT: &str = "E2010";

    // Runtime errors (E30xx)
    pub const DIVISION_BY_ZERO: &str = "E3001";
    pub const INDEX_OUT_OF_BOUNDS: &str = "E3002";
    pub const STACK_OVERFLOW: &str = "E3003";
    pub const ASSERTION_FAILED: &str = "E3004";
    pub const TIMEOUT: &str = "E3005";
    pub const AWAIT_FAILED: &str = "E3006";
    pub const PROMISE_REJECTED: &str = "E3007";
    pub const FUNCTION_NOT_FOUND: &str = "E3008";
    pub const METHOD_NOT_FOUND: &str = "E3009";

    // FFI errors (E40xx)
    pub const TYPE_NOT_FFI_SAFE: &str = "E4005";

    // Contract errors (E50xx)
    pub const CONTRACT_PRECONDITION_FAILED: &str = "E5001";
    pub const CONTRACT_POSTCONDITION_FAILED: &str = "E5002";
    pub const CONTRACT_INVARIANT_FAILED: &str = "E5003";
    pub const CONTRACT_OLD_EXPR_FAILED: &str = "E5004";
}
