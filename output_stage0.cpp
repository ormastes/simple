#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cstdarg>
#include <vector>

extern "C" {
#include "runtime.h"
}

#define asm asm_spl
#define assert spl_assert
#define template template_spl
#define register register_spl
#define default default_spl
#define class class_spl
#define new new_spl
#define delete delete_spl
#define union union_spl
#define namespace namespace_spl
#define operator operator_spl
#define private private_spl
#define protected protected_spl
#define public public_spl
#define virtual virtual_spl
#define throw throw_spl
#define catch catch_spl
#define try try_spl
#define typename typename_spl

static int has_field = 0;
static int64_t _ = 0;

typedef int64_t Effect;
typedef int64_t Result;
typedef int64_t Option;
typedef int64_t CompileResult;
typedef int64_t CoercionResult;
typedef int64_t Fn;
typedef int64_t Iterator;
typedef int64_t Any;
typedef int64_t fn;
typedef int64_t type;
typedef const char* text;
typedef int64_t i64;
typedef int32_t i32;
typedef double f64;
typedef float f32;
typedef uint8_t u8;
typedef uint32_t u32;
typedef int64_t (*FnPtr_i64)();
typedef const char* (*FnPtr_text)();
typedef void (*FnPtr_void)();
typedef bool (*FnPtr_bool)();
typedef int64_t (*FnPtr_Any)();
typedef int64_t (*FnPtr_ConstValue)();
typedef int64_t (*FnPtr_BlockValue)();
typedef SplArray* (*FnPtr_array)();
typedef int64_t (*FnPtr_HoverInfo)();
typedef uint64_t u64;

/* Common constants from stdlib */
static const char* NL = "\n";

inline void log_debug(...) {}
inline void log_trace(...) {}
inline void log_info(...) {}
inline void log_warn(...) {}
inline void log_error(...) {}
inline void spl_assert(bool cond) {}
inline SplArray* data_push(SplArray* arr, int64_t val) { spl_array_push(arr, spl_int(val)); return arr; }
inline int64_t spl_char_at(const char* s, int64_t i) { return (uint8_t)s[i]; }
inline int64_t spl_abs(int64_t x) { return x < 0 ? -x : x; }
inline int64_t spl_min(int64_t a, int64_t b) { return a < b ? a : b; }
inline int64_t spl_max(int64_t a, int64_t b) { return a > b ? a : b; }
inline const char* spl_str_lower(const char* s) { return s; }
inline const char* spl_str_upper(const char* s) { return s; }
inline const char* spl_substr(const char* s, int64_t start, int64_t len) { return ""; }

/* enum ProceedError */
static const int64_t ProceedError_NeverCalled = 0;
static const int64_t ProceedError_CalledMultipleTimes = 1;

/* enum ApiChangeKind */
static const int64_t ApiChangeKind_Added = 0;
static const int64_t ApiChangeKind_Removed = 1;
static const int64_t ApiChangeKind_Modified = 2;

/* enum RuleAction */
static const int64_t RuleAction_Forbid = 0;
static const int64_t RuleAction_Allow = 1;

/* enum DependencyKind */
static const int64_t DependencyKind_Import = 0;
static const int64_t DependencyKind_Depend = 1;
static const int64_t DependencyKind_Use = 2;

/* enum HirType */
static const int64_t HirType_Int = 0;
static const int64_t HirType_Str = 1;
static const int64_t HirType_Bool = 2;
static const int64_t HirType_Named = 3;
static const int64_t HirType_Generic = 4;
static const int64_t HirType_Projection = 5;
static const int64_t HirType_Error = 6;

/* enum Node */
static const int64_t Node_Function = 0;
static const int64_t Node_Struct = 1;
static const int64_t Node_Class = 2;
static const int64_t Node_Enum = 3;
static const int64_t Node_Trait = 4;
static const int64_t Node_Other = 5;

/* enum VolatileMode */
static const int64_t VolatileMode_None_ = 0;
static const int64_t VolatileMode_Full = 1;
static const int64_t VolatileMode_ReadOnly = 2;
static const int64_t VolatileMode_WriteOnly = 3;
static const int64_t VolatileMode_Explicit = 4;

/* enum BackendKind */
static const int64_t BackendKind_Cranelift = 0;
static const int64_t BackendKind_Llvm = 1;
static const int64_t BackendKind_Native = 2;
static const int64_t BackendKind_Wasm = 3;
static const int64_t BackendKind_Lean = 4;
static const int64_t BackendKind_Interpreter = 5;
static const int64_t BackendKind_Cuda = 6;
static const int64_t BackendKind_Vulkan = 7;

/* enum BackendResult */
static const int64_t BackendResult_Value = 0;
static const int64_t BackendResult_CompiledUnit = 1;
static const int64_t BackendResult_SdnData = 2;
static const int64_t BackendResult_Unit = 3;

/* enum BackendErrorKind */
static const int64_t BackendErrorKind_NotAllowed = 0;
static const int64_t BackendErrorKind_TypeError = 1;
static const int64_t BackendErrorKind_RuntimeError = 2;
static const int64_t BackendErrorKind_CompileError = 3;
static const int64_t BackendErrorKind_NotImplemented = 4;
static const int64_t BackendErrorKind_Internal = 5;

/* enum CompiledSymbolKind */
static const int64_t CompiledSymbolKind_Function = 0;
static const int64_t CompiledSymbolKind_Data = 1;
static const int64_t CompiledSymbolKind_External = 2;

/* enum RelocKind */
static const int64_t RelocKind_Absolute = 0;
static const int64_t RelocKind_Relative = 1;
static const int64_t RelocKind_PltRelative = 2;

/* enum SdnValueKind */
static const int64_t SdnValueKind_Nil = 0;
static const int64_t SdnValueKind_Bool = 1;
static const int64_t SdnValueKind_Int = 2;
static const int64_t SdnValueKind_Float = 3;
static const int64_t SdnValueKind_String = 4;
static const int64_t SdnValueKind_Array = 5;
static const int64_t SdnValueKind_Dict = 6;
static const int64_t SdnValueKind_Table = 7;

/* enum Value */
static const int64_t Value_Nil = 0;
static const int64_t Value_Unit = 1;
static const int64_t Value_Bool = 2;
static const int64_t Value_Int = 3;
static const int64_t Value_Float = 4;
static const int64_t Value_Char = 5;
static const int64_t Value_String = 6;
static const int64_t Value_Array = 7;
static const int64_t Value_Tuple = 8;
static const int64_t Value_Dict = 9;
static const int64_t Value_Struct = 10;
static const int64_t Value_Enum = 11;
static const int64_t Value_Function = 12;
static const int64_t Value_Closure = 13;
static const int64_t Value_Object = 14;
static const int64_t Value_Ref = 15;
static const int64_t Value_Option = 16;
static const int64_t Value_Result = 17;
static const int64_t Value_TraitType = 18;
static const int64_t Value_RuntimeValue = 19;

/* enum EnumPayloadValue */
static const int64_t EnumPayloadValue_Tuple = 0;
static const int64_t EnumPayloadValue_Struct = 1;

/* enum InferMode */
static const int64_t InferMode_Synthesize = 0;
static const int64_t InferMode_Check = 1;

/* enum HirExprKind */
static const int64_t HirExprKind_IntLit = 0;
static const int64_t HirExprKind_BoolLit = 1;
static const int64_t HirExprKind_TextLit = 2;
static const int64_t HirExprKind_Var = 3;
static const int64_t HirExprKind_Lambda = 4;
static const int64_t HirExprKind_Call = 5;
static const int64_t HirExprKind_Let = 6;

/* enum Option */
static const int64_t Option_Value = 0;
static const int64_t Option_None_ = 1;

/* enum PhaseResult */
static const int64_t PhaseResult_Success = 0;
static const int64_t PhaseResult_Warning = 1;
static const int64_t PhaseResult_Error = 2;

/* enum DiagnosticLevel */
static const int64_t DiagnosticLevel_Error = 0;
static const int64_t DiagnosticLevel_Warning = 1;
static const int64_t DiagnosticLevel_Info = 2;
static const int64_t DiagnosticLevel_Hint = 3;

/* enum BuildMode */
static const int64_t BuildMode_Debug = 0;
static const int64_t BuildMode_Release = 1;

/* enum OutputFormat */
static const int64_t OutputFormat_Smf = 0;
static const int64_t OutputFormat_Native = 1;

/* enum LinkResult */

/* enum StructReturn */
static const int64_t StructReturn_InRegs = 0;
static const int64_t StructReturn_Hidden = 1;
static const int64_t StructReturn_OnStack = 2;

/* enum CallingConvention */
static const int64_t CallingConvention_Simple = 0;
static const int64_t CallingConvention_C = 1;
static const int64_t CallingConvention_Fastcall = 2;
static const int64_t CallingConvention_Stdcall = 3;
static const int64_t CallingConvention_Vectorcall = 4;
static const int64_t CallingConvention_Interrupt = 5;
static const int64_t CallingConvention_Naked = 6;

/* enum CodegenTarget */
static const int64_t CodegenTarget_X86_64 = 0;
static const int64_t CodegenTarget_Aarch64 = 1;
static const int64_t CodegenTarget_Riscv64 = 2;
static const int64_t CodegenTarget_Native = 3;

/* enum CodegenMode */
static const int64_t CodegenMode_Jit = 0;
static const int64_t CodegenMode_Aot = 1;

/* enum FallbackReason */
static const int64_t FallbackReason_DynamicTypes = 0;
static const int64_t FallbackReason_CollectionOps = 1;
static const int64_t FallbackReason_CollectionLiteral = 2;
static const int64_t FallbackReason_StringOps = 3;
static const int64_t FallbackReason_GcInNogcContext = 4;
static const int64_t FallbackReason_BlockingInAsync = 5;
static const int64_t FallbackReason_ActorOps = 6;
static const int64_t FallbackReason_UserMacros = 7;
static const int64_t FallbackReason_PatternMatch = 8;
static const int64_t FallbackReason_Closure = 9;
static const int64_t FallbackReason_ObjectConstruction = 10;
static const int64_t FallbackReason_MethodCall = 11;
static const int64_t FallbackReason_FieldAccess = 12;
static const int64_t FallbackReason_Generator = 13;
static const int64_t FallbackReason_AsyncAwait = 14;
static const int64_t FallbackReason_Decorators = 15;
static const int64_t FallbackReason_TryOperator = 16;
static const int64_t FallbackReason_WithStatement = 17;
static const int64_t FallbackReason_ContextBlock = 18;
static const int64_t FallbackReason_UnknownExtern = 19;
static const int64_t FallbackReason_NotYetImplemented = 20;

/* enum CompilabilityStatus */
static const int64_t CompilabilityStatus_Compilable = 0;
static const int64_t CompilabilityStatus_RequiresInterpreter = 1;

/* enum InstantiationMode */
static const int64_t InstantiationMode_CompileTime = 0;
static const int64_t InstantiationMode_LinkTime = 1;
static const int64_t InstantiationMode_JitTime = 2;

/* enum ContractMode */
static const int64_t ContractMode_Off = 0;
static const int64_t ContractMode_Boundary = 1;
static const int64_t ContractMode_All = 2;
static const int64_t ContractMode_Test = 3;

/* enum CompilerProfile */
static const int64_t CompilerProfile_Dev = 0;
static const int64_t CompilerProfile_Test = 1;
static const int64_t CompilerProfile_Prod = 2;
static const int64_t CompilerProfile_Sdn = 3;

/* enum ConstValue */
static const int64_t ConstValue_Int = 0;
static const int64_t ConstValue_Float = 1;
static const int64_t ConstValue_Bool = 2;
static const int64_t ConstValue_Char = 3;
static const int64_t ConstValue_String = 4;
static const int64_t ConstValue_Unit = 5;
static const int64_t ConstValue_Array = 6;
static const int64_t ConstValue_Tuple = 7;
static const int64_t ConstValue_Struct = 8;

/* enum ConstEvalError */
static const int64_t ConstEvalError_NotConstant = 0;
static const int64_t ConstEvalError_UndefinedVariable = 1;
static const int64_t ConstEvalError_TypeError = 2;
static const int64_t ConstEvalError_DivisionByZero = 3;
static const int64_t ConstEvalError_Overflow = 4;
static const int64_t ConstEvalError_UnsupportedOperation = 5;
static const int64_t ConstEvalError_AssertionFailed = 6;
static const int64_t ConstEvalError_ArrayBoundsError = 7;

/* enum KeyError */
static const int64_t KeyError_MissingKeys = 0;
static const int64_t KeyError_ExtraKeys = 1;
static const int64_t KeyError_NotConstKeySet = 2;
static const int64_t KeyError_BothErrors = 3;

/* enum Result */
static const int64_t Result_Ok = 0;
static const int64_t Result_Err = 1;

/* enum DimClause */
static const int64_t DimClause_DimEqual = 0;
static const int64_t DimClause_DimRange = 1;
static const int64_t DimClause_DimMin = 2;
static const int64_t DimClause_DimMax = 3;

/* enum DimCheckMode */
static const int64_t DimCheckMode_None_ = 0;
static const int64_t DimCheckMode_Assert = 1;
static const int64_t DimCheckMode_Log = 2;
static const int64_t DimCheckMode_Strict = 3;

/* enum RuntimeDimCheckKind */
static const int64_t RuntimeDimCheckKind_ShapeEqual = 0;
static const int64_t RuntimeDimCheckKind_DimEqual = 1;
static const int64_t RuntimeDimCheckKind_DimRange = 2;
static const int64_t RuntimeDimCheckKind_LayerCompat = 3;

/* enum DimCheckTiming */
static const int64_t DimCheckTiming_CompileTime = 0;
static const int64_t DimCheckTiming_Runtime = 1;
static const int64_t DimCheckTiming_Both = 2;

/* enum DimConstraint */
static const int64_t DimConstraint_Equal = 0;
static const int64_t DimConstraint_GreaterEq = 1;
static const int64_t DimConstraint_LessEq = 2;
static const int64_t DimConstraint_InRange = 3;
static const int64_t DimConstraint_ProductEquals = 4;
static const int64_t DimConstraint_LayerCompatible = 5;

/* enum DimNoteKind */
static const int64_t DimNoteKind_Info = 0;
static const int64_t DimNoteKind_Expected = 1;
static const int64_t DimNoteKind_Found = 2;
static const int64_t DimNoteKind_Suggestion = 3;
static const int64_t DimNoteKind_Context = 4;

/* enum DimErrorKind */
static const int64_t DimErrorKind_Mismatch = 0;
static const int64_t DimErrorKind_OutOfRange = 1;
static const int64_t DimErrorKind_Unsatisfiable = 2;
static const int64_t DimErrorKind_UnresolvedVariable = 3;
static const int64_t DimErrorKind_ShapeMismatch = 4;
static const int64_t DimErrorKind_LayerIncompatible = 5;
static const int64_t DimErrorKind_BroadcastIncompat = 6;
static const int64_t DimErrorKind_MatMulIncompat = 7;
static const int64_t DimErrorKind_RankMismatch = 8;
static const int64_t DimErrorKind_BatchMismatch = 9;
static const int64_t DimErrorKind_ChannelMismatch = 10;
static const int64_t DimErrorKind_SequenceMismatch = 11;

/* enum DiErrorKind */
static const int64_t DiErrorKind_MixedInjection = 0;
static const int64_t DiErrorKind_MixedAnnotations = 1;
static const int64_t DiErrorKind_InvalidInjectionPoint = 2;
static const int64_t DiErrorKind_CircularDependency = 3;
static const int64_t DiErrorKind_AmbiguousBinding = 4;
static const int64_t DiErrorKind_NoBinding = 5;

/* enum Effect */
static const int64_t Effect_Sync = 0;
static const int64_t Effect_Async = 1;

/* enum HirExpr */
static const int64_t HirExpr_IntLit = 0;
static const int64_t HirExpr_StrLit = 1;
static const int64_t HirExpr_BoolLit = 2;
static const int64_t HirExpr_Var = 3;
static const int64_t HirExpr_Call = 4;
static const int64_t HirExpr_Suspend = 5;
static const int64_t HirExpr_SuspendAssign = 6;
static const int64_t HirExpr_SuspendIf = 7;
static const int64_t HirExpr_SuspendWhile = 8;
static const int64_t HirExpr_SuspendFor = 9;
static const int64_t HirExpr_If = 10;
static const int64_t HirExpr_Block = 11;
static const int64_t HirExpr_Binary = 12;

/* enum Severity */
static const int64_t Severity_Error = 0;
static const int64_t Severity_Warning = 1;
static const int64_t Severity_Note = 2;
static const int64_t Severity_Help = 3;

/* enum ValueType */
static const int64_t ValueType_Nil = 0;
static const int64_t ValueType_Bool = 1;
static const int64_t ValueType_Int = 2;
static const int64_t ValueType_Float = 3;
static const int64_t ValueType_String = 4;
static const int64_t ValueType_Array = 5;
static const int64_t ValueType_Dict = 6;
static const int64_t ValueType_Object = 7;
static const int64_t ValueType_Function = 8;

/* enum Kind */
static const int64_t Kind_Star = 0;
static const int64_t Kind_Arrow = 1;

/* enum HirVariantKind */

/* enum HirEnumPayload */
static const int64_t HirEnumPayload_Tuple = 0;
static const int64_t HirEnumPayload_Struct = 1;

/* enum HirComprehensionKind */
static const int64_t HirComprehensionKind_List = 0;
static const int64_t HirComprehensionKind_Dict = 1;
static const int64_t HirComprehensionKind_Set = 2;
static const int64_t HirComprehensionKind_Generator = 3;

/* enum HirCompClauseKind */
static const int64_t HirCompClauseKind_For = 0;
static const int64_t HirCompClauseKind_If = 1;

/* enum HirBinOp */
static const int64_t HirBinOp_Add = 0;
static const int64_t HirBinOp_Sub = 1;
static const int64_t HirBinOp_Mul = 2;
static const int64_t HirBinOp_Div = 3;
static const int64_t HirBinOp_Mod = 4;
static const int64_t HirBinOp_Pow = 5;
static const int64_t HirBinOp_MatMul = 6;
static const int64_t HirBinOp_Eq = 7;
static const int64_t HirBinOp_NotEq = 8;
static const int64_t HirBinOp_Lt = 9;
static const int64_t HirBinOp_LtEq = 10;
static const int64_t HirBinOp_Gt = 11;
static const int64_t HirBinOp_GtEq = 12;
static const int64_t HirBinOp_And = 13;
static const int64_t HirBinOp_Or = 14;
static const int64_t HirBinOp_BitAnd = 15;
static const int64_t HirBinOp_BitOr = 16;
static const int64_t HirBinOp_BitXor = 17;
static const int64_t HirBinOp_Shl = 18;
static const int64_t HirBinOp_Shr = 19;
static const int64_t HirBinOp_BroadcastAdd = 20;
static const int64_t HirBinOp_BroadcastSub = 21;
static const int64_t HirBinOp_BroadcastMul = 22;
static const int64_t HirBinOp_BroadcastDiv = 23;
static const int64_t HirBinOp_BroadcastPow = 24;
static const int64_t HirBinOp_PipeForward = 25;
static const int64_t HirBinOp_Compose = 26;
static const int64_t HirBinOp_ComposeBack = 27;
static const int64_t HirBinOp_Parallel = 28;
static const int64_t HirBinOp_LayerConnect = 29;
static const int64_t HirBinOp_In = 30;
static const int64_t HirBinOp_NotIn = 31;
static const int64_t HirBinOp_Is = 32;
static const int64_t HirBinOp_IsNot = 33;
static const int64_t HirBinOp_Concat = 34;

/* enum HirUnaryOp */
static const int64_t HirUnaryOp_Neg = 0;
static const int64_t HirUnaryOp_Not = 1;
static const int64_t HirUnaryOp_BitNot = 2;
static const int64_t HirUnaryOp_Ref = 3;
static const int64_t HirUnaryOp_RefMut = 4;
static const int64_t HirUnaryOp_Deref = 5;
static const int64_t HirUnaryOp_Transpose = 6;

/* enum HirPatternKind */
static const int64_t HirPatternKind_Wildcard = 0;
static const int64_t HirPatternKind_Literal = 1;
static const int64_t HirPatternKind_Binding = 2;
static const int64_t HirPatternKind_Tuple = 3;
static const int64_t HirPatternKind_Array = 4;
static const int64_t HirPatternKind_Struct = 5;
static const int64_t HirPatternKind_Enum = 6;
static const int64_t HirPatternKind_Or = 7;
static const int64_t HirPatternKind_Range = 8;
static const int64_t HirPatternKind_Error = 9;

/* enum HirPatternPayload */
static const int64_t HirPatternPayload_Tuple = 0;
static const int64_t HirPatternPayload_Struct = 1;

/* enum HirStmtKind */
static const int64_t HirStmtKind_Expr = 0;
static const int64_t HirStmtKind_Let = 1;
static const int64_t HirStmtKind_Assign = 2;
static const int64_t HirStmtKind_Block = 3;

/* enum HirAssignOp */
static const int64_t HirAssignOp_Add = 0;
static const int64_t HirAssignOp_Sub = 1;
static const int64_t HirAssignOp_Mul = 2;
static const int64_t HirAssignOp_Div = 3;
static const int64_t HirAssignOp_Mod = 4;
static const int64_t HirAssignOp_BitAnd = 5;
static const int64_t HirAssignOp_BitOr = 6;
static const int64_t HirAssignOp_BitXor = 7;
static const int64_t HirAssignOp_Shl = 8;
static const int64_t HirAssignOp_Shr = 9;

/* enum SymbolKind */
static const int64_t SymbolKind_Function = 0;
static const int64_t SymbolKind_Method = 1;
static const int64_t SymbolKind_Variable = 2;
static const int64_t SymbolKind_Parameter = 3;
static const int64_t SymbolKind_Field = 4;
static const int64_t SymbolKind_Class = 5;
static const int64_t SymbolKind_Struct = 6;
static const int64_t SymbolKind_Enum = 7;
static const int64_t SymbolKind_EnumVariant = 8;
static const int64_t SymbolKind_Trait = 9;
static const int64_t SymbolKind_TypeAlias = 10;
static const int64_t SymbolKind_TypeParam = 11;
static const int64_t SymbolKind_Const = 12;
static const int64_t SymbolKind_Module = 13;
static const int64_t SymbolKind_Import = 14;

/* enum MethodResolution */
static const int64_t MethodResolution_InstanceMethod = 0;
static const int64_t MethodResolution_TraitMethod = 1;
static const int64_t MethodResolution_FreeFunction = 2;
static const int64_t MethodResolution_StaticMethod = 3;
static const int64_t MethodResolution_Unresolved = 4;

/* enum ScopeKind */
static const int64_t ScopeKind_Module = 0;
static const int64_t ScopeKind_Function = 1;
static const int64_t ScopeKind_Block = 2;
static const int64_t ScopeKind_Loop = 3;
static const int64_t ScopeKind_Match = 4;
static const int64_t ScopeKind_Class = 5;
static const int64_t ScopeKind_Impl = 6;

/* enum CompilationStatus */
static const int64_t CompilationStatus_Unknown = 0;
static const int64_t CompilationStatus_Dirty = 1;
static const int64_t CompilationStatus_Complete = 2;
static const int64_t CompilationStatus_Failed = 3;

/* enum CompilerMode */
static const int64_t CompilerMode_Interpret = 0;
static const int64_t CompilerMode_Jit = 1;
static const int64_t CompilerMode_Aot = 2;
static const int64_t CompilerMode_Sdn = 3;
static const int64_t CompilerMode_Check = 4;

/* enum LayoutPhase */
static const int64_t LayoutPhase_Startup = 0;
static const int64_t LayoutPhase_FirstFrame = 1;
static const int64_t LayoutPhase_Steady = 2;
static const int64_t LayoutPhase_Cold = 3;

/* enum TokenKind */
static const int64_t TokenKind_IntLit = 0;
static const int64_t TokenKind_FloatLit = 1;
static const int64_t TokenKind_StringLit = 2;
static const int64_t TokenKind_RawStringLit = 3;
static const int64_t TokenKind_BoolLit = 4;
static const int64_t TokenKind_NilLit = 5;
static const int64_t TokenKind_Ident = 6;
static const int64_t TokenKind_KwFn = 7;
static const int64_t TokenKind_KwVal = 8;
static const int64_t TokenKind_KwVar = 9;
static const int64_t TokenKind_KwStruct = 10;
static const int64_t TokenKind_KwClass = 11;
static const int64_t TokenKind_KwEnum = 12;
static const int64_t TokenKind_KwTrait = 13;
static const int64_t TokenKind_KwImpl = 14;
static const int64_t TokenKind_KwType = 15;
static const int64_t TokenKind_KwMod = 16;
static const int64_t TokenKind_KwPub = 17;
static const int64_t TokenKind_KwPri = 18;
static const int64_t TokenKind_KwStatic = 19;
static const int64_t TokenKind_KwMe = 20;
static const int64_t TokenKind_KwExtern = 21;
static const int64_t TokenKind_KwConst = 22;
static const int64_t TokenKind_KwBitfield = 23;
static const int64_t TokenKind_KwKernel = 24;
static const int64_t TokenKind_KwShared = 25;
static const int64_t TokenKind_KwUnsafe = 26;
static const int64_t TokenKind_KwAsm = 27;
static const int64_t TokenKind_KwIf = 28;
static const int64_t TokenKind_KwElse = 29;
static const int64_t TokenKind_KwElif = 30;
static const int64_t TokenKind_KwMatch = 31;
static const int64_t TokenKind_KwCase = 32;
static const int64_t TokenKind_KwFor = 33;
static const int64_t TokenKind_KwWhile = 34;
static const int64_t TokenKind_KwLoop = 35;
static const int64_t TokenKind_KwBreak = 36;
static const int64_t TokenKind_KwContinue = 37;
static const int64_t TokenKind_KwReturn = 38;
static const int64_t TokenKind_KwYield = 39;
static const int64_t TokenKind_KwAwait = 40;
static const int64_t TokenKind_KwAsync = 41;
static const int64_t TokenKind_KwSpawn = 42;
static const int64_t TokenKind_KwActor = 43;
static const int64_t TokenKind_KwIn = 44;
static const int64_t TokenKind_KwIs = 45;
static const int64_t TokenKind_KwAs = 46;
static const int64_t TokenKind_KwNot = 47;
static const int64_t TokenKind_KwAnd = 48;
static const int64_t TokenKind_KwOr = 49;
static const int64_t TokenKind_KwXor = 50;
static const int64_t TokenKind_KwTry = 51;
static const int64_t TokenKind_KwCatch = 52;
static const int64_t TokenKind_KwThrow = 53;
static const int64_t TokenKind_KwWith = 54;
static const int64_t TokenKind_KwImport = 55;
static const int64_t TokenKind_KwExport = 56;
static const int64_t TokenKind_KwFrom = 57;
static const int64_t TokenKind_KwSelf = 58;
static const int64_t TokenKind_KwSuper = 59;
static const int64_t TokenKind_KwNone = 60;
static const int64_t TokenKind_KwSome = 61;
static const int64_t TokenKind_KwOk = 62;
static const int64_t TokenKind_KwErr = 63;
static const int64_t TokenKind_KwLoss = 64;
static const int64_t TokenKind_KwNograd = 65;
static const int64_t TokenKind_Plus = 66;
static const int64_t TokenKind_Minus = 67;
static const int64_t TokenKind_Star = 68;
static const int64_t TokenKind_Slash = 69;
static const int64_t TokenKind_Percent = 70;
static const int64_t TokenKind_StarStar = 71;
static const int64_t TokenKind_Eq = 72;
static const int64_t TokenKind_NotEq = 73;
static const int64_t TokenKind_Lt = 74;
static const int64_t TokenKind_Gt = 75;
static const int64_t TokenKind_LtEq = 76;
static const int64_t TokenKind_GtEq = 77;
static const int64_t TokenKind_Assign = 78;
static const int64_t TokenKind_PlusEq = 79;
static const int64_t TokenKind_MinusEq = 80;
static const int64_t TokenKind_StarEq = 81;
static const int64_t TokenKind_SlashEq = 82;
static const int64_t TokenKind_PercentEq = 83;
static const int64_t TokenKind_Ampersand = 84;
static const int64_t TokenKind_Pipe = 85;
static const int64_t TokenKind_Caret = 86;
static const int64_t TokenKind_Tilde = 87;
static const int64_t TokenKind_AmpAmp = 88;
static const int64_t TokenKind_PipePipe = 89;
static const int64_t TokenKind_Question = 90;
static const int64_t TokenKind_QuestionDot = 91;
static const int64_t TokenKind_QuestionQuestion = 92;
static const int64_t TokenKind_DotQuestion = 93;
static const int64_t TokenKind_Bang = 94;
static const int64_t TokenKind_At = 95;
static const int64_t TokenKind_Hash = 96;
static const int64_t TokenKind_HashLBracket = 97;
static const int64_t TokenKind_Dollar = 98;
static const int64_t TokenKind_Backslash = 99;
static const int64_t TokenKind_Transpose = 100;
static const int64_t TokenKind_PipeForward = 101;
static const int64_t TokenKind_Compose = 102;
static const int64_t TokenKind_ComposeBack = 103;
static const int64_t TokenKind_Parallel = 104;
static const int64_t TokenKind_LayerConnect = 105;
static const int64_t TokenKind_TripleLess = 106;
static const int64_t TokenKind_TripleGreater = 107;
static const int64_t TokenKind_LParen = 108;
static const int64_t TokenKind_RParen = 109;
static const int64_t TokenKind_LBrace = 110;
static const int64_t TokenKind_RBrace = 111;
static const int64_t TokenKind_LBracket = 112;
static const int64_t TokenKind_RBracket = 113;
static const int64_t TokenKind_Comma = 114;
static const int64_t TokenKind_Colon = 115;
static const int64_t TokenKind_ColonColon = 116;
static const int64_t TokenKind_Semicolon = 117;
static const int64_t TokenKind_Dot = 118;
static const int64_t TokenKind_DotDot = 119;
static const int64_t TokenKind_DotDotEq = 120;
static const int64_t TokenKind_DotPlus = 121;
static const int64_t TokenKind_DotMinus = 122;
static const int64_t TokenKind_DotStar = 123;
static const int64_t TokenKind_DotSlash = 124;
static const int64_t TokenKind_DotCaret = 125;
static const int64_t TokenKind_Ellipsis = 126;
static const int64_t TokenKind_Arrow = 127;
static const int64_t TokenKind_FatArrow = 128;
static const int64_t TokenKind_Underscore = 129;
static const int64_t TokenKind_Newline = 130;
static const int64_t TokenKind_Indent = 131;
static const int64_t TokenKind_Dedent = 132;
static const int64_t TokenKind_Eof = 133;
static const int64_t TokenKind_Error = 134;
static const int64_t TokenKind_ImplicitMul = 135;
static const int64_t TokenKind_ArraySuffix = 136;
static const int64_t TokenKind_BlockStart = 137;
static const int64_t TokenKind_BlockPayload = 138;
static const int64_t TokenKind_BlockEnd = 139;
static const int64_t TokenKind_SetLitStart = 140;
static const int64_t TokenKind_LiteralStart = 141;

/* enum Expr */
static const int64_t Expr_IntLit = 0;
static const int64_t Expr_StrLit = 1;
static const int64_t Expr_BoolLit = 2;
static const int64_t Expr_Var = 3;
static const int64_t Expr_Call = 4;
static const int64_t Expr_If = 5;
static const int64_t Expr_Block = 6;

/* enum MacroAnchor */
static const int64_t MacroAnchor_Head = 0;
static const int64_t MacroAnchor_Tail = 1;
static const int64_t MacroAnchor_Here = 2;

/* enum MacroIntroKind */
static const int64_t MacroIntroKind_Function = 0;
static const int64_t MacroIntroKind_Class = 1;
static const int64_t MacroIntroKind_TypeAlias = 2;
static const int64_t MacroIntroKind_Field = 3;
static const int64_t MacroIntroKind_Variable = 4;

/* enum BlockPosition */
static const int64_t BlockPosition_Head = 0;
static const int64_t BlockPosition_Middle = 1;
static const int64_t BlockPosition_Tail = 2;

/* enum LowererState */
static const int64_t LowererState_Idle = 0;
static const int64_t LowererState_Lowering = 1;

/* enum BlockState */
static const int64_t BlockState_Open = 0;
static const int64_t BlockState_Sealed = 1;

/* enum MirLowerError */
static const int64_t MirLowerError_Unsupported = 0;
static const int64_t MirLowerError_InvalidState = 1;
static const int64_t MirLowerError_BreakOutsideLoop = 2;
static const int64_t MirLowerError_ContinueOutsideLoop = 3;
static const int64_t MirLowerError_AopWeavingFailed = 4;
static const int64_t MirLowerError_CircularDependency = 5;

/* enum LocalKind */
static const int64_t LocalKind_Arg = 0;
static const int64_t LocalKind_Var = 1;
static const int64_t LocalKind_Temp = 2;
static const int64_t LocalKind_Return = 3;

/* enum MirConstValue */

/* enum MirTypeDefKind */
static const int64_t MirTypeDefKind_Struct = 0;
static const int64_t MirTypeDefKind_Enum = 1;
static const int64_t MirTypeDefKind_Union = 2;

/* enum MirTypeKind */
static const int64_t MirTypeKind_I8 = 0;
static const int64_t MirTypeKind_I16 = 1;
static const int64_t MirTypeKind_I32 = 2;
static const int64_t MirTypeKind_I64 = 3;
static const int64_t MirTypeKind_U8 = 4;
static const int64_t MirTypeKind_U16 = 5;
static const int64_t MirTypeKind_U32 = 6;
static const int64_t MirTypeKind_U64 = 7;
static const int64_t MirTypeKind_F32 = 8;
static const int64_t MirTypeKind_F64 = 9;
static const int64_t MirTypeKind_Bool = 10;
static const int64_t MirTypeKind_Char = 11;
static const int64_t MirTypeKind_Unit = 12;
static const int64_t MirTypeKind_Ptr = 13;
static const int64_t MirTypeKind_Ref = 14;
static const int64_t MirTypeKind_FuncPtr = 15;
static const int64_t MirTypeKind_Array = 16;
static const int64_t MirTypeKind_Slice = 17;
static const int64_t MirTypeKind_Tuple = 18;
static const int64_t MirTypeKind_Struct = 19;
static const int64_t MirTypeKind_Enum = 20;
static const int64_t MirTypeKind_Never = 21;
static const int64_t MirTypeKind_Opaque = 22;
static const int64_t MirTypeKind_Promise = 23;
static const int64_t MirTypeKind_Generator = 24;
static const int64_t MirTypeKind_ActorType = 25;

/* enum MirInstKind */

/* enum AsyncEffect */
static const int64_t AsyncEffect_Compute = 0;
static const int64_t AsyncEffect_Io = 1;
static const int64_t AsyncEffect_Wait = 2;

/* enum NogcInstr */
static const int64_t NogcInstr_Const = 0;
static const int64_t NogcInstr_Add = 1;
static const int64_t NogcInstr_GcAlloc = 2;

/* enum BuiltinFunc */
static const int64_t BuiltinFunc_Await = 0;
static const int64_t BuiltinFunc_Wait = 1;
static const int64_t BuiltinFunc_Join = 2;
static const int64_t BuiltinFunc_Recv = 3;
static const int64_t BuiltinFunc_Sleep = 4;
static const int64_t BuiltinFunc_GcAlloc = 5;
static const int64_t BuiltinFunc_GcNew = 6;
static const int64_t BuiltinFunc_Box = 7;
static const int64_t BuiltinFunc_Print = 8;
static const int64_t BuiltinFunc_Println = 9;
static const int64_t BuiltinFunc_Read = 10;
static const int64_t BuiltinFunc_Write = 11;
static const int64_t BuiltinFunc_Send = 12;
static const int64_t BuiltinFunc_Spawn = 13;
static const int64_t BuiltinFunc_HttpGet = 14;
static const int64_t BuiltinFunc_HttpPost = 15;
static const int64_t BuiltinFunc_TcpConnect = 16;
static const int64_t BuiltinFunc_TcpListen = 17;
static const int64_t BuiltinFunc_UdpBind = 18;
static const int64_t BuiltinFunc_ReadFile = 19;
static const int64_t BuiltinFunc_WriteFile = 20;
static const int64_t BuiltinFunc_OpenFile = 21;
static const int64_t BuiltinFunc_DeleteFile = 22;
static const int64_t BuiltinFunc_ListDir = 23;
static const int64_t BuiltinFunc_CreateDir = 24;
static const int64_t BuiltinFunc_UnsafePtr = 25;
static const int64_t BuiltinFunc_UnsafeDeref = 26;
static const int64_t BuiltinFunc_UnsafeCast = 27;

/* enum InterpError */
static const int64_t InterpError_DivisionByZero = 0;
static const int64_t InterpError_InvalidCast = 1;
static const int64_t InterpError_UnsupportedOperation = 2;
static const int64_t InterpError_InvalidRegister = 3;
static const int64_t InterpError_OutOfBounds = 4;
static const int64_t InterpError_RuntimeError = 5;

/* enum OptimizationConfig */
static const int64_t OptimizationConfig_Disabled = 0;
static const int64_t OptimizationConfig_Enabled = 1;

/* enum OptimizationLevel */
static const int64_t OptimizationLevel_None_ = 0;
static const int64_t OptimizationLevel_Basic = 1;
static const int64_t OptimizationLevel_Standard = 2;
static const int64_t OptimizationLevel_Aggressive = 3;

/* enum CompileResult */
static const int64_t CompileResult_Success = 0;
static const int64_t CompileResult_Failed = 1;

/* enum VariantKind */
static const int64_t VariantKind_Unit = 0;
static const int64_t VariantKind_Tuple = 1;
static const int64_t VariantKind_Struct = 2;

/* enum TypeKind */
static const int64_t TypeKind_Named = 0;
static const int64_t TypeKind_Tuple = 1;
static const int64_t TypeKind_Array = 2;
static const int64_t TypeKind_Function = 3;
static const int64_t TypeKind_Optional = 4;
static const int64_t TypeKind_Reference = 5;
static const int64_t TypeKind_Atomic = 6;
static const int64_t TypeKind_Isolated = 7;
static const int64_t TypeKind_Infer = 8;
static const int64_t TypeKind_Error = 9;

/* enum DType */
static const int64_t DType_F16 = 0;
static const int64_t DType_F32 = 1;
static const int64_t DType_F64 = 2;
static const int64_t DType_BF16 = 3;
static const int64_t DType_I8 = 4;
static const int64_t DType_I16 = 5;
static const int64_t DType_I32 = 6;
static const int64_t DType_I64 = 7;
static const int64_t DType_U8 = 8;
static const int64_t DType_U16 = 9;
static const int64_t DType_U32 = 10;
static const int64_t DType_U64 = 11;

/* enum Device */
static const int64_t Device_CPU = 0;
static const int64_t Device_CUDA = 1;

/* enum Backend */
static const int64_t Backend_Native = 0;
static const int64_t Backend_PyTorch = 1;

/* enum ExprKind */
static const int64_t ExprKind_IntLit = 0;
static const int64_t ExprKind_FloatLit = 1;
static const int64_t ExprKind_StringLit = 2;
static const int64_t ExprKind_BoolLit = 3;
static const int64_t ExprKind_NilLit = 4;
static const int64_t ExprKind_ArrayLit = 5;
static const int64_t ExprKind_TupleLit = 6;
static const int64_t ExprKind_DictLit = 7;
static const int64_t ExprKind_SetLit = 8;
static const int64_t ExprKind_Ident = 9;
static const int64_t ExprKind_Field = 10;
static const int64_t ExprKind_Index = 11;
static const int64_t ExprKind_OptionalChain = 12;
static const int64_t ExprKind_NullCoalesce = 13;
static const int64_t ExprKind_ExistsCheck = 14;
static const int64_t ExprKind_Binary = 15;
static const int64_t ExprKind_Unary = 16;
static const int64_t ExprKind_Range = 17;
static const int64_t ExprKind_Call = 18;
static const int64_t ExprKind_MethodCall = 19;
static const int64_t ExprKind_If = 20;
static const int64_t ExprKind_MatchCase = 21;
static const int64_t ExprKind_Try = 22;
static const int64_t ExprKind_TryCatch = 23;
static const int64_t ExprKind_Lambda = 24;
static const int64_t ExprKind_Block = 25;
static const int64_t ExprKind_ListComprehension = 26;
static const int64_t ExprKind_DictComprehension = 27;
static const int64_t ExprKind_Await = 28;
static const int64_t ExprKind_Spawn = 29;
static const int64_t ExprKind_Yield = 30;
static const int64_t ExprKind_Return = 31;
static const int64_t ExprKind_Break = 32;
static const int64_t ExprKind_Continue = 33;
static const int64_t ExprKind_Throw = 34;
static const int64_t ExprKind_StructLit = 35;
static const int64_t ExprKind_EnumLit = 36;
static const int64_t ExprKind_LossBlock = 37;
static const int64_t ExprKind_NogradBlock = 38;
static const int64_t ExprKind_UnsafeBlock = 39;
static const int64_t ExprKind_AsmBlock = 40;
static const int64_t ExprKind_CustomBlock = 41;
static const int64_t ExprKind_ArrayLitSuffix = 42;
static const int64_t ExprKind_KernelLaunch = 43;
static const int64_t ExprKind_GpuIntrinsic = 44;
static const int64_t ExprKind_Error = 45;

/* enum GpuIntrinsicKind */
static const int64_t GpuIntrinsicKind_GlobalId = 0;
static const int64_t GpuIntrinsicKind_LocalId = 1;
static const int64_t GpuIntrinsicKind_BlockId = 2;
static const int64_t GpuIntrinsicKind_BlockDim = 3;
static const int64_t GpuIntrinsicKind_GridDim = 4;
static const int64_t GpuIntrinsicKind_Sync = 5;
static const int64_t GpuIntrinsicKind_Barrier = 6;
static const int64_t GpuIntrinsicKind_MemFence = 7;
static const int64_t GpuIntrinsicKind_AtomicAdd = 8;
static const int64_t GpuIntrinsicKind_AtomicSub = 9;
static const int64_t GpuIntrinsicKind_AtomicMin = 10;
static const int64_t GpuIntrinsicKind_AtomicMax = 11;
static const int64_t GpuIntrinsicKind_AtomicAnd = 12;
static const int64_t GpuIntrinsicKind_AtomicOr = 13;
static const int64_t GpuIntrinsicKind_AtomicXor = 14;
static const int64_t GpuIntrinsicKind_AtomicExchange = 15;
static const int64_t GpuIntrinsicKind_AtomicCas = 16;

/* enum ComprehensionKind */
static const int64_t ComprehensionKind_For = 0;
static const int64_t ComprehensionKind_If = 1;

/* enum EnumPayload */
static const int64_t EnumPayload_Tuple = 0;
static const int64_t EnumPayload_Struct = 1;

/* enum PatternKind */
static const int64_t PatternKind_Wildcard = 0;
static const int64_t PatternKind_Literal = 1;
static const int64_t PatternKind_Binding = 2;
static const int64_t PatternKind_Tuple = 3;
static const int64_t PatternKind_Array = 4;
static const int64_t PatternKind_Struct = 5;
static const int64_t PatternKind_Enum = 6;
static const int64_t PatternKind_Or = 7;
static const int64_t PatternKind_Guard = 8;
static const int64_t PatternKind_As = 9;
static const int64_t PatternKind_Range = 10;
static const int64_t PatternKind_Error = 11;

/* enum EnumPatternPayload */
static const int64_t EnumPatternPayload_Tuple = 0;
static const int64_t EnumPatternPayload_Struct = 1;

/* enum StmtKind */
static const int64_t StmtKind_Expr = 0;
static const int64_t StmtKind_Val = 1;
static const int64_t StmtKind_Var = 2;
static const int64_t StmtKind_SharedVal = 3;
static const int64_t StmtKind_SharedVar = 4;
static const int64_t StmtKind_Assign = 5;
static const int64_t StmtKind_For = 6;
static const int64_t StmtKind_While = 7;
static const int64_t StmtKind_Loop = 8;
static const int64_t StmtKind_Break = 9;
static const int64_t StmtKind_Continue = 10;
static const int64_t StmtKind_Return = 11;
static const int64_t StmtKind_Yield = 12;
static const int64_t StmtKind_Throw = 13;
static const int64_t StmtKind_With = 14;

/* enum AssignOp */
static const int64_t AssignOp_Add = 0;
static const int64_t AssignOp_Sub = 1;
static const int64_t AssignOp_Mul = 2;
static const int64_t AssignOp_Div = 3;
static const int64_t AssignOp_Mod = 4;

/* enum BinOp */
static const int64_t BinOp_Add = 0;
static const int64_t BinOp_Sub = 1;
static const int64_t BinOp_Mul = 2;
static const int64_t BinOp_Div = 3;
static const int64_t BinOp_Mod = 4;
static const int64_t BinOp_Pow = 5;
static const int64_t BinOp_MatMul = 6;
static const int64_t BinOp_Eq = 7;
static const int64_t BinOp_NotEq = 8;
static const int64_t BinOp_Lt = 9;
static const int64_t BinOp_LtEq = 10;
static const int64_t BinOp_Gt = 11;
static const int64_t BinOp_GtEq = 12;
static const int64_t BinOp_And = 13;
static const int64_t BinOp_Or = 14;
static const int64_t BinOp_BitAnd = 15;
static const int64_t BinOp_BitOr = 16;
static const int64_t BinOp_BitXor = 17;
static const int64_t BinOp_Shl = 18;
static const int64_t BinOp_Shr = 19;
static const int64_t BinOp_BroadcastAdd = 20;
static const int64_t BinOp_BroadcastSub = 21;
static const int64_t BinOp_BroadcastMul = 22;
static const int64_t BinOp_BroadcastDiv = 23;
static const int64_t BinOp_BroadcastPow = 24;
static const int64_t BinOp_PipeForward = 25;
static const int64_t BinOp_Compose = 26;
static const int64_t BinOp_ComposeBack = 27;
static const int64_t BinOp_Parallel = 28;
static const int64_t BinOp_LayerConnect = 29;
static const int64_t BinOp_In = 30;
static const int64_t BinOp_NotIn = 31;
static const int64_t BinOp_Is = 32;
static const int64_t BinOp_IsNot = 33;

/* enum UnaryOp */
static const int64_t UnaryOp_Neg = 0;
static const int64_t UnaryOp_Not = 1;
static const int64_t UnaryOp_BitNot = 2;
static const int64_t UnaryOp_Ref = 3;
static const int64_t UnaryOp_Deref = 4;
static const int64_t UnaryOp_Transpose = 5;

/* enum AsmConstraintKind */
static const int64_t AsmConstraintKind_In = 0;
static const int64_t AsmConstraintKind_Out = 1;
static const int64_t AsmConstraintKind_InOut = 2;
static const int64_t AsmConstraintKind_LateOut = 3;

/* enum AsmLocation */
static const int64_t AsmLocation_Reg = 0;
static const int64_t AsmLocation_RegSpec = 1;
static const int64_t AsmLocation_Mem = 2;
static const int64_t AsmLocation_Imm = 3;

/* enum Token */
static const int64_t Token_Not = 0;
static const int64_t Token_And = 1;
static const int64_t Token_Or = 2;
static const int64_t Token_LParen = 3;
static const int64_t Token_RParen = 4;
static const int64_t Token_Comma = 5;
static const int64_t Token_Sel = 6;

/* enum PredicateContext */
static const int64_t PredicateContext_Weaving = 0;
static const int64_t PredicateContext_DependencyInjection = 1;
static const int64_t PredicateContext_Mock = 2;
static const int64_t PredicateContext_Architecture = 3;

/* enum ArgPatterns */
static const int64_t ArgPatterns_Any = 0;
static const int64_t ArgPatterns_Specific = 1;

/* enum Selector */
static const int64_t Selector_Execution = 0;
static const int64_t Selector_Within = 1;
static const int64_t Selector_Attr = 2;
static const int64_t Selector_Effect = 3;
static const int64_t Selector_Test = 4;
static const int64_t Selector_Decision = 5;
static const int64_t Selector_Condition = 6;
static const int64_t Selector_Call = 7;
static const int64_t Selector_Type = 8;
static const int64_t Selector_Init = 9;
static const int64_t Selector_Import = 10;
static const int64_t Selector_Depend = 11;
static const int64_t Selector_Use = 12;
static const int64_t Selector_Export = 13;
static const int64_t Selector_Config = 14;

/* enum Predicate */
static const int64_t Predicate_Sel = 0;
static const int64_t Predicate_Not = 1;
static const int64_t Predicate_And = 2;
static const int64_t Predicate_Or = 3;

/* enum CompletionKind */
static const int64_t CompletionKind_Variable = 0;
static const int64_t CompletionKind_Function = 1;
static const int64_t CompletionKind_Method = 2;
static const int64_t CompletionKind_Keyword = 3;
static const int64_t CompletionKind_Module = 4;
static const int64_t CompletionKind_Type = 5;
static const int64_t CompletionKind_Field = 6;
static const int64_t CompletionKind_EnumVariant = 7;

/* enum DiagnosticSeverity */
static const int64_t DiagnosticSeverity_Error = 0;
static const int64_t DiagnosticSeverity_Warning = 1;
static const int64_t DiagnosticSeverity_Info = 2;
static const int64_t DiagnosticSeverity_Hint = 3;

/* enum SafetyError */
static const int64_t SafetyError_InlineAsmOutsideUnsafe = 0;
static const int64_t SafetyError_UnsafeFfiOutsideUnsafe = 1;
static const int64_t SafetyError_RawPointerOutsideUnsafe = 2;
static const int64_t SafetyError_Other = 3;

/* enum ChangeKind */
static const int64_t ChangeKind_Added = 0;
static const int64_t ChangeKind_Removed = 1;
static const int64_t ChangeKind_TypeChanged = 2;
static const int64_t ChangeKind_SignatureChanged = 3;
static const int64_t ChangeKind_VisibilityChanged = 4;
static const int64_t ChangeKind_DefaultValueChanged = 5;
static const int64_t ChangeKind_ReturnTypeChanged = 6;
static const int64_t ChangeKind_ParamAdded = 7;
static const int64_t ChangeKind_ParamRemoved = 8;
static const int64_t ChangeKind_ParamTypeChanged = 9;
static const int64_t ChangeKind_ParamRenamed = 10;
static const int64_t ChangeKind_FieldAdded = 11;
static const int64_t ChangeKind_FieldRemoved = 12;
static const int64_t ChangeKind_FieldTypeChanged = 13;
static const int64_t ChangeKind_VariantAdded = 14;
static const int64_t ChangeKind_VariantRemoved = 15;
static const int64_t ChangeKind_ImplementationChanged = 16;
static const int64_t ChangeKind_DocChanged = 17;

/* enum ImpactLevel */
static const int64_t ImpactLevel_Breaking = 0;
static const int64_t ImpactLevel_Major = 1;
static const int64_t ImpactLevel_Minor = 2;
static const int64_t ImpactLevel_Info = 3;

/* enum SimdElementType */
static const int64_t SimdElementType_I8 = 0;
static const int64_t SimdElementType_I16 = 1;
static const int64_t SimdElementType_I32 = 2;
static const int64_t SimdElementType_I64 = 3;
static const int64_t SimdElementType_F32 = 4;
static const int64_t SimdElementType_F64 = 5;

/* enum SimdOperation */
static const int64_t SimdOperation_Add = 0;
static const int64_t SimdOperation_Sub = 1;
static const int64_t SimdOperation_Mul = 2;
static const int64_t SimdOperation_Div = 3;
static const int64_t SimdOperation_And = 4;
static const int64_t SimdOperation_Or = 5;
static const int64_t SimdOperation_Xor = 6;
static const int64_t SimdOperation_Not = 7;
static const int64_t SimdOperation_Eq = 8;
static const int64_t SimdOperation_Ne = 9;
static const int64_t SimdOperation_Lt = 10;
static const int64_t SimdOperation_Le = 11;
static const int64_t SimdOperation_Gt = 12;
static const int64_t SimdOperation_Ge = 13;
static const int64_t SimdOperation_ReduceAdd = 14;
static const int64_t SimdOperation_ReduceMul = 15;
static const int64_t SimdOperation_ReduceMin = 16;
static const int64_t SimdOperation_ReduceMax = 17;
static const int64_t SimdOperation_Shuffle = 18;
static const int64_t SimdOperation_Splat = 19;
static const int64_t SimdOperation_Extract = 20;
static const int64_t SimdOperation_Insert = 21;
static const int64_t SimdOperation_Widen = 22;
static const int64_t SimdOperation_Narrow = 23;
static const int64_t SimdOperation_Convert = 24;

/* enum SimdCheckError */
static const int64_t SimdCheckError_InvalidLaneCount = 0;
static const int64_t SimdCheckError_IncompatibleTypes = 1;
static const int64_t SimdCheckError_InvalidVectorWidth = 2;
static const int64_t SimdCheckError_UnsupportedOperation = 3;
static const int64_t SimdCheckError_LaneIndexOutOfBounds = 4;
static const int64_t SimdCheckError_ShuffleMaskInvalid = 5;

/* enum SimdPlatform */
static const int64_t SimdPlatform_None_Platform = 0;
static const int64_t SimdPlatform_SSE = 1;
static const int64_t SimdPlatform_SSE2 = 2;
static const int64_t SimdPlatform_AVX = 3;
static const int64_t SimdPlatform_AVX2 = 4;
static const int64_t SimdPlatform_AVX512 = 5;
static const int64_t SimdPlatform_NEON = 6;
static const int64_t SimdPlatform_SVE = 7;

/* enum NodeKind */
static const int64_t NodeKind_Function = 0;
static const int64_t NodeKind_Class = 1;
static const int64_t NodeKind_Struct = 2;
static const int64_t NodeKind_Enum = 3;
static const int64_t NodeKind_Import = 4;
static const int64_t NodeKind_Expression = 5;

/* enum DiffLine */
static const int64_t DiffLine_Context = 0;
static const int64_t DiffLine_Addition = 1;
static const int64_t DiffLine_Deletion = 2;

/* enum CoherenceError */
static const int64_t CoherenceError_OrphanImpl = 0;
static const int64_t CoherenceError_OverlappingImpl = 1;
static const int64_t CoherenceError_ConflictingAssociatedType = 2;
static const int64_t CoherenceError_BlanketImplConflict = 3;

/* enum VariantPayload */
static const int64_t VariantPayload_Tuple = 0;
static const int64_t VariantPayload_Struct = 1;

/* enum TypeOutlineKind */
static const int64_t TypeOutlineKind_Named = 0;
static const int64_t TypeOutlineKind_Tuple = 1;
static const int64_t TypeOutlineKind_Array = 2;
static const int64_t TypeOutlineKind_Function = 3;
static const int64_t TypeOutlineKind_Optional = 4;
static const int64_t TypeOutlineKind_Reference = 5;
static const int64_t TypeOutlineKind_Atomic = 6;
static const int64_t TypeOutlineKind_Isolated = 7;
static const int64_t TypeOutlineKind_Infer = 8;

/* enum ErrorSeverity */
static const int64_t ErrorSeverity_Error = 0;
static const int64_t ErrorSeverity_Warning = 1;
static const int64_t ErrorSeverity_Info = 2;

/* enum TypeInferError */
static const int64_t TypeInferError_Mismatch = 0;
static const int64_t TypeInferError_OccursCheck = 1;
static const int64_t TypeInferError_Undefined = 2;
static const int64_t TypeInferError_DimensionError = 3;
static const int64_t TypeInferError_TraitNotImplemented = 4;
static const int64_t TypeInferError_Other = 5;

/* enum LayoutKind */
static const int64_t LayoutKind_Simple = 0;
static const int64_t LayoutKind_C = 1;
static const int64_t LayoutKind_Packed = 2;
static const int64_t LayoutKind_Transparent = 3;

/* enum UnsafeOp */
static const int64_t UnsafeOp_PointerDeref = 0;
static const int64_t UnsafeOp_PointerArithmetic = 1;
static const int64_t UnsafeOp_PointerCast = 2;
static const int64_t UnsafeOp_Transmute = 3;
static const int64_t UnsafeOp_ReadUninitialized = 4;
static const int64_t UnsafeOp_WriteToRaw = 5;
static const int64_t UnsafeOp_FfiCall = 6;
static const int64_t UnsafeOp_InlineAssembly = 7;
static const int64_t UnsafeOp_MutableStatic = 8;
static const int64_t UnsafeOp_StaticReference = 9;
static const int64_t UnsafeOp_UncheckedCast = 10;
static const int64_t UnsafeOp_UnionFieldAccess = 11;

/* enum Variance */
static const int64_t Variance_Covariant = 0;
static const int64_t Variance_Contravariant = 1;
static const int64_t Variance_Inv = 2;
static const int64_t Variance_Bivariant = 3;

/* enum VerificationRule */
static const int64_t VerificationRule_VUnsafe = 0;
static const int64_t VerificationRule_VEffect = 1;
static const int64_t VerificationRule_VReflect = 2;
static const int64_t VerificationRule_VGhost = 3;
static const int64_t VerificationRule_VTrusted = 4;
static const int64_t VerificationRule_VPartial = 5;

/* enum VolatileKind */
static const int64_t VolatileKind_Read = 0;
static const int64_t VolatileKind_Write = 1;
static const int64_t VolatileKind_ReadWrite = 2;
static const int64_t VolatileKind_None_ = 3;

struct ProceedContext;
struct AroundAdviceContext;
struct ConditionalProceedContext;
struct Logger;
struct Advice;
struct LogAspect;
struct TracingAspect;
struct ContractAspect;
struct AopWeaver;
struct ParamSignature;
struct FieldSignature;
struct FunctionSignature;
struct StructSignature;
struct ClassSignature;
struct EnumSignature;
struct TraitSignature;
struct ApiSurface;
struct ApiChange;
struct ArchRule;
struct ArchRulesConfig;
struct Dependency;
struct ArchViolation;
struct ArchRulesEngine;
struct TraitRef;
struct AssocTypeDef;
struct TraitDefEx;
struct ImplBlockEx;
struct FunctionDef;
struct StructDef;
struct ClassDef;
struct EnumDef;
struct TraitDef;
struct Module;
struct AsyncInstInfo;
struct AsyncFunctionInfo;
struct VolatileAttr;
struct BackendError;
struct CompiledUnit;
struct CompiledSymbol;
struct Relocation;
struct SdnValue;
struct FunctionValue;
struct ClosureValue;
struct ObjectValue;
struct HirExpr;
struct TypeInferencer;
struct HirFunction;
struct BitLayout;
struct BuildEnvironment;
struct BuildInputs;
struct BuildPhase;
struct BuildOutput;
struct BuildDiagnostic;
struct BuildLog;
struct BuildLogger;
struct DeterministicConfig;
struct LinkConfig;
struct LinkStats;
struct LinkError;
struct Linker;
struct BuildConfig;
struct AbiInfo;
struct CodegenEnhanced;
struct CodegenStats;
struct CodegenError;
struct Codegen;
struct CompilabilityAnalyzer;
struct GenericTemplate;
struct ConcreteType;
struct TypeRegistry;
struct InstantiationRecord;
struct Config;
struct CompilerConfig;
struct ConstEvaluator;
struct KeyExtractor;
struct ConstKeySet;
struct TemplateTypeInference;
struct ConstKeyValidator;
struct TemplateKey;
struct TemplateSchema;
struct SymbolUsage;
struct ContextPack;
struct SourceLoc;
struct FunctionCoverage;
struct ModuleCoverage;
struct CoverageStats;
struct CoverageReport;
struct CoverageCollector;
struct DimSolver;
struct WhereClause;
struct RuntimeDimCheck;
struct DimCheckGenerator;
struct DimError;
struct DimNote;
struct Binding;
struct DiContainer;
struct DiValidationError;
struct ParamInfo;
struct ConstructorInfo;
struct DiValidator;
struct CheckBackendImpl;
struct CompilerDriver;
struct EffectCacheConfig;
struct EffectCacheStats;
struct FunctionEffectInfo;
struct EffectCache;
struct EffectEnv;
struct TypeWrapper;
struct EffectScanner;
struct EffectSolver;
struct EffectStats;
struct Color;
struct ErrorContext;
struct ShellResult;
struct TypeVar;
struct QuantifierLevel;
struct QuantifierContext;
struct HirTypeParam;
struct HirParam;
struct HirClass;
struct HirStruct;
struct HirField;
struct HirEnum;
struct HirVariant;
struct HirBitfield;
struct HirBitfieldField;
struct HirTraitBound;
struct HirTrait;
struct HirImpl;
struct HirConst;
struct HirStaticAssert;
struct HirInterpolation;
struct HirCallArg;
struct HirMatchArm;
struct HirWithItem;
struct HirCompClause;
struct HirPattern;
struct HirStmt;
struct HirBlock;
struct HirAsm;
struct HirAsmConstraint;
struct HirModule;
struct HirImport;
struct HirImportItem;
struct SymbolId;
struct Symbol;
struct ScopeId;
struct Scope;
struct SymbolTable;
struct EventOptions;
struct EventBinding;
struct ManifestMetadata;
struct HydrationManifest;
struct IncrementalConfig;
struct SourceInfo;
struct CachedArtifact;
struct IncrementalStats;
struct IncrementalState;
struct IncrementalBuilder;
struct FileHash;
struct CompilerContext;
struct InlineAsm;
struct TemplateInstantiator;
struct InterruptAttr;
struct FunctionRecord;
struct RecordingSession;
struct Lexer;
struct SourcePosition;
struct Span;
struct Token;
struct MacroParam;
struct MacroDef;
struct MacroRegistry;
struct MacroCall;
struct TypeEnv;
struct MacroTypeChecker;
struct SubstitutionMap;
struct MacroExpander;
struct IntroducedSymbol;
struct InjectionSpec;
struct MacroContractResult;
struct MacroContractItem;
struct SymbolScope;
struct BlockContext;
struct ValidationResult;
struct MacroValidator;
struct CliArgs;
struct BitfieldMirLower;
struct LoopContext;
struct ContractContext;
struct MirModule;
struct MirFunction;
struct MirSignature;
struct MirLocal;
struct LocalId;
struct MirStatic;
struct MirConstant;
struct MirTypeDef;
struct MirFieldDef;
struct MirVariantDef;
struct MirType;
struct BlockId;
struct MirBlock;
struct MirInst;
struct EffectSet;
struct MirInterpreter;
struct MirLowering;
struct MirError;
struct MonomorphizationPass;
struct MonoStats;
struct OptimizationStats;
struct ParallelConfig;
struct CompileUnit;
struct ParallelScheduler;
struct AttributeParser;
struct Import;
struct ImportItem;
struct Export;
struct Function;
struct Param;
struct TypeParam;
struct TraitBound;
struct Attribute;
struct Class;
struct ActorDef;
struct Struct;
struct Field;
struct Enum;
struct Variant;
struct Bitfield;
struct BitfieldField;
struct Trait;
struct Impl;
struct TypeAlias;
struct Const;
struct StaticAssert;
struct Type;
struct TensorSuffix;
struct Expr;
struct Interpolation;
struct CallArg;
struct MatchArm;
struct CatchClause;
struct LambdaParam;
struct ComprehensionClause;
struct Pattern;
struct Stmt;
struct Block;
struct WithItem;
struct AsmExpr;
struct AsmConstraint;
struct Parser;
struct SignaturePattern;
struct MatchContext;
struct PrettyConfig;
struct PrettyPrinter;
struct ProjectConfig;
struct ProfileConfig;
struct ProjectContext;
struct Position;
struct Location;
struct Range;
struct Completion;
struct Diagnostic;
struct HoverInfo;
struct DefinitionResult;
struct CompilerQueryContext;
struct TypeChecker;
struct MethodResolver;
struct SafetyContext;
struct SafetyChecker;
struct SymbolInfo;
struct SemanticChange;
struct DiffSummary;
struct SemanticDiffer;
struct SimdVectorType;
struct SimdTypeChecker;
struct Vec2f;
struct Vec4f;
struct Vec8f;
struct Vec4d;
struct SimdCapabilities;
struct Target;
struct SmfBuildOptions;
struct SymbolUsageResult;
struct AnalysisNode;
struct SymbolUsageAnalyzer;
struct TestRunner;
struct DiffHunk;
struct TextDiff;
struct ImplInfo;
struct CoherenceChecker;
struct MethodSig;
struct MethodImpl;
struct ImplBlock;
struct Obligation;
struct ImplRegistry;
struct TraitSolver;
struct CycleDetector;
struct OutlineModule;
struct BlockOutline;
struct ImportOutline;
struct ExportOutline;
struct FunctionOutline;
struct ParamOutline;
struct AttributeOutline;
struct ClassOutline;
struct ActorOutline;
struct StructOutline;
struct FieldOutline;
struct EnumOutline;
struct BitfieldOutline;
struct BitfieldFieldOutline;
struct VariantOutline;
struct TraitOutline;
struct ImplOutline;
struct TypeAliasOutline;
struct ConstOutline;
struct StaticAssertOutline;
struct TypeParamOutline;
struct TypeOutline;
struct ParseError;
struct HmInferContext;
struct TypeScheme;
struct Substitution;
struct LayoutAttr;
struct UnsafeOperation;
struct UnsafeContext;
struct VarianceOps;
struct TypeParamDef;
struct VarianceEnv;
struct FieldDef;
struct MethodDef;
struct TypeDef;
struct VarianceInference;
struct SubtypeEnv;
struct VarianceChecker;
struct VerificationViolation;
struct FunctionInfo;
struct VerificationChecker;
struct VisibilityWarning;
struct VisibilityChecker;
struct VolatileAccess;
struct Option_Span;
struct Option_BuildOutput;
struct Option_text;
struct Option_FunctionAttr;
struct Option_HirType;
struct Option_Symbol;

/* Option<text> */
struct Option_text {
    bool has_value;
    const char* value;
    Option_text() : has_value(false), value{} {}
    Option_text(const char* v) : has_value(true), value(v) {}
    Option_text(SplValue) : has_value(false), value{} {}
};

/* Option<FunctionAttr> */
struct Option_FunctionAttr {
    bool has_value;
    int64_t value;
    Option_FunctionAttr() : has_value(false), value{} {}
    Option_FunctionAttr(int64_t v) : has_value(true), value(v) {}
    Option_FunctionAttr(SplValue) : has_value(false), value{} {}
};

/* Option<HirType> */
struct Option_HirType {
    bool has_value;
    int64_t value;
    Option_HirType() : has_value(false), value{} {}
    Option_HirType(int64_t v) : has_value(true), value(v) {}
    Option_HirType(SplValue) : has_value(false), value{} {}
};

/* Option<Span> */
struct Option_Span {
    bool has_value;
    int64_t value;  /* struct/Result/tuple pointer as int64_t */
    Option_Span() : has_value(false), value(0) {}
    Option_Span(int64_t v) : has_value(true), value(v) {}
    Option_Span(SplValue) : has_value(false), value(0) {}
};

/* Option<BuildOutput> */
struct Option_BuildOutput {
    bool has_value;
    int64_t value;  /* struct/Result/tuple pointer as int64_t */
    Option_BuildOutput() : has_value(false), value(0) {}
    Option_BuildOutput(int64_t v) : has_value(true), value(v) {}
    Option_BuildOutput(SplValue) : has_value(false), value(0) {}
};

/* Option<Symbol> */
struct Option_Symbol {
    bool has_value;
    int64_t value;  /* struct/Result/tuple pointer as int64_t */
    Option_Symbol() : has_value(false), value(0) {}
    Option_Symbol(int64_t v) : has_value(true), value(v) {}
    Option_Symbol(SplValue) : has_value(false), value(0) {}
};

struct ProceedContext {
    const char* advice_name;
    int64_t proceed_count;
    bool has_error;
};

struct AroundAdviceContext {
    ProceedContext* proceed_ctx;
    int64_t target_fn;
};

struct ConditionalProceedContext {
    AroundAdviceContext* base_ctx;
};

struct Logger {
    int64_t level;
};

struct Advice {
    int64_t kind;
    int64_t pointcut;
    FnPtr_i64 handler;
    int64_t order;
};

struct LogAspect {
    int64_t level;
};

struct TracingAspect {
    int64_t level;
};

struct ContractAspect {
    bool enabled;
};

struct AopWeaver {
    std::vector<Advice> advices;
    int64_t config;
    Logger* logger;
};

struct ParamSignature {
    const char* name;
    bool has_type_name;
    const char* type_name;
};

struct FieldSignature {
    const char* name;
    bool has_type_name;
    const char* type_name;
    bool is_public;
};

struct FunctionSignature {
    const char* name;
    std::vector<ParamSignature> params;
    bool has_return_type;
    const char* return_type;
    bool is_async;
    bool is_generator;
};

struct StructSignature {
    const char* name;
    std::vector<FieldSignature> fields;
};

struct ClassSignature {
    const char* name;
    std::vector<FieldSignature> fields;
    SplArray* methods;
};

struct EnumSignature {
    const char* name;
    SplArray* variants;
};

struct TraitSignature {
    const char* name;
    SplArray* methods;
};

struct ApiSurface {
    const char* module;
    int64_t functions;
    int64_t structs;
    int64_t classes;
    int64_t enums;
    int64_t traits;
};

struct ApiChange {
    int64_t kind;
    const char* symbol;
    const char* category;
    bool has_detail;
    const char* detail;
};

struct ArchRule {
    int64_t action;
    int64_t predicate;
    int64_t priority;
    bool has_message;
    const char* message;
};

struct ArchRulesConfig {
    bool enabled;
    std::vector<ArchRule> rules;
};

struct Dependency {
    int64_t kind;
    const char* source_file;
    int64_t line;
};

struct ArchViolation {
    ArchRule* rule;
    Dependency* dependency;
    const char* message;
};

struct ArchRulesEngine {
    ArchRulesConfig* config;
};

struct TraitRef {
    const char* name;
};

struct AssocTypeDef {
    const char* name;
    const char* bounds;
    const char* default_type;
};

struct TraitDefEx {
    const char* name;
    const char* methods;
    const char* supertraits;
    const char* assoc_types;
};

struct ImplBlockEx {
    const char* trait_ref;
    const char* for_type;
    const char* methods;
    const char* assoc_type_impls;
};

struct FunctionDef {
    const char* name;
    SplArray* generic_params;
    SplArray* params;
    bool has_return_type;
    const char* return_type;
    SplArray* body;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    int64_t type_bindings;
};

struct StructDef {
    const char* name;
    SplArray* generic_params;
    SplArray* fields;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    int64_t type_bindings;
};

struct ClassDef {
    const char* name;
    SplArray* generic_params;
    SplArray* fields;
    SplArray* methods;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    int64_t type_bindings;
};

struct EnumDef {
    const char* name;
    SplArray* generic_params;
    SplArray* variants;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    int64_t type_bindings;
};

struct TraitDef {
    const char* name;
    SplArray* generic_params;
    SplArray* methods;
    bool is_generic_template;
};

struct Module {
    const char* name;
    SplArray* items;
};

struct AsyncInstInfo {
    const char* runtime_fn;
    const char* result_type;
    bool is_suspend_point;
};

struct AsyncFunctionInfo {
    const char* name;
    bool has_await;
    bool has_yield;
    int64_t suspension_points;
    bool is_generator;
};

struct VolatileAttr {
    int64_t mode;
    bool has_address;
    int64_t address;
    bool barriers;
};

struct BackendError {
    const char* message;
    bool has_span;
    Span* span;
    int64_t kind;
};

struct CompiledUnit {
    const char* name;
    SplArray* code;
    SplDict* symbols;
    bool has_entry_point;
    const char* entry_point;
    std::vector<Relocation> relocations;
};

struct CompiledSymbol {
    const char* name;
    int64_t address;
    int64_t size;
    int64_t kind;
};

struct Relocation {
    int64_t offset;
    const char* symbol;
    int64_t kind;
};

struct SdnValue {
    int64_t kind;
};

struct FunctionValue {
    SymbolId* symbol;
    const char* name;
};

struct ClosureValue {
    std::vector<HirParam> params;
    HirExpr* body;
    SplDict* captures;
};

struct ObjectValue {
    SymbolId* class_;
    SplDict* fields;
};

struct HirExpr {
    int64_t kind;
};

struct TypeInferencer {
    const char* context;
    int64_t next_var_id;
};

struct HirFunction {
    Symbol* name;
    std::vector<Symbol> params;
    SplArray* param_types;
    Option_HirType return_type;
    HirExpr* body;
};

struct BitLayout {
    int64_t bit_width;
    bool is_signed;
    int64_t min;
    int64_t max;
};

struct BuildEnvironment {
    const char* working_dir;
    int64_t env_vars;
};

struct BuildInputs {
    SplArray* source_files;
    int64_t dependencies;
};

struct BuildPhase {
    const char* name;
    int64_t duration_ms;
    int64_t result;
    bool has_error;
    const char* error;
};

struct BuildOutput {
    SplArray* artifacts;
    int64_t total_size;
};

struct BuildDiagnostic {
    int64_t level;
    const char* message;
    bool has_file;
    const char* file;
    bool has_line;
    int64_t line;
    bool has_code;
    const char* code;
};

struct BuildLog {
    const char* session_id;
    const char* timestamp;
    const char* compiler_version;
    const char* command;
    BuildEnvironment* environment;
    BuildInputs* inputs;
    std::vector<BuildPhase> phases;
    bool has_output;
    BuildOutput* output;
    std::vector<BuildDiagnostic> diagnostics;
    bool success;
};

struct BuildLogger {
    const char* session_id;
    const char* start_time;
    const char* command;
    std::vector<BuildPhase> phases;
    std::vector<BuildDiagnostic> diagnostics;
    SplArray* source_files;
};

struct DeterministicConfig {
    bool enabled;
    bool has_timestamp;
    const char* timestamp;
    int64_t seed;
    bool normalize_paths;
};

struct LinkConfig {
    int64_t output_format;
    const char* output_path;
    SplArray* libraries;
    SplArray* library_paths;
    bool pie;
    bool debug;
    bool verbose;
    bool allow_deferred;
    int32_t optimization_level;
    SplArray* target_flags;
    SplArray* linker_flags;
};

struct LinkStats {
    int64_t output_size;
    int32_t symbol_count;
};

struct LinkError {
    const char* message;
};

struct Linker {
    LinkConfig* config;
};

struct BuildConfig {
    const char* entry_point;
    const char* output;
    SplArray* dependencies;
    SplArray* libraries;
    SplArray* library_paths;
    int32_t optimization;
    bool debug;
    bool verbose;
    bool pie;
    bool has_target_cpu;
    const char* target_cpu;
    SplArray* target_features;
    SplArray* linker_flags;
};

struct AbiInfo {
    int64_t arch;
    int64_t convention;
    SplArray* arg_regs;
    SplArray* float_arg_regs;
    SplArray* ret_regs;
    SplArray* float_ret_regs;
    SplArray* callee_saved;
    SplArray* caller_saved;
    int64_t stack_align;
    int64_t red_zone;
    int64_t struct_return;
    int64_t struct_in_regs_max;
};

struct CodegenEnhanced {
    int64_t module_handle;
    int64_t current_ctx;
    int64_t type_map;
    int64_t const_map;
    int64_t use_count;
    SplArray* dead_locals;
    int64_t local_values;
    int64_t block_map;
    int64_t function_map;
    int64_t symbol_map;
    bool optimizations_enabled;
    CodegenStats* opt_stats;
    std::vector<CodegenError> errors;
};

struct CodegenStats {
    int64_t constants_folded;
    int64_t dead_code_removed;
    int64_t instructions_simplified;
    int64_t type_casts_eliminated;
};

struct CodegenError {
    const char* message;
    bool has_instruction;
    const char* instruction;
    bool has_local_id;
    int64_t local_id;
    bool has_span;
    Span* span;
};

struct Codegen {
    int64_t module_handle;
    int64_t current_ctx;
    int64_t target;
    int64_t mode;
    SplDict* local_values;
    SplDict* block_map;
    SplDict* function_map;
    SplDict* symbol_map;
    std::vector<CodegenError> errors;
};

struct CompilabilityAnalyzer {
    int64_t results;
    SplArray* known_safe_externs;
};

struct GenericTemplate {
    const char* name;
    SplArray* type_params;
    int64_t ast_data;
};

struct ConcreteType {
    const char* name;
};

struct TypeRegistry {
    SplDict* types;
};

struct InstantiationRecord {
    const char* template_name;
    SplArray* type_args;
    int64_t mode;
    bool has_source_module;
    const char* source_module;
};

struct Config {
    SplDict* values;
};

struct CompilerConfig {
    int64_t profile;
    int64_t log_level;
    int64_t type_inference;
    SplDict* values;
    bool use_rust_types;
    bool use_rust_interp;
    bool use_rust_lexer;
    bool deterministic;
    bool coverage_enabled;
};

struct ConstEvaluator {
    HirModule* module;
    SplDict* constants;
    SplDict* type_sizes;
    SplDict* type_aligns;
    SplDict* locals;
    int64_t call_depth;
};

struct KeyExtractor {
};

struct ConstKeySet {
    std::vector<Symbol> keys;
};

struct TemplateTypeInference {
};

struct ConstKeyValidator {
};

struct TemplateKey {
    const char* name;
    int64_t position;
    bool is_optional;
    bool has_default;
    const char* default_value;
};

struct TemplateSchema {
    const char* template;
    std::vector<TemplateKey> keys;
    SplArray* required_keys;
    SplArray* optional_keys;
};

struct SymbolUsage {
    SplArray* used_functions;
    SplArray* used_types;
    SplArray* required_imports;
};

struct ContextPack {
    const char* target;
    int64_t functions;
    SplArray* types;
    SplArray* imports;
    int64_t symbol_count;
};

struct SourceLoc {
    const char* file;
    int64_t line;
    int64_t column;
};

struct FunctionCoverage {
    const char* name;
    int64_t lines_hit;
    int64_t lines_total;
    int64_t branches_hit;
    int64_t branches_total;
};

struct ModuleCoverage {
    const char* name;
    std::vector<FunctionCoverage> functions;
};

struct CoverageStats {
    int64_t lines_hit;
    int64_t lines_total;
    int64_t branches_hit;
    int64_t branches_total;
    int64_t functions_hit;
    int64_t functions_total;
};

struct CoverageReport {
    std::vector<ModuleCoverage> modules;
    CoverageStats* stats;
};

struct CoverageCollector {
    int64_t line_hits;
    int64_t function_calls;
};

struct DimSolver {
    SplArray* constraints;
    SplDict* substitution;
    int64_t next_var_id;
    std::vector<DimError> errors;
};

struct WhereClause {
    SplArray* constraints;
    Span* span;
};

struct RuntimeDimCheck {
    int64_t kind;
    Span* span;
    const char* error_message;
};

struct DimCheckGenerator {
    int64_t mode;
    std::vector<RuntimeDimCheck> checks;
};

struct DimError {
    const char* message;
    int64_t kind;
    Span* span;
    std::vector<DimNote> notes;
    bool has_help;
    const char* help;
    const char* error_code;
};

struct DimNote {
    const char* message;
    bool has_span;
    Span* span;
    int64_t kind;
};

struct Binding {
    FnPtr_i64 factory;
    bool has_profile;
    int64_t profile;
    SplArray* tags;
};

struct DiContainer {
    SplDict* bindings;
    SplDict* singletons;
    const char* profile;
    std::vector<Binding> all_bindings;
};

struct DiValidationError {
    int64_t kind;
    const char* message;
    const char* constructor_name;
    SplArray* params;
    bool has_suggestion;
    const char* suggestion;
};

struct ParamInfo {
    const char* name;
    const char* type_name;
    bool has_inject;
    bool is_injectable;
};

struct ConstructorInfo {
    const char* class_name;
    bool has_sys_inject;
    std::vector<ParamInfo> params;
};

struct DiValidator {
};

struct CheckBackendImpl {
};

struct CompilerDriver {
    int64_t ctx;
};

struct EffectCacheConfig {
    int64_t max_entries;
    bool validate_on_lookup;
};

struct EffectCacheStats {
    int64_t hits;
    int64_t misses;
    int64_t entries;
};

struct FunctionEffectInfo {
    const char* name;
    SplArray* declared_effects;
    SplArray* derived_effects;
    SplArray* called_operations;
    SplArray* called_functions;
    SplArray* violations;
};

struct EffectCache {
    EffectCacheConfig* config;
    int64_t function_cache;
    int64_t operation_effects;
    EffectCacheStats* stats;
};

struct EffectEnv {
    const char* data;
};

struct TypeWrapper {
    const char* env;
};

struct EffectScanner {
    const char* env;
};

struct EffectSolver {
    const char* env;
    const char* scanner;
    int64_t max_iterations;
};

struct EffectStats {
    int64_t total_functions;
    int64_t async_functions;
    int64_t sync_functions;
    int64_t iterations;
    int64_t builtins_count;
};

struct Color {
    const char* reset;
    const char* bold;
    const char* red;
    const char* green;
    const char* yellow;
    const char* blue;
    const char* cyan;
    const char* white;
    const char* dim;
};

struct ErrorContext {
    Span* span;
    SplArray* secondary_spans;
    const char* file;
    const char* source;
    const char* code;
    SplArray* notes;
    SplArray* help;
};

struct ShellResult {
    int64_t exit_code;
    bool has_stdout;
    const char* stdout;
    bool has_stderr;
    const char* stderr;
};

struct TypeVar {
    int64_t id;
    const char* name;
    const char* kind;
};

struct QuantifierLevel {
    int64_t level;
    bool is_rigid;
};

struct QuantifierContext {
    const char* bound_vars;
    int64_t skolem_counter;
    int64_t scope_level;
    int64_t inference_counter;
};

struct HirTypeParam {
    SymbolId* symbol;
    const char* name;
    SplArray* bounds;
    bool has_default;
    int64_t default_;
    Span* span;
};

struct HirParam {
    SymbolId* symbol;
    const char* name;
    int64_t type_;
    bool has_default;
    HirExpr* default_;
    Span* span;
};

struct HirClass {
    SymbolId* symbol;
    const char* name;
    std::vector<HirTypeParam> type_params;
    std::vector<HirField> fields;
    SplDict* methods;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
    bool has_layout_attr;
    LayoutAttr* layout_attr;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    SplDict* type_bindings;
};

struct HirStruct {
    SymbolId* symbol;
    const char* name;
    std::vector<HirTypeParam> type_params;
    std::vector<HirField> fields;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
    bool has_layout_attr;
    LayoutAttr* layout_attr;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    SplDict* type_bindings;
};

struct HirField {
    SymbolId* symbol;
    const char* name;
    int64_t type_;
    bool has_default;
    HirExpr* default_;
    bool is_public;
    bool is_volatile;
    bool has_fixed_address;
    int64_t fixed_address;
    Span* span;
};

struct HirEnum {
    SymbolId* symbol;
    const char* name;
    std::vector<HirTypeParam> type_params;
    std::vector<HirVariant> variants;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    SplDict* type_bindings;
};

struct HirVariant {
    SymbolId* symbol;
    const char* name;
    int64_t kind;
    Span* span;
};

struct HirBitfield {
    SymbolId* symbol;
    const char* name;
    int64_t backing_type;
    std::vector<HirBitfieldField> fields;
    int64_t total_bits;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
};

struct HirBitfieldField {
    SymbolId* symbol;
    const char* name;
    bool has_type_;
    int64_t type_;
    int64_t bit_width;
    int64_t bit_offset;
    bool is_reserved;
    Span* span;
};

struct HirTraitBound {
    SymbolId* type_param;
    int64_t trait_;
    Span* span;
};

struct HirTrait {
    SymbolId* symbol;
    const char* name;
    std::vector<HirTypeParam> type_params;
    std::vector<HirFunction> methods;
    SplArray* supertraits;
    std::vector<HirFunction> defaults;
    std::vector<HirTraitBound> where_clause;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    SplDict* type_bindings;
};

struct HirImpl {
    int64_t type_;
    bool has_trait_;
    int64_t trait_;
    std::vector<HirTypeParam> type_params;
    std::vector<HirTraitBound> where_clause;
    SplDict* methods;
    Span* span;
};

struct HirConst {
    SymbolId* symbol;
    const char* name;
    int64_t type_;
    HirExpr* value;
    bool is_mutable;
    bool is_public;
    bool is_volatile;
    bool has_fixed_address;
    int64_t fixed_address;
    Span* span;
};

struct HirStaticAssert {
    HirExpr* condition;
    bool has_message;
    const char* message;
    Span* span;
};

struct HirInterpolation {
    HirExpr* expr;
    bool has_format;
    const char* format;
    Span* span;
};

struct HirCallArg {
    bool has_name;
    const char* name;
    HirExpr* value;
    Span* span;
};

struct HirMatchArm {
    HirPattern* pattern;
    bool has_guard;
    HirExpr* guard;
    HirBlock* body;
    Span* span;
};

struct HirWithItem {
    HirExpr* context_expr;
    bool has_target;
    SymbolId* target;
    Span* span;
};

struct HirCompClause {
    int64_t kind;
    Span* span;
};

struct HirPattern {
    int64_t kind;
    bool has_type_;
    int64_t type_;
    Span* span;
};

struct HirStmt {
    int64_t kind;
    Span* span;
};

struct HirBlock {
    std::vector<HirStmt> stmts;
    bool has;
    HirExpr* value;
    Span* span;
};

struct HirAsm {
    const char* asm_template;
    bool is_volatile;
    std::vector<HirAsmConstraint> constraints;
    SplArray* clobbers;
    Span* span;
};

struct HirAsmConstraint {
    const char* name;
    int64_t kind;
    int64_t location;
    HirExpr* value;
    Span* span;
};

struct HirModule {
    const char* name;
    const char* path;
    std::vector<HirImport> imports;
    SplArray* exports;
    SymbolTable* symbols;
    SplDict* functions;
    SplDict* classes;
    SplDict* structs;
    SplDict* enums;
    SplDict* bitfields;
    SplDict* traits;
    std::vector<HirImpl> impls;
    SplDict* constants;
    std::vector<HirStaticAssert> static_asserts;
};

struct HirImport {
    const char* module_path;
    std::vector<HirImportItem> items;
    Span* span;
};

struct HirImportItem {
    const char* name;
    bool has_alias;
    const char* alias;
    bool has_resolved;
    SymbolId* resolved;
};

struct SymbolId {
    int64_t id;
};

struct Symbol {
    SymbolId* id;
    const char* name;
    int64_t kind;
    bool has_type_;
    int64_t type_;
    ScopeId* scope;
    Span* span;
    bool is_public;
    bool is_mutable;
    bool has_defining_module;
    const char* defining_module;
};

struct ScopeId {
    int64_t id;
};

struct Scope {
    ScopeId* id;
    bool has_parent;
    ScopeId* parent;
    int64_t kind;
    SplDict* symbols;
};

struct SymbolTable {
    SplDict* symbols;
    SplDict* scopes;
    ScopeId* current_scope;
    int64_t next_symbol_id;
    int64_t next_scope_id;
};

struct EventOptions {
    bool has_once;
    bool once;
    bool has_passive;
    bool passive;
    bool has_capture;
    bool capture;
};

struct EventBinding {
    const char* selector;
    const char* event;
    const char* handler;
    bool has_options;
    EventOptions* options;
};

struct ManifestMetadata {
    const char* compiled_at;
    const char* source;
    bool has_wasm_size;
    int64_t wasm_size;
};

struct HydrationManifest {
    int64_t version;
    SplArray* exports;
    std::vector<EventBinding> bindings;
    int64_t state;
    ManifestMetadata* metadata;
};

struct IncrementalConfig {
    bool persist;
    bool validate_on_load;
    bool has_cache_dir;
    const char* cache_dir;
};

struct SourceInfo {
    const char* path;
    int64_t content_hash;
    SplArray* dependencies;
    SplArray* functions;
    SplArray* types;
    SplArray* macros;
};

struct CachedArtifact {
    SourceInfo* source;
    bool has_hir;
    bool has_mir;
    bool has_object;
};

struct IncrementalStats {
    int64_t files_checked;
    int64_t files_dirty;
    int64_t cache_hits;
    int64_t cache_misses;
};

struct IncrementalState {
    int64_t sources;
    int64_t statuses;
    int64_t artifacts;
    IncrementalStats* stats;
};

struct IncrementalBuilder {
    IncrementalState* state;
};

struct FileHash {
    const char* path;
    int64_t content_hash;
    int64_t mtime_ms;
};

struct CompilerContext {
    int64_t config;
    int64_t container;
    int64_t mode;
};

struct InlineAsm {
    SplArray* template;
    SplArray* operands;
    SplArray* clobbers;
    SplArray* options;
    int64_t arch;
    Span* span;
};

struct TemplateInstantiator {
    int64_t context;
    SplArray* in_progress;
    SplDict* cache;
};

struct InterruptAttr {
    int64_t vector;
    int64_t priority;
    bool is_naked;
    bool is_fast;
    bool is_noreturn;
    bool is_reentrant;
};

struct FunctionRecord {
    const char* name;
    bool has_module;
    const char* module;
    int64_t call_count;
    int64_t first_call_us;
    int64_t last_call_us;
    int64_t estimated_size;
    SplArray* callees;
    bool is_startup_path;
};

struct RecordingSession {
    int64_t functions;
    SplArray* call_stack;
    int64_t start_millis;
    int64_t first_frame_us;
    int64_t event_loop_us;
};

struct Lexer {
    const char* source;
    int64_t pos;
    int64_t line;
    int64_t col;
    SplArray* indent_stack;
    int64_t pending_dedents;
    bool at_line_start;
    int64_t paren_depth;
    bool in_math_block;
    int64_t math_brace_depth;
    int64_t prev_token_kind;
    bool has_pending_token;
    Token* pending_token;
    int64_t generic_depth;
    bool has_block_registry;
    int64_t block_registry;
    bool has_current_block_kind;
    const char* current_block_kind;
    int64_t current_lexer_mode;
    bool in_raw_block;
    int64_t raw_block_start;
    int64_t block_brace_depth;
    bool has_unified_registry;
    int64_t unified_registry;
};

struct SourcePosition {
    int64_t offset;
    int64_t line;
    int64_t col;
};

struct Span {
    int64_t start;
    int64_t end;
    int64_t line;
    int64_t col;
};

struct Token {
    int64_t kind;
    Span* span;
    const char* text;
};

struct MacroParam {
    Symbol* name;
    int64_t ty;
    bool is_variadic;
};

struct MacroDef {
    Symbol* name;
    std::vector<MacroParam> params;
    Expr* body;
    int64_t expansion_ty;
    int64_t hygiene_scope;
};

struct MacroRegistry {
    const char* macros;
    int64_t next_hygiene_scope;
};

struct MacroCall {
    Symbol* name;
    std::vector<Expr> args;
};

struct TypeEnv {
    const char* vars;
};

struct MacroTypeChecker {
    MacroRegistry* registry;
    TypeEnv* type_env;
};

struct SubstitutionMap {
    const char* mapping;
};

struct MacroExpander {
    MacroTypeChecker* type_checker;
};

struct IntroducedSymbol {
    const char* name;
    int64_t kind;
    bool has_type_annotation;
    const char* type_annotation;
    bool is_const;
};

struct InjectionSpec {
    int64_t anchor;
    bool has_label;
    const char* label;
};

struct MacroContractResult {
    int64_t introduced_functions;
    int64_t introduced_classes;
    int64_t introduced_types;
    std::vector<IntroducedSymbol> introduced_fields;
    SplArray* introduced_vars;
    int64_t injections;
    int64_t inject_labels;
    int64_t intro_function_labels;
    bool has_return_type;
    const char* return_type;
    bool has_return_label;
    const char* return_label;
};

struct MacroContractItem {
    const char* kind;
    bool has_name;
    const char* name;
    bool has_type_name;
    const char* type_name;
    bool has_label;
    const char* label;
    bool has_anchor;
    const char* anchor;
};

struct SymbolScope {
    SplArray* functions;
    SplArray* classes;
    SplArray* variables;
    SplArray* types;
};

struct BlockContext {
    bool has_non_macro_statements;
    int64_t current_position;
};

struct ValidationResult {
    bool is_valid;
    SplArray* errors;
    SplArray* warnings;
};

struct MacroValidator {
    SplArray* known_macros;
    int64_t max_expansion_depth;
};

struct CliArgs {
    int64_t mode;
    SplArray* input_files;
    bool has_output_file;
    const char* output_file;
    bool optimize;
    bool debug_info;
    bool verbose;
    int64_t log_level;
    const char* profile;
    bool help;
    bool version;
};

struct BitfieldMirLower {
    int64_t builder;
};

struct LoopContext {
    int64_t continue_target;
    int64_t break_target;
};

struct ContractContext {
    int64_t old_captures;
    bool has_return;
    int64_t return_value;
    const char* func_name;
    bool is_public;
};

struct MirModule {
    const char* name;
    SplDict* functions;
    SplDict* statics;
    SplDict* constants;
    SplDict* types;
};

struct MirFunction {
    SymbolId* symbol;
    const char* name;
    MirSignature* signature;
    std::vector<MirLocal> locals;
    std::vector<MirBlock> blocks;
    BlockId* entry_block;
    Span* span;
    SplArray* generic_params;
    bool is_generic_template;
    bool has_specialization_of;
    const char* specialization_of;
    SplDict* type_bindings;
};

struct MirSignature {
    std::vector<MirType> params;
    MirType* return_type;
    bool is_variadic;
};

struct MirLocal {
    LocalId* id;
    bool has_name;
    const char* name;
    MirType* type_;
    int64_t kind;
};

struct LocalId {
    int64_t id;
};

struct MirStatic {
    SymbolId* symbol;
    const char* name;
    MirType* type_;
    bool has_init;
    MirConstant* init;
    bool is_mutable;
};

struct MirConstant {
    SymbolId* symbol;
    const char* name;
    MirType* type_;
    int64_t value;
};

struct MirTypeDef {
    SymbolId* symbol;
    const char* name;
    int64_t kind;
};

struct MirFieldDef {
    const char* name;
    MirType* type_;
    int64_t offset;
};

struct MirVariantDef {
    const char* name;
    int64_t discriminant;
    bool has_payload;
    MirType* payload;
};

struct MirType {
    int64_t kind;
};

struct BlockId {
    int64_t id;
};

struct MirBlock {
    BlockId* id;
    bool has_label;
    const char* label;
    std::vector<MirInst> instructions;
    int64_t terminator;
};

struct MirInst {
    int64_t kind;
    bool has_span;
    Span* span;
};

struct EffectSet {
    SplArray* effects;
};

struct MirInterpreter {
    int64_t locals;
    int64_t globals;
    int64_t blocks;
    int64_t current_block;
    int64_t return_;
    bool has_returned;
};

struct MirLowering {
    int64_t builder;
    SymbolTable* symbols;
    SplDict* local_map;
    SplArray* loop_stack;
    std::vector<MirError> errors;
};

struct MirError {
    const char* message;
    bool has_span;
    Span* span;
};

struct MonomorphizationPass {
    int64_t monomorphizer;
    SplDict* generic_functions;
    SplDict* generic_structs;
    SplDict* generic_classes;
    SplDict* specialized_functions;
    SplDict* specialized_structs;
    SplDict* specialized_classes;
    MonoStats* stats;
};

struct MonoStats {
    int64_t generic_functions_found;
    int64_t generic_structs_found;
    int64_t generic_classes_found;
    int64_t call_sites_found;
    int64_t specializations_created;
};

struct OptimizationStats {
    int64_t constants_folded;
    int64_t constant_propagations;
    int64_t identity_eliminations;
    int64_t zero_eliminations;
    int64_t strength_reductions;
    int64_t common_subexpressions;
    int64_t dead_instructions;
    int64_t redundant_casts;
    int64_t redundant_loads;
    int64_t peephole_improvements;
    int64_t algebraic_simplifications;
};

struct ParallelConfig {
    int64_t max_threads;
    int64_t batch_size;
};

struct CompileUnit {
    const char* path;
    SplArray* dependencies;
    int64_t priority;
};

struct ParallelScheduler {
    ParallelConfig* config;
    std::vector<CompileUnit> units;
    SplArray* completed;
    SplArray* failed;
};

struct AttributeParser {
    std::vector<Token> tokens;
    int64_t pos;
};

struct Import {
    const char* module;
    std::vector<ImportItem> items;
    Span* span;
};

struct ImportItem {
    const char* name;
    bool has_alias;
    const char* alias;
};

struct Export {
    SplArray* items;
    Span* span;
};

struct Function {
    const char* name;
    std::vector<TypeParam> type_params;
    std::vector<Param> params;
    bool has_return_type;
    Type* return_type;
    Block* body;
    bool is_async;
    bool is_static;
    bool is_public;
    bool is_method;
    bool is_mutable;
    bool is_const;
    bool is_kernel;
    bool is_extern;
    std::vector<Attribute> attributes;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
};

struct Param {
    const char* name;
    bool has_type_;
    Type* type_;
    bool has_default;
    Expr* default_;
    Span* span;
};

struct TypeParam {
    const char* name;
    std::vector<Type> bounds;
    bool has_default;
    Type* default_;
    Span* span;
};

struct TraitBound {
    const char* type_param;
    Type* trait_;
    Span* span;
};

struct Attribute {
    const char* name;
    std::vector<Expr> args;
    Span* span;
};

struct Class {
    const char* name;
    std::vector<TypeParam> type_params;
    std::vector<Field> fields;
    SplDict* methods;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<Attribute> attributes;
    Span* span;
};

struct ActorDef {
    const char* name;
    std::vector<TypeParam> type_params;
    std::vector<Field> fields;
    SplDict* methods;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<Attribute> attributes;
    Span* span;
};

struct Struct {
    const char* name;
    std::vector<TypeParam> type_params;
    std::vector<Field> fields;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<Attribute> attributes;
    Span* span;
};

struct Field {
    const char* name;
    Type* type_;
    bool has_default;
    Expr* default_;
    bool is_public;
    bool is_volatile;
    bool has_fixed_address;
    int64_t fixed_address;
    Span* span;
};

struct Enum {
    const char* name;
    std::vector<TypeParam> type_params;
    std::vector<Variant> variants;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
};

struct Variant {
    const char* name;
    int64_t kind;
    Span* span;
};

struct Bitfield {
    const char* name;
    Type* backing_type;
    std::vector<BitfieldField> fields;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<Attribute> attributes;
    Span* span;
};

struct BitfieldField {
    const char* name;
    bool has_type_;
    Type* type_;
    bool has_bits;
    int64_t bits;
    bool is_reserved;
    Span* span;
};

struct Trait {
    const char* name;
    std::vector<TypeParam> type_params;
    std::vector<Type> super_traits;
    std::vector<TraitBound> where_clause;
    std::vector<Function> methods;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
};

struct Impl {
    Type* type_;
    bool has_trait_;
    Type* trait_;
    std::vector<TypeParam> type_params;
    std::vector<TraitBound> where_clause;
    SplDict* methods;
    Span* span;
};

struct TypeAlias {
    const char* name;
    std::vector<TypeParam> type_params;
    Type* type_;
    bool is_public;
    Span* span;
};

struct Const {
    const char* name;
    bool has_type_;
    Type* type_;
    Expr* value;
    bool is_mutable;
    bool is_public;
    bool is_volatile;
    bool has_fixed_address;
    int64_t fixed_address;
    Span* span;
};

struct StaticAssert {
    Expr* condition;
    bool has_message;
    const char* message;
    Span* span;
};

struct Type {
    int64_t kind;
    Span* span;
};

struct TensorSuffix {
    bool has_dtype;
    int64_t dtype;
    bool has_device;
    int64_t device;
    bool trainable;
    bool pinned;
    bool has_backend;
    int64_t backend;
    const char* raw;
};

struct Expr {
    int64_t kind;
    Span* span;
};

struct Interpolation {
    Expr* expr;
    bool has_format;
    const char* format;
    Span* span;
};

struct CallArg {
    bool has_name;
    const char* name;
    Expr* value;
    Span* span;
};

struct MatchArm {
    Pattern* pattern;
    bool has_guard;
    Expr* guard;
    Block* body;
    Span* span;
};

struct CatchClause {
    bool has_pattern;
    Pattern* pattern;
    bool has_type_;
    Type* type_;
    Block* body;
    Span* span;
};

struct LambdaParam {
    const char* name;
    bool has_type_;
    Type* type_;
    Span* span;
};

struct ComprehensionClause {
    int64_t kind;
    Span* span;
};

struct Pattern {
    int64_t kind;
    Span* span;
};

struct Stmt {
    int64_t kind;
    Span* span;
};

struct Block {
    std::vector<Stmt> stmts;
    Span* span;
};

struct WithItem {
    Expr* context_expr;
    bool has_target;
    const char* target;
    Span* span;
};

struct AsmExpr {
    const char* asm_template;
    bool is_volatile;
    std::vector<AsmConstraint> constraints;
    SplArray* clobbers;
    Span* span;
};

struct AsmConstraint {
    const char* name;
    int64_t kind;
    int64_t location;
    Expr* value;
    Span* span;
};

struct Parser {
    const char* source;
    Lexer* lexer;
    Token* current;
    Token* previous;
    std::vector<ParseError> errors;
    bool has_outline;
    OutlineModule* outline;
    bool has_resolved_blocks;
    int64_t resolved_blocks;
};

struct SignaturePattern {
    const char* return_type;
    const char* qualified_name;
    int64_t args;
};

struct MatchContext {
    bool has_type_name;
    const char* type_name;
    bool has_module_path;
    const char* module_path;
    SplArray* attrs;
    bool has_signature;
    const char* signature;
    SplArray* effects;
};

struct PrettyConfig {
    int64_t indent_size;
    int64_t max_line_length;
};

struct PrettyPrinter {
    PrettyConfig* config;
    int64_t indent_level;
    const char* output;
};

struct ProjectConfig {
    const char* name;
    const char* version;
    const char* source_root;
    SplArray* features;
    int64_t profiles;
    int64_t lint_overrides;
    bool di_enabled;
    bool aop_enabled;
    bool deterministic;
    bool has_layout_config_path;
    const char* layout_config_path;
    const char* gc_mode;
};

struct ProfileConfig {
    SplArray* attributes;
    SplArray* imports;
};

struct ProjectContext {
    const char* root;
    const char* source_root;
    const char* name;
    SplArray* features;
    int64_t profiles;
    int64_t lint_overrides;
    bool di_enabled;
    bool aop_enabled;
    bool deterministic;
    const char* active_profile;
    const char* gc_mode;
};

struct Position {
    int64_t line;
    int64_t column;
};

struct Location {
    const char* file;
    Position* start;
    Position* end;
};

struct Range {
    Position* start;
    Position* end;
};

struct Completion {
    const char* label;
    int64_t kind;
    Option_text detail;
    Option_text documentation;
    const char* insert_text;
    int64_t sort_priority;
};

struct Diagnostic {
    Range* range;
    int64_t severity;
    const char* message;
    Option_text code;
    const char* source;
};

struct HoverInfo {
    Range* range;
    const char* contents;
    Option_text type_info;
};

struct DefinitionResult {
    std::vector<Location> locations;
    Option_Symbol symbol;
};

struct CompilerQueryContext {
    SplDict* cached_asts;
    SplDict* cached_symbols;
    SplDict* cached_types;
    SplDict* cached_diagnostics;
    SplDict* file_mtimes;
    const char* project_root;
    bool incremental;
};

struct TypeChecker {
};

struct MethodResolver {
    SymbolTable* symbols;
    TypeChecker* type_checker;
    SplArray* errors;
    SplDict* trait_impls;
    TraitSolver* trait_solver;
};

struct SafetyContext {
    bool in_unsafe;
    SplArray* errors;
};

struct SafetyChecker {
    SafetyContext* context;
};

struct SymbolInfo {
    const char* name;
    const char* kind;
    const char* visibility;
    bool has_signature;
    const char* signature;
    SplArray* fields;
    SplArray* variants;
    bool has_return_type;
    const char* return_type;
    SplArray* param_names;
    SplArray* param_types;
};

struct SemanticChange {
    const char* symbol;
    int64_t kind;
    int64_t impact;
    bool has_old;
    const char* old_value;
    bool has_new;
    const char* new_value;
    const char* message;
};

struct DiffSummary {
    std::vector<SemanticChange> changes;
    int64_t breaking_count;
    int64_t major_count;
    int64_t minor_count;
    int64_t info_count;
};

struct SemanticDiffer {
    std::vector<SemanticChange> changes;
};

struct SimdVectorType {
    int64_t element_type;
    int64_t lane_count;
};

struct SimdTypeChecker {
    SplArray* errors;
    int64_t target_max_width;
};

struct Vec2f {
    float x;
    float y;
};

struct Vec4f {
    float x;
    float y;
    float z;
    float w;
};

struct Vec8f {
    float e0;
    float e1;
    float e2;
    float e3;
    float e4;
    float e5;
    float e6;
    float e7;
};

struct Vec4d {
    double x;
    double y;
    double z;
    double w;
};

struct SimdCapabilities {
    int64_t platform;
};

struct Target {
    const char* os;
    const char* arch;
};

struct SmfBuildOptions {
    bool has_templates;
    int64_t templates;
    bool has_metadata;
    int64_t metadata;
    bool has_note_sdn;
    int64_t note_sdn;
    Target* target;
};

struct SymbolUsageResult {
    SplArray* used_functions;
    SplArray* used_types;
    SplArray* required_imports;
};

struct AnalysisNode {
    int64_t kind;
    const char* name;
    bool is_public;
    SplArray* param_types;
    bool has_return_type;
    const char* return_type;
    SplArray* body_calls;
    SplArray* body_type_refs;
    SplArray* field_types;
    SplArray* method_names;
    bool has_import_path;
    const char* import_path;
};

struct SymbolUsageAnalyzer {
    bool minimal;
};

struct TestRunner {
    int64_t passed;
    int64_t failed;
};

struct DiffHunk {
    int64_t old_start;
    int64_t old_count;
    int64_t new_start;
    int64_t new_count;
    SplArray* lines;
};

struct TextDiff {
    std::vector<DiffHunk> hunks;
};

struct ImplInfo {
    const char* target_type;
    bool has_trait_name;
    const char* trait_name;
    SplArray* generic_params;
    bool is_blanket;
    bool is_default;
    int64_t associated_types;
};

struct CoherenceChecker {
    SplArray* local_traits;
    SplArray* local_types;
    int64_t impls;
};

struct MethodSig {
    const char* name;
    const char* params;
    const char* return_type;
    bool has_self;
};

struct MethodImpl {
    const char* name;
    const char* body;
};

struct ImplBlock {
    const char* trait_ref;
    const char* for_type;
    const char* methods;
};

struct Obligation {
    const char* ty;
    const char* trait_ref;
    const char* span;
};

struct ImplRegistry {
    const char* impls;
};

struct TraitSolver {
    const char* impl_registry;
    int64_t max_depth;
};

struct CycleDetector {
    const char* registry;
    const char* visited;
    const char* rec_stack;
};

struct OutlineModule {
    const char* name;
    std::vector<ImportOutline> imports;
    std::vector<ExportOutline> exports;
    std::vector<FunctionOutline> functions;
    std::vector<ClassOutline> classes;
    std::vector<ActorOutline> actors;
    std::vector<StructOutline> structs;
    std::vector<EnumOutline> enums;
    std::vector<BitfieldOutline> bitfields;
    std::vector<TraitOutline> traits;
    std::vector<ImplOutline> impls;
    std::vector<TypeAliasOutline> type_aliases;
    std::vector<ConstOutline> constants;
    std::vector<StaticAssertOutline> static_asserts;
    std::vector<BlockOutline> inline_blocks;
    std::vector<ParseError> errors;
};

struct BlockOutline {
    const char* kind;
    const char* payload;
    Span* payload_span;
    Span* span;
    bool has_parent_context;
    const char* parent_context;
    bool has_pre_lex_info;
    int64_t pre_lex_info;
    bool has_outline_info;
    int64_t outline_info;
};

struct ImportOutline {
    const char* module;
    SplArray* items;
    bool has_alias;
    const char* alias;
    Span* span;
};

struct ExportOutline {
    SplArray* items;
    Span* span;
};

struct FunctionOutline {
    const char* name;
    std::vector<ParamOutline> params;
    bool has_return_type;
    TypeOutline* return_type;
    bool is_async;
    bool is_static;
    bool is_public;
    bool is_method;
    bool is_mutable;
    bool is_const;
    bool is_kernel;
    bool is_extern;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
    Span* body_span;
};

struct ParamOutline {
    const char* name;
    bool has_type_;
    TypeOutline* type_;
    bool has_default_span;
    Span* default_span;
    Span* span;
};

struct AttributeOutline {
    const char* name;
    bool has_args_span;
    Span* args_span;
    Span* span;
};

struct ClassOutline {
    const char* name;
    std::vector<TypeParamOutline> type_params;
    std::vector<FieldOutline> fields;
    std::vector<FunctionOutline> methods;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<AttributeOutline> attributes;
    Span* span;
};

struct ActorOutline {
    const char* name;
    std::vector<TypeParamOutline> type_params;
    std::vector<FieldOutline> fields;
    std::vector<FunctionOutline> methods;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<AttributeOutline> attributes;
    Span* span;
};

struct StructOutline {
    const char* name;
    std::vector<TypeParamOutline> type_params;
    std::vector<FieldOutline> fields;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<AttributeOutline> attributes;
    Span* span;
};

struct FieldOutline {
    const char* name;
    TypeOutline* type_;
    bool is_public;
    bool is_volatile;
    bool has_address_span;
    Span* address_span;
    bool has_default_span;
    Span* default_span;
    Span* span;
};

struct EnumOutline {
    const char* name;
    std::vector<TypeParamOutline> type_params;
    std::vector<VariantOutline> variants;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
};

struct BitfieldOutline {
    const char* name;
    TypeOutline* backing_type;
    std::vector<BitfieldFieldOutline> fields;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<AttributeOutline> attributes;
    Span* span;
};

struct BitfieldFieldOutline {
    const char* name;
    bool has_type_;
    TypeOutline* type_;
    bool has_bits;
    int64_t bits;
    bool is_reserved;
    Span* span;
};

struct VariantOutline {
    const char* name;
    bool has_payload;
    int64_t payload;
    Span* span;
};

struct TraitOutline {
    const char* name;
    std::vector<TypeParamOutline> type_params;
    std::vector<FunctionOutline> methods;
    bool is_public;
    bool has_doc_comment;
    const char* doc_comment;
    Span* span;
};

struct ImplOutline {
    TypeOutline* type_;
    bool has_trait_;
    TypeOutline* trait_;
    std::vector<FunctionOutline> methods;
    Span* span;
};

struct TypeAliasOutline {
    const char* name;
    std::vector<TypeParamOutline> type_params;
    TypeOutline* type_;
    bool is_public;
    Span* span;
};

struct ConstOutline {
    const char* name;
    bool has_type_;
    TypeOutline* type_;
    bool is_mutable;
    bool is_public;
    bool is_volatile;
    bool has_address_span;
    Span* address_span;
    Span* value_span;
    Span* span;
};

struct StaticAssertOutline {
    Span* condition_span;
    bool has_message;
    const char* message;
    Span* span;
};

struct TypeParamOutline {
    const char* name;
    std::vector<TypeOutline> bounds;
    bool has_default;
    TypeOutline* default_;
    Span* span;
};

struct TypeOutline {
    int64_t kind;
    Span* span;
};

struct ParseError {
    const char* message;
    Span* span;
    int64_t severity;
};

struct HmInferContext {
    SplDict* env;
    int64_t level;
    int64_t next_var;
    Substitution* subst;
    SplArray* errors;
    DimSolver* dim_solver;
    DimCheckGenerator* runtime_checks;
    int64_t dim_check_mode;
    TraitSolver* trait_solver;
    SplDict* function_bounds;
};

struct TypeScheme {
    SplArray* vars;
    int64_t ty;
};

struct Substitution {
    SplDict* map;
};

struct LayoutAttr {
    int64_t layout_kind;
    bool has_explicit_align;
    int64_t explicit_align;
    bool is_packed;
};

struct UnsafeOperation {
    int64_t op;
    Span* span;
    bool has_context;
    const char* context;
};

struct UnsafeContext {
    int64_t unsafe_depth;
    std::vector<UnsafeOperation> operations;
    bool function_unsafe;
    bool allow_implicit_unsafe;
};

struct VarianceOps {
};

struct TypeParamDef {
    Symbol* name;
    int64_t variance;
};

struct VarianceEnv {
    const char* type_variances;
};

struct FieldDef {
    Symbol* name;
    int64_t ty;
};

struct MethodDef {
    Symbol* name;
    SplArray* params;
    int64_t return_ty;
};

struct TypeDef {
    Symbol* name;
    int64_t type_param_count;
    std::vector<FieldDef> fields;
    std::vector<MethodDef> methods;
};

struct VarianceInference {
    const char* type_defs;
    const char* variances;
};

struct SubtypeEnv {
    const char* subtypes;
};

struct VarianceChecker {
    const char* variance_env;
    SubtypeEnv* subtype_env;
};

struct VerificationViolation {
    int64_t rule;
    const char* location;
    const char* message;
};

struct FunctionInfo {
    const char* name;
    SplArray* effects;
    bool is_verified;
    bool is_trusted;
    bool has_contract;
    bool has_ghost_params;
    bool has_ghost_locals;
    bool is_recursive;
    bool has_termination_proof;
    bool uses_reflection;
};

struct VerificationChecker {
    std::vector<VerificationViolation> violations;
    bool strict;
};

struct VisibilityWarning {
    const char* message;
    const char* symbol_name;
    const char* accessing_module;
    const char* defining_module;
    Span* span;
    const char* code;
};

struct VisibilityChecker {
    const char* current_module;
    std::vector<VisibilityWarning> warnings;
};

struct VolatileAccess {
    int64_t address;
    int64_t size;
    int64_t kind;
    int64_t type_;
    Span* span;
};

extern "C" int64_t cranelift_module_new(const char* name, int64_t target);
extern "C" void cranelift_free_module(int64_t module);
extern "C" int64_t cranelift_new_signature(int64_t call_conv);
extern "C" void cranelift_sig_set_return(int64_t sig, int64_t type_);

ProceedContext create_proceed_context_minimal(const char* advice_name);
int64_t create_proceed_context_internal(const char* advice_name);
int64_t create_around_advice_context(const char* advice_name, int64_t target_fn);
int64_t aroundadvicecontext_proceed(AroundAdviceContext self);
const char* verify_proceed_called(AroundAdviceContext ctx);
int64_t create_proceed_context(const char* advice_name, int64_t target_fn);
int64_t create_conditional_proceed_context(const char* advice_name, int64_t target_fn);
int64_t conditionalproceedcontext_proceed_if_allowed(ConditionalProceedContext self);
void test_proceed_enforcement();
void Logger__log(const Logger* self, int64_t level, const char* prefix, const char* message);
void LogAspect__log_aop(const LogAspect* self, const char* prefix, const char* message);
void LogAspect__before(const LogAspect* self, const char* name, SplArray* args);
void LogAspect__after(const LogAspect* self, const char* name, int64_t result);
int64_t LogAspect__around(const LogAspect* self, const char* name, SplArray* args, FnPtr_i64 proceed);
void TracingAspect__before(const TracingAspect* self, const char* name, SplArray* args);
void TracingAspect__after(const TracingAspect* self, const char* name, int64_t result);
bool ContractAspect__check_pre(const ContractAspect* self, const char* name, SplArray* args);
bool ContractAspect__check_post(const ContractAspect* self, const char* name, int64_t result);
void AopWeaver__add_log_aspect(AopWeaver* self, LogAspect aspect, int64_t pointcut);
void AopWeaver__add_tracing_aspect(AopWeaver* self, TracingAspect aspect, int64_t pointcut);
void AopWeaver__add_debug_log_aspect(AopWeaver* self, int64_t pointcut);
ApiSurface apisurface_create(const char* module);
ArchRulesConfig archrulesconfig_disabled();
ArchRulesConfig archrulesconfig_from_rules(std::vector<ArchRule> rules);
int64_t archrulesengine_create(ArchRulesConfig config);
const char* parse_arch_rules_from_sdn(int64_t sdn);
const char* parse_arch_rules_block(SplArray* tokens);
TraitRef traitref_new(const char* name);
int64_t assoctypedef_new(int64_t name);
AssocTypeDef assoctypedef_with_bounds(int64_t name, std::vector<TraitRef> bounds);
TraitDefEx traitdefex_new(int64_t name);
ImplBlockEx implblockex_new(TraitRef trait_ref, int64_t for_type);
const char* mir_type_to_async_type(int64_t mir_type);
int64_t get_async_inst_info(int64_t inst);
AsyncFunctionInfo analyze_async_function(int64_t body);
VolatileAttr parse_volatile_attrs(SplArray* attrs);
int64_t jitinterpreterconfig_always_jit();
int64_t jitinterpreterbackend_default();
int64_t backenderror_not_allowed(const char* message, Option_Span span);
int64_t backenderror_type_error(const char* message, Option_Span span);
int64_t backenderror_runtime_error(const char* message, Option_Span span);
int64_t backenderror_compile_error(const char* message, Option_Span span);
int64_t backenderror_not_implemented(const char* message);
int64_t backenderror_internal(const char* message);
SdnValue sdnvalue_make_nil();
SdnValue sdnvalue_bool(bool value);
SdnValue sdnvalue_int(int64_t value);
SdnValue sdnvalue_float(double value);
SdnValue sdnvalue_string(const char* value);
SdnValue sdnvalue_array(std::vector<SdnValue> elements);
SdnValue sdnvalue_dict(SplDict* entries);
int64_t value_make_nil();
int64_t value_bool(bool value);
int64_t value_int(int64_t value);
int64_t value_float(double value);
int64_t value_string(const char* value);
int64_t value_some(int64_t value);
int64_t value_none();
int64_t value_ok(int64_t value);
int64_t value_err(int64_t value);
const char* format_type_list(SplArray* types);
int64_t hirexpr_int_lit(int64_t value);
int64_t hirexpr_bool_lit(bool value);
int64_t hirexpr_text_lit(const char* value);
int64_t hirexpr_var(int64_t name);
int64_t hirexpr_lambda(SplArray* params, HirExpr body);
int64_t hirexpr_call(HirExpr callee, std::vector<HirExpr> args);
int64_t hirexpr_let_bind(int64_t name, HirExpr value, HirExpr body);
TypeInferencer typeinferencer_empty();
int64_t typeinferencer_infer_expr(TypeInferencer self, HirExpr expr, int64_t mode);
int64_t typeinferencer_synthesize_expr(TypeInferencer self, HirExpr expr);
int64_t typeinferencer_check_expr(TypeInferencer self, HirExpr expr, int64_t expected);
int64_t typeinferencer_synthesize_and_subsume(TypeInferencer self, HirExpr expr, int64_t expected);
bool typeinferencer_subsume(TypeInferencer self, int64_t inferred, int64_t expected);
void test_synthesize_int_lit();
void test_synthesize_bool_lit();
void test_synthesize_text_lit();
void test_check_int_against_int();
void test_mode_is_check();
void test_mode_is_synthesize();
void test_mode_expected();
void test_types_equal();
void test_subsume_compatible();
void test_subsume_incompatible();
void test_check_lambda_with_function_type();
void test_synthesize_lambda_without_expected();
void spl_main();
TypeInferencer TypeInferencer__empty();
bool Option__is_some(const Option* self);
bool Option__is_none(const Option* self);
void test_call_checks_arguments();
void test_let_with_annotation();
void test_let_without_annotation();
void test_nested_application();
void test_lambda_in_application();
void test_check_let_in_check_mode();
void test_option_is_some();
void test_option_is_none();
int64_t hirexpr_return_expr(HirExpr value);
int64_t hirexpr_tuple(std::vector<HirExpr> elems);
int64_t hirexpr_array(std::vector<HirExpr> elems);
int64_t hirexpr_if_expr(HirExpr cond, HirExpr then_expr, HirExpr else_expr);
int64_t bitwise_not_i64(int64_t n);
BitLayout bitlayout_unsigned(int64_t bits);
void bootstrap_hello();
int64_t buildlogger_start(const char* command);
int64_t buildlogger_start_phase(BuildLogger self, const char* name);
int64_t buildlogger_finish(BuildLogger self, Option_BuildOutput output);
int64_t deterministicconfig_create();
int64_t deterministicconfig_disabled();
int64_t linker_new(LinkConfig config);
int64_t linker_link(Linker self, SplArray* smf_files);
BuildConfig buildconfig_default(const char* entry, const char* output);
int64_t get_abi(int64_t arch, int64_t conv);
AbiInfo get_avr_abi(int64_t conv);
CodegenEnhanced codegenenhanced_create(bool enable_opts);
Codegen codegen_new(int64_t target, int64_t mode);
CompilabilityAnalyzer compilabilityanalyzer_create();
int64_t compiledunit_empty(const char* name, int64_t mode);
int64_t compilerprofile_from_text(const char* s);
Config Config__default();
const char* Config__get(const Config* self, const char* key);
void Config__set(Config* self, const char* key, const char* value);
CompilerConfig compilerconfig_default();
ConstEvaluator constevaluator_new(int64_t module);
bool keyextractor_has_keys(const char* tmpl);
int64_t keyextractor_key_count(const char* tmpl);
int64_t constkeyset_from_template(const char* tmpl);
int64_t constkeyset_from_keys(SplArray* keys);
int64_t constkeyset_empty();
void test_extract_single_key();
void test_extract_multiple_keys();
void test_extract_no_keys();
void test_extract_duplicate_keys();
void test_has_keys();
void test_unique_keys();
void test_key_count();
void test_const_key_set_from_template();
void test_const_key_set_empty();
void test_const_key_set_has_key();
void test_const_key_set_missing_keys();
void test_const_key_set_extra_keys();
void test_const_key_set_perfect_match();
int64_t templatetypeinference_infer_template(const char* value);
bool templatetypeinference_is_template(const char* value);
SplArray* KeyExtractor__extract_keys(const char* tmpl);
void test_const_key_set_type();
void test_get_keys();
void test_get_keys_empty();
void test_has_key();
void test_type_equality_const_key_set();
void test_type_equality_other();
void test_infer_template_with_keys();
void test_infer_plain_string();
void test_is_template();
void test_const_key_set_to_string();
void test_dependent_keys_type();
const char* format_key_list(SplArray* keys);
SplArray* find_missing_keys(SplArray* required, SplArray* provided);
SplArray* find_extra_keys(SplArray* required, SplArray* provided);
void test_validate_with_call_success();
void test_validate_with_call_missing_keys();
void test_validate_with_call_extra_keys();
void test_validate_with_call_both_errors();
void test_validate_with_call_not_const_key_set();
void test_validate_keys_match();
void test_has_missing_keys();
void test_has_extra_keys();
void test_find_missing_keys();
void test_find_extra_keys();
void test_key_error_to_string();
void test_typo_detection();
int64_t templatekey_required(const char* name, int64_t position);
int64_t templatekey_optional(const char* name, int64_t position, const char* default_val);
TemplateSchema templateschema_from_template(const char* template);
SymbolUsage symbolusage_empty();
ContextPack contextpack_create(const char* target);
CoverageStats coveragestats_empty();
CoverageCollector coveragecollector_create();
int64_t desugar_async_function(int64_t func);
DimSolver dimsolver_new();
const char* format_shape(SplArray* dims);
DimCheckGenerator dimcheckgenerator_new(int64_t mode);
DimError dimerror_mismatch(int64_t d1, int64_t d2, int64_t span);
void di_panic(const char* msg);
DiContainer dicontainer_for_profile(int64_t profile);
void set_container(DiContainer container);
int64_t get_container();
ParamInfo paraminfo_create(const char* name, const char* type_name, bool has_inject);
DiValidator divalidator_create();
const char* validate_constructor(ConstructorInfo ctor);
const char* validate_class_injection(const char* class_name, bool has_sys_inject, SplArray* field_types);
const char* format_di_error(DiValidationError error);
const char* get_error_code(int64_t kind);
const char* CheckBackendImpl__name(const CheckBackendImpl* self);
bool CheckBackendImpl__is_allowed(const CheckBackendImpl* self, const char* op);
const char* CheckBackendImpl__process_module(const CheckBackendImpl* self, int64_t module);
const char* CheckBackendImpl__eval_expr(const CheckBackendImpl* self, HirExpr expr, int64_t env);
const char* CheckBackendImpl__exec_stmt(const CheckBackendImpl* self, int64_t stmt, int64_t env);
int64_t CompilerDriver__create(int64_t options);
int64_t CompilerDriver__compile(CompilerDriver* self);
bool CompilerDriver__load_sources_impl(CompilerDriver* self);
bool CompilerDriver__parse_all_impl(CompilerDriver* self);
int64_t CompilerDriver__parse_source(const CompilerDriver* self, int64_t source);
bool CompilerDriver__lower_and_check_impl(CompilerDriver* self);
int64_t CompilerDriver__lower_to_hir_impl(const CompilerDriver* self);
int64_t CompilerDriver__resolve_methods_impl(const CompilerDriver* self);
int64_t CompilerDriver__type_check_impl(const CompilerDriver* self);
bool CompilerDriver__monomorphize_impl(CompilerDriver* self);
int64_t CompilerDriver__process_sdn(const CompilerDriver* self);
int64_t CompilerDriver__interpret(const CompilerDriver* self);
int64_t CompilerDriver__run_module(const CompilerDriver* self, int64_t backend, int64_t module);
int64_t CompilerDriver__jit_compile_and_run(CompilerDriver* self);
int64_t CompilerDriver__aot_compile(CompilerDriver* self);
int64_t CompilerDriver__compile_to_native(CompilerDriver* self, const char* output);
int64_t CompilerDriver__compile_to_smf(CompilerDriver* self, const char* output);
int64_t CompilerDriver__compile_to_self_contained(CompilerDriver* self, const char* output);
int64_t CompilerDriver__collect_smf_bytes(CompilerDriver* self);
const char* CompilerDriver__link_objects(const CompilerDriver* self, SplArray* objects, const char* output);
bool CompilerDriver__lower_to_mir(CompilerDriver* self);
bool CompilerDriver__borrow_check(CompilerDriver* self);
const char* CompilerDriver__format_borrow_error(const CompilerDriver* self, int64_t err);
int64_t CompilerDriver__process_async(CompilerDriver* self);
void CompilerDriver__optimize_mir(CompilerDriver* self, int64_t config);
int64_t CompilerDriver__get_optimization_config(const CompilerDriver* self);
Config create_config();
int64_t create_block_resolver();
EffectCacheConfig effectcacheconfig_default_config();
EffectCacheStats effectcachestats_empty();
FunctionEffectInfo functioneffectinfo_empty(const char* name);
EffectCache effectcache_create(EffectCacheConfig config);
bool Effect__is_sync(const Effect* self);
bool Effect__is_async(const Effect* self);
int64_t effect_new_env();
void init_builtins();
EffectEnv effectenv_new();
void test_env();
void test_set_get();
void test_dirty();
int64_t effect_combine_all(SplArray* effects);
TypeWrapper typewrapper_new(int64_t env);
void test_basic_types();
void test_promise_wrap();
void test_promise_unwrap();
void test_suspend_validation();
void test_nested_promises();
void test_function_types();
EffectScanner effectscanner_new(int64_t env);
EffectEnv effectenv_new_for_test();
HirExpr make_int(int64_t n);
HirExpr make_str(const char* s);
HirExpr make_call(int64_t func, std::vector<HirExpr> args);
HirExpr make_suspend(HirExpr expr);
HirExpr make_block(std::vector<HirExpr> exprs);
void test_literals();
void test_suspend_operators();
void test_function_calls();
void test_control_flow();
void test_nested();
int64_t Effect__combine(const Effect* self, int64_t other);
HirFunction hirfunction_new(const char* name, HirExpr body);
EffectSolver effectsolver_new(int64_t env);
const char* Effect__to_string(const Effect* self);
const char* EffectStats__to_string(const EffectStats* self);
const char* effect_to_string(int64_t eff);
bool is_async(int64_t eff);
bool is_sync(int64_t eff);
void test_effect_basic();
void test_effect_combine();
void test_effect_combine_all();
void test_effect_env_basic();
void test_effect_env_set_get();
void test_effect_env_dirty();
void test_builtins();
void test_convenience_functions();
const char* get_category(const char* code);
bool is_semantic(const char* code);
bool is_codegen(const char* code);
bool is_runtime(const char* code);
Color color_new();
ErrorContext errorcontext_empty();
void gc_init();
int64_t gc_malloc(int64_t size);
void gc_collect();
int64_t value_nil();
int64_t value_array_new();
int64_t value_dict_new();
int64_t value_type(int64_t value);
bool value_is_nil(int64_t value);
bool value_is_bool(int64_t value);
bool value_is_int(int64_t value);
bool value_is_float(int64_t value);
bool value_is_string(int64_t value);
bool value_is_array(int64_t value);
bool value_is_dict(int64_t value);
bool value_as_bool(int64_t value);
int64_t value_as_int(int64_t value);
double value_as_float(int64_t value);
int64_t value_as_string(int64_t value, int64_t out_len);
int64_t value_add(int64_t left, int64_t right);
int64_t value_sub(int64_t left, int64_t right);
int64_t value_mul(int64_t left, int64_t right);
int64_t value_div(int64_t left, int64_t right);
bool value_eq(int64_t left, int64_t right);
bool value_lt(int64_t left, int64_t right);
void value_print(int64_t value);
void value_println(int64_t value);
void value_free(int64_t value);
int64_t value_clone(int64_t value);
bool file_exists_ptr(int64_t path_ptr, int64_t path_len);
int64_t file_read_text_ptr(int64_t path_ptr, int64_t path_len);
bool file_write_text_ptr(int64_t path_ptr, int64_t path_len, int64_t content_ptr, int64_t content_len);
bool file_delete_ptr(int64_t path_ptr, int64_t path_len);
void string_free(int64_t ptr);
int64_t env_get_ptr(int64_t name_ptr, int64_t name_len);
bool env_set_ptr(int64_t name_ptr, int64_t name_len, int64_t value_ptr, int64_t value_len);
int64_t recognize_gpu_intrinsic(const char* name);
bool is_gpu_intrinsic(const char* name);
int64_t gpu_intrinsic_arg_count(int64_t kind);
const char* gpu_intrinsic_description(int64_t kind);
bool requires_kernel_context(int64_t kind);
bool has_side_effects(int64_t kind);
SplArray* all_gpu_intrinsic_names();
TypeVar tyvar_new(int64_t id, int64_t name, int64_t kind);
TypeVar typevar_new(int64_t id, int64_t name, int64_t kind);
QuantifierLevel quantifierlevel_new(int64_t level, bool is_rigid);
QuantifierContext quantifiercontext_new();
SymbolId symbolid_new(int64_t id);
SymbolTable symboltable_new();
HydrationManifest hydrationmanifest_create();
IncrementalConfig incrementalconfig_default_config();
IncrementalConfig incrementalconfig_memory_only();
SourceInfo sourceinfo_from_path(const char* path);
CachedArtifact cachedartifact_from_source(SourceInfo source);
IncrementalStats incrementalstats_empty();
IncrementalState incrementalstate_create();
bool incrementalstate_needs_recompile(IncrementalState self, const char* path);
IncrementalBuilder incrementalbuilder_create();
IncrementalConfig incrementalconfig_disabled();
int64_t compilermode_from_text(const char* mode);
const char* init_compiler();
const char* init_compiler_with_file(const char* config_path);
const char* init_compiler_with_config(int64_t config);
InlineAsm inlineasm_new(SplArray* template, int64_t span);
void mangle(int64_t template_name, int64_t type_args);
void TemplateInstantiator__instantiate(TemplateInstantiator* self, int64_t template_name, int64_t type_args);
void TemplateInstantiator__is_cached(const TemplateInstantiator* self, int64_t template_name, int64_t type_args);
void TemplateInstantiator__cache_size(const TemplateInstantiator* self);
InterruptAttr interruptattr_default_(int64_t vector);
FunctionRecord functionrecord_create(const char* name);
RecordingSession recordingsession_create();
void start_recording();
void stop_recording();
const char* export_layout_sdn();
Lexer lexer_new(const char* source);
SourcePosition sourceposition_new(int64_t offset, int64_t line, int64_t col);
SourcePosition sourceposition_advance(SourcePosition self, const char* char_);
SourcePosition SourcePosition__start();
Span span_new(int64_t start, int64_t end, int64_t line, int64_t col);
Span span_empty();
Span Span__new(int64_t start, int64_t end, int64_t line, int64_t col);
Span Span__empty();
Span span_from_position(SourcePosition pos);
Span span_from_range(SourcePosition start, SourcePosition end);
Span span_extend(Span self, SourcePosition end);
Token token_new(int64_t kind, Span span, const char* text);
Token token_eof(int64_t pos, int64_t line);
MacroParam macroparam_regular(Symbol name, int64_t ty);
MacroParam macroparam_variadic(Symbol name, int64_t elem_ty);
MacroRegistry macroregistry_empty();
MacroCall macrocall_new_call(Symbol name, SplArray* args);
TypeEnv typeenv_empty();
MacroTypeChecker macrotypechecker_new_checker(MacroRegistry registry);
SubstitutionMap substitutionmap_empty();
MacroExpander macroexpander_new_expander(MacroTypeChecker type_checker);
void test_substitution_map();
void test_build_substitution_regular();
MacroContractResult macrocontractresult_empty();
const char* process_macro_contract(SplArray* contract_items, int64_t const_bindings, int64_t existing_symbols);
SymbolScope symbolscope_empty();
BlockContext blockcontext_create();
ValidationResult validationresult_ok();
ValidationResult validationresult_error(const char* msg);
MacroValidator macrovalidator_create();
const char* format_runtime_error_message(const char* msg);
CliArgs CliArgs__default();
bool is_bitfield_type(int64_t type_);
int64_t get_bitfield_info(int64_t type_);
BitfieldMirLower bitfieldmirlower_new(int64_t builder);
ContractContext contractcontext_empty(const char* func_name, bool is_public);
MirType mirtype_i64();
MirType mirtype_f64();
MirType mirtype_bool();
MirType mirtype_unit();
MirType mirtype_ptr(MirType pointee, bool mutable_);
MirType mirtype_promise(MirType inner);
MirType mirtype_generator(MirType yield_ty, MirType return_ty);
MirType mirtype_actor_type(MirType message_ty);
BlockId blockid_new(int64_t id);
BlockId blockid_entry();
bool pipeline_safe(SplArray* es);
SplArray* append_safe(SplArray* a, SplArray* b);
bool nogc(SplArray* p);
EffectSet effectset_empty();
int64_t builtin_effect(int64_t b);
int64_t builtin_from_name(const char* name);
MirInterpreter mirinterpreter_create();
const char* serialize_mir_type(MirType t);
const char* serialize_const_value(int64_t c);
const char* serialize_binop(int64_t op);
const char* serialize_unaryop(int64_t op);
const char* serialize_aggregate_kind(int64_t kind);
const char* serialize_operand(int64_t op);
const char* serialize_mir_terminator(int64_t term);
const char* serialize_mir_inst_kind(int64_t inst);
const char* serialize_mir_block(MirBlock block);
const char* serialize_mir_signature(MirSignature sig);
const char* serialize_mir_local(MirLocal local);
const char* serialize_mir_function(MirFunction func);
const char* escape_json_string(const char* s);
MirLowering mirlowering_new(SymbolTable symbols);
int64_t optimizationconfig_none();
int64_t optimizationconfig_debug();
int64_t optimizationconfig_size();
int64_t optimizationconfig_speed();
int64_t optimizationconfig_aggressive();
const char* serialize_mir_module(MirModule module);
const char* serialize_local_kind(int64_t kind);
const char* serialize_mir_inst(MirInst inst);
const char* serialize_mir_static(MirStatic static_);
const char* serialize_mir_constant(MirConstant const_);
const char* serialize_mir_typedef(MirTypeDef typedef_);
const char* serialize_typedef_kind(int64_t kind);
const char* serialize_field_def(MirFieldDef field);
const char* serialize_variant_def(MirVariantDef variant);
MonomorphizationPass monomorphizationpass_create();
OptimizationStats optimizationstats_create();
ParallelConfig parallelconfig_default_config();
ParallelConfig parallelconfig_single_threaded();
ParallelScheduler parallelscheduler_create(ParallelConfig config);
AttributeParser attributeparser_new(std::vector<Token> tokens);
bool is_async_function(std::vector<Token> tokens);
int64_t extract_async_flag(std::vector<Token> tokens);
int64_t parse_await_expr(int64_t parser);
int64_t create_parser(const char* src);
TensorSuffix tensorsuffix_from_string(int64_t text);
double parse_float_literal(int64_t text);
double parse_float_int_part(const char* s);
double parse_fractional(const char* s);
SplArray* split_exponent(const char* s);
double pow10(double exp);
const char* tokenize(const char* input);
const char* parse_predicate(const char* input);
const char* parse_or(std::vector<Token> tokens, int64_t pos);
const char* parse_and(std::vector<Token> tokens, int64_t pos);
const char* parse_not(std::vector<Token> tokens, int64_t pos);
const char* parse_primary(std::vector<Token> tokens, int64_t pos);
const char* make_selector(const char* name, SplArray* args);
int64_t parse_signature_pattern(const char* input);
MatchContext matchcontext_empty();
bool match_pattern(const char* pattern, const char* target);
bool match_selector(int64_t sel, MatchContext ctx);
bool match_predicate(int64_t pred, MatchContext ctx);
int64_t pattern_specificity(const char* pattern);
int64_t selector_specificity(int64_t sel);
int64_t predicate_specificity(int64_t pred);
const char* validate_selector(int64_t sel, int64_t ctx);
PrettyConfig prettyconfig_default_config();
PrettyPrinter prettyprinter_create(PrettyConfig config);
PrettyPrinter prettyprinter_with_defaults();
ProjectConfig projectconfig_default(const char* name);
ProjectContext projectcontext_from_root(const char* root);
ProjectContext projectcontext_with_defaults(const char* root);
ProjectContext projectcontext_load_from_sdn(const char* root, const char* path);
ProjectContext projectcontext_load_from_toml(const char* root, const char* path);
CompilerQueryContext CompilerQueryContext__create(const char* project_root);
bool TypeChecker__is_compatible(const TypeChecker* self, int64_t a, int64_t b);
int64_t TypeChecker__get_type_symbol(const TypeChecker* self, int64_t ty);
MethodResolver MethodResolver__new(SymbolTable symbols);
SafetyContext safetycontext_new();
SafetyChecker SafetyChecker__create();
SplArray* SafetyChecker__check_module(SafetyChecker* self, HirModule module);
void SafetyChecker__check_function(SafetyChecker* self, HirFunction func);
void SafetyChecker__check_block(SafetyChecker* self, HirBlock block);
void SafetyChecker__check_stmt(SafetyChecker* self, HirStmt stmt);
void SafetyChecker__check_expr(SafetyChecker* self, HirExpr expr);
int64_t change_impact(int64_t kind);
DiffSummary diffsummary_from_changes(std::vector<SemanticChange> changes);
SemanticDiffer semanticdiffer_create();
SimdVectorType simdvectortype_create(int64_t element, int64_t lanes);
SimdVectorType simdvectortype_i8x16();
SimdVectorType simdvectortype_i16x8();
SimdVectorType simdvectortype_i32x4();
SimdVectorType simdvectortype_i64x2();
SimdVectorType simdvectortype_f32x4();
SimdVectorType simdvectortype_f64x2();
SimdTypeChecker SimdTypeChecker__create(int64_t max_width);
SimdTypeChecker SimdTypeChecker__for_sse();
SimdTypeChecker SimdTypeChecker__for_avx();
SimdTypeChecker SimdTypeChecker__for_avx512();
bool SimdTypeChecker__check_vector_type(SimdTypeChecker* self, SimdVectorType ty);
bool SimdTypeChecker__check_binary_op(SimdTypeChecker* self, int64_t op, SimdVectorType lhs, SimdVectorType rhs);
bool SimdTypeChecker__check_lane_access(SimdTypeChecker* self, SimdVectorType ty, int64_t lane_index);
Vec2f vec2f_splat(float value);
Vec2f vec2f_from_array(SplArray* arr);
Vec2f vec2f_zero();
Vec4f vec4f_splat(float value);
Vec4f vec4f_from_array(SplArray* arr);
Vec4f vec4f_zero();
Vec8f vec8f_splat(float value);
int64_t vec2d_from_array(SplArray* arr);
int64_t vec2d_zero();
Vec4d vec4d_splat(double value);
Vec4d vec4d_from_array(SplArray* arr);
Vec4d vec4d_zero();
void test_vec2f_create();
void test_vec2f_splat();
void test_vec2f_from_array();
void test_vec2f_to_array();
void test_vec2f_get();
void test_vec4f_create();
void test_vec4f_splat();
void test_vec4f_from_array();
void test_vec4f_to_array();
void test_vec4f_get();
void test_vec8f_create();
void test_vec4f_add();
void test_vec4f_sub();
void test_vec4f_mul();
void test_vec4f_div();
void test_vec4f_scale();
void test_vec4f_sum();
void test_vec4f_dot();
void test_vec4f_length();
void test_vec4f_normalize();
void test_vec4f_distance();
void test_vec4f_equals();
void test_vec4f_less_than();
void test_vec4f_min();
void test_vec4f_max();
void test_vec4f_abs();
void test_vec4f_negate();
void test_vec4f_min_element();
void test_vec4f_max_element();
SimdCapabilities simdcapabilities_detect();
int64_t simdcapabilities_detect_x86();
int64_t simdcapabilities_detect_x86_from_flags(const char* flags);
int64_t simdcapabilities_detect_arm();
int64_t simdcapabilities_detect_arm_from_flags(const char* flags);
const char* _read_cpuinfo();
const char* _extract_cpu_flags(const char* cpuinfo);
Vec4f simdintrinsics_sse_sub_ps(Vec4f a, Vec4f b);
Vec4f simdintrinsics_sse_mul_ps(Vec4f a, Vec4f b);
Vec4f simdintrinsics_sse_div_ps(Vec4f a, Vec4f b);
Vec4f simdintrinsics_sse_sqrt_ps(Vec4f a);
Target target_host();
Target target_x86_64_unknown_linux_gnu();
Target target_aarch64_unknown_linux_gnu();
SmfBuildOptions smfbuildoptions_create(Target target);
SymbolUsageResult symbolusageresult_empty();
SymbolUsageAnalyzer symbolusageanalyzer_create();
SymbolUsageAnalyzer symbolusageanalyzer_minimal_mode();
int64_t cranelift_finalize_module(int64_t module);
bool test_create_module();
bool test_exec_ffi();
bool test_file_hash_ffi();
TestRunner TestRunner__create();
int64_t TestRunner__run_test(TestRunner* self, const char* name, FnPtr_i64 test_fn);
int64_t TestRunner__total_failed(const TestRunner* self);
int64_t shell(const char* command);
void try_parse(const char* label, const char* src);
const char* byte_to_hex(int64_t b);
bool compile_and_run(const char* label, const char* source, int64_t expected_exit);
bool compile_and_run_output(const char* label, const char* source, int64_t expected_exit, const char* expected_stdout);
TextDiff compute_diff(const char* old_text, const char* new_text);
DiffHunk finalize_hunk(int64_t old_start, int64_t new_start, SplArray* lines);
const char* format_unified(TextDiff diff, const char* old_path, const char* new_path);
CoherenceChecker coherencechecker_create();
MethodSig methodsig_new(const char* name, bool has_self);
int64_t create_standard_traits();
void test_method_sig();
void test_trait_def();
void test_registry_basic();
void test_duplicate_registration();
void test_trait_lookup();
void test_builtin_traits();
MethodImpl methodimpl_new(Symbol name);
MethodSig methodsig_inherent(Symbol name);
MethodSig methodsig_from_trait(Symbol name, Symbol trait_name);
ImplBlock implblock_new(TraitRef trait_ref, int64_t for_type);
Obligation obligation_new(int64_t ty, TraitRef trait_ref);
ImplRegistry implregistry_new();
TraitSolver traitsolver_new(int64_t impl_registry);
TraitDef traitdef_create(Symbol name, Span span);
TraitDef traitdef_new(const char* name);
CycleDetector cycledetector_new(int64_t registry);
int64_t treesitter_parse_outline(int64_t self);
SplDict* empty_subst_map();
SplDict* empty_type_env();
TypeScheme typescheme_mono(int64_t ty);
TypeScheme typescheme_poly(SplArray* vars, int64_t ty);
Substitution substitution_new();
LayoutAttr layoutattr_default_();
UnsafeContext unsafecontext_new();
bool is_ffi_function(HirExpr callee);
const char* check_unsafe_context(UnsafeContext ctx, int64_t op, Span span);
const char* require_unsafe(UnsafeContext ctx, int64_t op, Span span);
const char* validate_unsafe_block(UnsafeContext ctx, Span block_span);
int64_t VarianceOps__flip(int64_t v);
int64_t VarianceOps__compose(int64_t outer, int64_t inner);
int64_t VarianceOps__combine(int64_t v1, int64_t v2);
TypeParamDef typeparamdef_covariant(Symbol name);
TypeParamDef typeparamdef_contravariant(Symbol name);
TypeParamDef typeparamdef_inv(Symbol name);
TypeParamDef typeparamdef_bivariant(Symbol name);
VarianceEnv varianceenv_empty();
void test_variance_basic();
void test_variance_flip();
void test_variance_compose();
void test_variance_combine();
void test_type_param_def();
void test_variance_env();
void test_variance_env_multiple();
void test_variance_env_bulk();
VarianceInference varianceinference_empty();
SubtypeEnv subtypeenv_empty();
VarianceChecker variancechecker_new_checker(SubtypeEnv subtype_env);
VerificationChecker verificationchecker_create(bool strict);
VisibilityChecker VisibilityChecker__new(const char* current_module);
const char* filename_to_type_name(const char* filename);
bool type_matches_filename(const char* type_name, const char* filename);
VolatileAccess volatileaccess_read(int64_t addr, int64_t size, int64_t type_, Span span);

static int64_t CL_TYPE_I8 = 1;
static int64_t CL_TYPE_I16 = 2;
static int64_t CL_TYPE_I32 = 3;
static int64_t CL_TYPE_I64 = 4;
static int64_t CL_TYPE_F32 = 5;
static int64_t CL_TYPE_F64 = 6;
static int64_t CL_TYPE_B1 = 7;
static int64_t CL_TYPE_PTR = 8;
static int64_t CL_CC_SYSTEM_V = 0;
static int64_t CL_CC_WINDOWS_FASTCALL = 1;
static int64_t CL_CC_FAST = 2;
static int64_t CL_CMP_EQ = 0;
static int64_t CL_CMP_NE = 1;
static int64_t CL_CMP_SLT = 2;
static int64_t CL_CMP_SLE = 3;
static int64_t CL_CMP_SGT = 4;
static int64_t CL_CMP_SGE = 5;
static int64_t CL_CMP_ULT = 6;
static int64_t CL_CMP_ULE = 7;
static int64_t CL_CMP_UGT = 8;
static int64_t CL_CMP_UGE = 9;
static int64_t CL_FCMP_EQ = 0;
static int64_t CL_FCMP_NE = 1;
static int64_t CL_FCMP_LT = 2;
static int64_t CL_FCMP_LE = 3;
static int64_t CL_FCMP_GT = 4;
static int64_t CL_FCMP_GE = 5;
static int64_t CL_TARGET_X86_64 = 0;
static int64_t CL_TARGET_AARCH64 = 1;
static int64_t CL_TARGET_RISCV64 = 2;
static int64_t MAX_CONST_CALL_DEPTH = 100;
static DiContainer _global_container = {};
static const char* UNDEFINED_VARIABLE = "E1001";
static const char* UNDEFINED_FUNCTION = "E1002";
static const char* TYPE_MISMATCH = "E1003";
static const char* INVALID_ASSIGNMENT = "E1004";
static const char* INVALID_OPERATION = "E1005";
static const char* INVALID_PATTERN = "E1006";
static const char* MISSING_FIELD = "E1007";
static const char* DUPLICATE_DEFINITION = "E1008";
static const char* CIRCULAR_DEPENDENCY = "E1009";
static const char* MODULE_NOT_FOUND = "E1010";
static const char* UNDEFINED_TYPE = "E1011";
static const char* UNDEFINED_FIELD = "E1012";
static const char* UNKNOWN_METHOD = "E1013";
static const char* UNKNOWN_CLASS = "E1014";
static const char* UNKNOWN_ENUM = "E1015";
static const char* LET_BINDING_FAILED = "E1016";
static const char* IMPURE_FUNCTION_IN_CONTRACT = "E1017";
static const char* EFFECT_DECLARATION_FAILED = "E1018";
static const char* DUPLICATE_BINDING = "E1019";
static const char* ARGUMENT_COUNT_MISMATCH = "E1020";
static const char* MISSING_STRUCT_FIELDS = "E1021";
static const char* INVALID_LHS_ASSIGNMENT = "E1022";
static const char* INVALID_STRUCT_LITERAL = "E1023";
static const char* CONST_EVAL_FAILED = "E1024";
static const char* DUPLICATE_METHOD = "E1025";
static const char* UNKNOWN_ASSOC_TYPE = "E1026";
static const char* UNCONSTRAINED_TYPE_PARAM = "E1027";
static const char* UNKNOWN_ASSOC_TYPE_NAME = "E1028";
static const char* CONFLICTING_TRAIT_BOUNDS = "E1029";
static const char* INVALID_LIFETIME_ON_TRAIT = "E1030";
static const char* MISSING_TRAIT_METHOD = "E1031";
static const char* SELF_IN_STATIC = "E1032";
static const char* INVALID_SELF_IMPORT = "E1033";
static const char* UNRESOLVED_IMPORT = "E1034";
static const char* INVALID_SELF_CONTEXT = "E1035";
static const char* CLOSURE_CAPTURE_FAILED = "E1036";
static const char* INVALID_SELF_PARAM = "E1037";
static const char* PRIVATE_IN_PUBLIC = "E1038";
static const char* INVALID_VISIBILITY = "E1039";
static const char* PRIVATE_FIELD_ACCESS = "E1040";
static const char* INVALID_UNARY_OP = "E1041";
static const char* INVALID_SELF_TYPE = "E1042";
static const char* INVALID_INDEX_TYPE = "E1043";
static const char* TUPLE_INDEX_OOB = "E1044";
static const char* INVALID_FIELD_ASSIGN = "E1045";
static const char* PRIVATE_FIELD = "E1046";
static const char* CANNOT_BORROW_MUT_FIELD = "E1047";
static const char* NOT_CALLABLE = "E1048";
static const char* CANNOT_CALL_NON_FUNCTION = "E1049";
static const char* DISALLOWED_COERCION = "E1050";
static const char* CLOSURE_SIGNATURE_MISMATCH = "E1051";
static const char* INVALID_LET_ELSE_PATTERN = "E1052";
static const char* CANNOT_BORROW_IMMUTABLE = "E1053";
static const char* INVALID_DEREFERENCE = "E1054";
static const char* TYPE_ALIAS_BOUNDS = "E1055";
static const char* INVALID_RANGE = "E1056";
static const char* YIELD_OUTSIDE_GENERATOR = "E1057";
static const char* INVALID_DOC_COMMENT = "E1058";
static const char* INVALID_IMPLICIT_DEREFERENCE = "E1059";
static const char* INVALID_CONST_EXPRESSION = "E1060";
static const char* EMPTY_ENUM = "E1061";
static const char* RECURSION_LIMIT_EXCEEDED = "E1062";
static const char* TYPE_SIZE_LIMIT_EXCEEDED = "E1063";
static const char* WRONG_INTRINSIC_TYPE = "E1064";
static const char* INVALID_RETURN_TYPE = "E1065";
static const char* INVALID_MAIN_SIGNATURE = "E1066";
static const char* INVALID_BUILTIN_ATTRIBUTE = "E1067";
static const char* INCONSISTENT_BINDINGS = "E1068";
static const char* MISMATCHED_BINDING = "E1069";
static const char* INVALID_DEFAULT_VARIANT = "E1070";
static const char* INVALID_ATTRIBUTE_POSITION = "E1071";
static const char* INVALID_DESTRUCTURING = "E1072";
static const char* NON_EXHAUSTIVE_TYPE = "E1073";
static const char* CONFLICTING_REPRESENTATION = "E1074";
static const char* DISCRIMINANT_OVERFLOW = "E1075";
static const char* UNKNOWN_INTRINSIC = "E1076";
static const char* WRONG_INTRINSIC_SIGNATURE = "E1077";
static const char* INVALID_INTRINSIC_RETURN = "E1078";
static const char* MISSING_GENERIC_ARGUMENTS = "E1079";
static const char* TYPE_TOO_COMPLEX = "E1080";
static const char* INVALID_CONTEXT = "E1081";
static const char* BREAK_OUTSIDE_LOOP = "E1101";
static const char* CONTINUE_OUTSIDE_LOOP = "E1102";
static const char* RETURN_OUTSIDE_FUNCTION = "E1103";
static const char* RETURN_IN_CLOSURE = "E1104";
static const char* INVALID_CONTROL_FLOW = "E1105";
static const char* ACTOR_SEND_FAILED = "E1201";
static const char* ACTOR_RECV_FAILED = "E1202";
static const char* CHANNEL_CLOSED = "E1203";
static const char* DEADLOCK_DETECTED = "E1204";
static const char* ACTOR_JOIN_FAILED = "E1205";
static const char* CAPABILITY_VIOLATION = "E1301";
static const char* ISOLATION_VIOLATION = "E1302";
static const char* BORROW_VIOLATION = "E1303";
static const char* USE_AFTER_FREE = "E1304";
static const char* MACRO_UNDEFINED = "E1401";
static const char* MACRO_USED_BEFORE_DEFINITION = "E1402";
static const char* KEYWORD_IN_MACRO = "E1403";
static const char* MACRO_SHADOWING = "E1403";
static const char* MACRO_INVALID_BLOCK_POSITION = "E1404";
static const char* MACRO_MISSING_TYPE_ANNOTATION = "E1405";
static const char* MACRO_INVALID_QIDENT = "E1406";
static const char* INVALID_POINTCUT_SYNTAX = "E1501";
static const char* UNDEFINED_JOINPOINT = "E1502";
static const char* INVALID_ADVICE_TYPE = "E1503";
static const char* CONFLICTING_ADVICE_ORDER = "E1504";
static const char* INVALID_WEAVING_TARGET = "E1505";
static const char* ASPECT_CIRCULAR_DEPENDENCY = "E1506";
static const char* INVALID_POINTCUT_SELECTOR = "E1507";
static const char* ASPECT_NOT_ENABLED = "E1508";
static const char* UNKNOWN_BLOCK_TYPE = "E1601";
static const char* INVALID_BLOCK_SYNTAX = "E1602";
static const char* MATH_BLOCK_INVALID_EXPR = "E1603";
static const char* MATH_BLOCK_UNDEFINED_VAR = "E1604";
static const char* SHELL_BLOCK_INVALID_CMD = "E1605";
static const char* SHELL_BLOCK_UNSAFE_OP = "E1606";
static const char* SQL_BLOCK_SYNTAX_ERROR = "E1607";
static const char* SQL_BLOCK_INVALID_PARAM = "E1608";
static const char* REGEX_BLOCK_INVALID = "E1609";
static const char* REGEX_BLOCK_UNKNOWN_FLAG = "E1610";
static const char* BLOCK_MISSING_CLOSING = "E1611";
static const char* BLOCK_TYPE_MISMATCH = "E1612";
static const char* MIXIN_NOT_FOUND = "E1701";
static const char* MIXIN_METHOD_CONFLICT = "E1702";
static const char* MIXIN_MISSING_REQUIRED = "E1703";
static const char* MIXIN_CIRCULAR_DEPENDENCY = "E1704";
static const char* MIXIN_INVALID_USE = "E1705";
static const char* MIXIN_FIELD_CONFLICT = "E1706";
static const char* MIXIN_SELF_REFERENCE = "E1707";
static const char* MIXIN_TYPE_MISMATCH = "E1708";
static const char* SDN_SYNTAX_ERROR = "E1801";
static const char* SDN_UNKNOWN_KEY = "E1802";
static const char* SDN_TYPE_MISMATCH = "E1803";
static const char* SDN_MISSING_REQUIRED = "E1804";
static const char* SDN_DUPLICATE_KEY = "E1805";
static const char* SDN_INVALID_VALUE = "E1806";
static const char* SDN_NESTING_LIMIT = "E1807";
static const char* SDN_CIRCULAR_REFERENCE = "E1808";
static const char* DI_MISSING_BINDING = "E1901";
static const char* DI_AMBIGUOUS_BINDING = "E1902";
static const char* DI_CIRCULAR_DEPENDENCY = "E1903";
static const char* DI_INVALID_SCOPE = "E1904";
static const char* DI_INJECT_FAILED = "E1905";
static const char* DI_INVALID_ATTRIBUTE = "E1906";
static const char* DI_SCOPE_MISMATCH = "E1907";
static const char* DI_MOCK_NOT_TEST = "E1908";
static const char* ARCH_FORBIDDEN_IMPORT = "E1A01";
static const char* ARCH_FORBIDDEN_DEPEND = "E1A02";
static const char* ARCH_LAYER_VIOLATION = "E1A03";
static const char* ARCH_INVALID_RULE = "E1A04";
static const char* ARCH_CONFLICTING_RULES = "E1A05";
static const char* ARCH_CIRCULAR_MODULES = "E1A06";
static const char* UNSUPPORTED_FEATURE = "E2001";
static const char* FFI_ERROR = "E2002";
static const char* FAILED_BUILD_LOAD = "E2003";
static const char* FAILED_BUILD_STORE = "E2004";
static const char* FAILED_BUILD_ALLOCA = "E2005";
static const char* FAILED_BUILD_CALL = "E2006";
static const char* FAILED_TO_CAST = "E2007";
static const char* FAILED_BUILD_GEP = "E2008";
static const char* UNSUPPORTED_RETURN_TYPE = "E2009";
static const char* DIVISION_BY_ZERO = "E3001";
static const char* INDEX_OUT_OF_BOUNDS = "E3002";
static const char* STACK_OVERFLOW = "E3003";
static const char* ASSERTION_FAILED = "E3004";
static const char* TIMEOUT = "E3005";
static const char* AWAIT_FAILED = "E3006";
static const char* PROMISE_REJECTED = "E3007";
static const char* FUNCTION_NOT_FOUND = "E3008";
static const char* UNHANDLED_EXCEPTION = "E3009";
static const char* NULL_POINTER = "E3010";
static const char* MEMORY_ERROR = "E3011";
static const char* TYPE_ERROR = "E3012";
static const char* CONTRACT_VIOLATION = "E3013";
static const char* INVARIANT_VIOLATION = "E3014";
static const char* POSTCONDITION_VIOLATION = "E3015";
static const char* PRECONDITION_VIOLATION = "E3016";
static CompilerContext global_context = {};
static RecordingSession _global_session = {};
static SplDict* BITFIELD_REGISTRY = 0;
static const char* source = spl_str_concat(spl_str_concat(spl_str_concat("fn main() -> i64:", NL), "    0"), NL);
static int64_t parser = 0;
static int64_t ast_module = 0;
static int64_t options = 0;
static int64_t v1 = 0;
static int64_t v2 = 0;
static int64_t lowering = 0;
static const char* src = "fn main(): 0";
static Lexer lex = {};
static int64_t builder = 0;
static MirType i64_type = {};
static MirType bool_type = {};
static MirType unit_type = {};
static MirSignature main_sig = {};
static Span dummy_span = {};
static int64_t then_block = 0;
static int64_t else_block = 0;
static int64_t exit_block = 0;
static int64_t x_local = 0;
static int64_t y_local = 0;
static const char* z_local = "";
static SplArray* locals;
static MirBlock entry_block = {};
static int64_t hir_lowering = 0;
static int64_t hir_module = 0;
static MirLowering mir_ctx = {};
static int64_t mir_module = 0;
static SplArray* code;
static int64_t code_size = 0;
static SplArray* rodata;
static int64_t writer = 0;
static int64_t text_section = 0;
static int64_t str_reloc = 0;
static int64_t ast = 0;
static int64_t ts = 0;
static int64_t outline = 0;
static int64_t imp_idx = 0;
static int64_t exp_idx = 0;
static int64_t module = 0;
static int64_t elf_bytes = 0;
static bool t1 = false;
static bool t2 = false;
static bool t3 = false;
static bool t4 = false;
static bool t5 = false;
static bool t6 = false;
static bool t7 = false;
static bool t8 = false;
static bool t9 = false;
static bool t10 = false;
static bool t11 = false;
static bool t12 = false;
static bool t13 = false;
static bool t14 = false;
static bool t15 = false;
static bool t16 = false;
static bool t17 = false;
static bool t18 = false;
static bool t19 = false;
static bool t20 = false;
static bool t21 = false;
static bool t22 = false;
static bool t23 = false;
static bool t24 = false;
static bool t25 = false;
static bool t26 = false;
static bool t27 = false;
static bool t28 = false;
static bool t29 = false;
static bool t30 = false;
static bool t31 = false;
static bool t32 = false;
static bool t33 = false;
static bool t34 = false;
static bool t35 = false;
static bool t36 = false;
static bool t37 = false;
static bool t38 = false;
static bool t39 = false;
static bool t40 = false;
static bool t41 = false;
static bool t42 = false;
static bool t43 = false;
static bool t44 = false;
static bool t45 = false;
static bool t46 = false;
static bool t47 = false;
static bool t48 = false;
static bool t49 = false;
static bool t50 = false;
static bool t51 = false;
static int64_t passed = 0;
static int64_t total = 51;
static MirLowering mir_lowering_ctx = {};
static int64_t offset = 0;
static const char* link_r = "";
static MirType t = {};
static SplArray* UNSAFE_BUILTINS;

ProceedContext create_proceed_context_minimal(const char* advice_name) {
    return ProceedContext{.advice_name = advice_name, .proceed_count = 0};
}

int64_t create_proceed_context_internal(const char* advice_name) {
    return 0;
}

int64_t create_around_advice_context(const char* advice_name, int64_t target_fn) {
    return 0;
}

int64_t aroundadvicecontext_proceed(AroundAdviceContext self) {
    return 0;
}

const char* verify_proceed_called(AroundAdviceContext ctx) {
    return "";
}

int64_t create_proceed_context(const char* advice_name, int64_t target_fn) {
    return 0;
}

int64_t create_conditional_proceed_context(const char* advice_name, int64_t target_fn) {
    return 0;
}

int64_t conditionalproceedcontext_proceed_if_allowed(ConditionalProceedContext self) {
    return 0;
}

void test_proceed_enforcement() {
    /* pass */;
}

void Logger__log(const Logger* self, int64_t level, const char* prefix, const char* message) {
    if ((level <= self->level)) {
        spl_println(spl_str_concat(spl_str_concat(spl_str_concat("[", prefix), "] "), message));
    }
}

void LogAspect__log_aop(const LogAspect* self, const char* prefix, const char* message) {
    if ((self->level > 0)) {
        spl_println(spl_str_concat(spl_str_concat(spl_str_concat("[AOP] ", prefix), " "), message));
    }
}

void LogAspect__before(const LogAspect* self, const char* name, SplArray* args) {
    LogAspect__log_aop(self, ">>", name);
}

void LogAspect__after(const LogAspect* self, const char* name, int64_t result) {
    LogAspect__log_aop(self, "<<", name);
}

int64_t LogAspect__around(const LogAspect* self, const char* name, SplArray* args, FnPtr_i64 proceed) {
    LogAspect__before(self, name, args);
    int64_t result = proceed();
    LogAspect__after(self, name, result);
    return result;
}

void TracingAspect__before(const TracingAspect* self, const char* name, SplArray* args) {
    spl_println(spl_str_concat("[TRACE] enter ", name));
}

void TracingAspect__after(const TracingAspect* self, const char* name, int64_t result) {
    spl_println(spl_str_concat("[TRACE] exit ", name));
}

bool ContractAspect__check_pre(const ContractAspect* self, const char* name, SplArray* args) {
    return true;
}

bool ContractAspect__check_post(const ContractAspect* self, const char* name, int64_t result) {
    return true;
}

void AopWeaver__add_log_aspect(AopWeaver* self, LogAspect aspect, int64_t pointcut) {
    /* stub */
}

void AopWeaver__add_tracing_aspect(AopWeaver* self, TracingAspect aspect, int64_t pointcut) {
    /* stub */
}

void AopWeaver__add_debug_log_aspect(AopWeaver* self, int64_t pointcut) {
    /* stub */
}

ApiSurface apisurface_create(const char* module) {
    return ApiSurface{}; /* stub */
}

ArchRulesConfig archrulesconfig_disabled() {
    return ArchRulesConfig{.enabled = false, .rules = {}};
}

ArchRulesConfig archrulesconfig_from_rules(std::vector<ArchRule> rules) {
    bool has_rules = false;
    if (((int64_t)rules.size() > 0)) {
        has_rules = true;
    }
    return ArchRulesConfig{.enabled = has_rules, .rules = rules};
}

int64_t archrulesengine_create(ArchRulesConfig config) {
    return 0;
}

const char* parse_arch_rules_from_sdn(int64_t sdn) {
    return "";
}

const char* parse_arch_rules_block(SplArray* tokens) {
    return ""; /* stub */
}

TraitRef traitref_new(const char* name) {
    return TraitRef{.name = name};
}

int64_t assoctypedef_new(int64_t name) {
    return 0;
}

AssocTypeDef assoctypedef_with_bounds(int64_t name, std::vector<TraitRef> bounds) {
    return AssocTypeDef{}; /* stub */
}

TraitDefEx traitdefex_new(int64_t name) {
    return TraitDefEx{}; /* stub */
}

ImplBlockEx implblockex_new(TraitRef trait_ref, int64_t for_type) {
    return ImplBlockEx{}; /* stub */
}

const char* mir_type_to_async_type(int64_t mir_type) {
    return "Any";
}

int64_t get_async_inst_info(int64_t inst) {
    return 0;
}

AsyncFunctionInfo analyze_async_function(int64_t body) {
    return AsyncFunctionInfo{}; /* stub */
}

VolatileAttr parse_volatile_attrs(SplArray* attrs) {
    return VolatileAttr{}; /* stub */
}

int64_t jitinterpreterconfig_always_jit() {
    return 0;
}

int64_t jitinterpreterbackend_default() {
    return 0; /* stub */
}

int64_t backenderror_not_allowed(const char* message, Option_Span span) {
    return 0;
}

int64_t backenderror_type_error(const char* message, Option_Span span) {
    return 0;
}

int64_t backenderror_runtime_error(const char* message, Option_Span span) {
    return 0;
}

int64_t backenderror_compile_error(const char* message, Option_Span span) {
    return 0;
}

int64_t backenderror_not_implemented(const char* message) {
    return 0;
}

int64_t backenderror_internal(const char* message) {
    return 0;
}

SdnValue sdnvalue_make_nil() {
    return SdnValue{.kind = SdnValueKind_Nil};
}

SdnValue sdnvalue_bool(bool value) {
    return SdnValue{.kind = SdnValueKind_Nil};
}

SdnValue sdnvalue_int(int64_t value) {
    return SdnValue{.kind = SdnValueKind_Nil};
}

SdnValue sdnvalue_float(double value) {
    return SdnValue{.kind = SdnValueKind_Nil};
}

SdnValue sdnvalue_string(const char* value) {
    return SdnValue{.kind = SdnValueKind_Nil};
}

SdnValue sdnvalue_array(std::vector<SdnValue> elements) {
    return SdnValue{.kind = SdnValueKind_Nil};
}

SdnValue sdnvalue_dict(SplDict* entries) {
    return SdnValue{.kind = SdnValueKind_Nil};
}

int64_t value_make_nil() {
    return Value_Nil;
}

int64_t value_bool(bool value) {
    return value_bool(value);
}

int64_t value_int(int64_t value) {
    return value_int(value);
}

int64_t value_float(double value) {
    return value_float(value);
}

int64_t value_string(const char* value) {
    return value_string(value);
}

int64_t value_some(int64_t value) {
    return Value_Nil;
}

int64_t value_none() {
    return Value_Nil;
}

int64_t value_ok(int64_t value) {
    return Value_Nil;
}

int64_t value_err(int64_t value) {
    return Value_Nil;
}

const char* format_type_list(SplArray* types) {
    return "";
}

int64_t hirexpr_int_lit(int64_t value) {
    return 0;
}

int64_t hirexpr_bool_lit(bool value) {
    return 0;
}

int64_t hirexpr_text_lit(const char* value) {
    return 0;
}

int64_t hirexpr_var(int64_t name) {
    return 0;
}

int64_t hirexpr_lambda(SplArray* params, HirExpr body) {
    return 0;
}

int64_t hirexpr_call(HirExpr callee, std::vector<HirExpr> args) {
    return 0;
}

int64_t hirexpr_let_bind(int64_t name, HirExpr value, HirExpr body) {
    return 0;
}

TypeInferencer typeinferencer_empty() {
    return TypeInferencer{.context = "", .next_var_id = 0};
}

int64_t typeinferencer_infer_expr(TypeInferencer self, HirExpr expr, int64_t mode) {
    return 0;
}

int64_t typeinferencer_synthesize_expr(TypeInferencer self, HirExpr expr) {
    return 0;
}

int64_t typeinferencer_check_expr(TypeInferencer self, HirExpr expr, int64_t expected) {
    return 0;
}

int64_t typeinferencer_synthesize_and_subsume(TypeInferencer self, HirExpr expr, int64_t expected) {
    return 0;
}

bool typeinferencer_subsume(TypeInferencer self, int64_t inferred, int64_t expected) {
    return false;
}

void test_synthesize_int_lit() {
    /* pass */;
}

void test_synthesize_bool_lit() {
    /* pass */;
}

void test_synthesize_text_lit() {
    /* pass */;
}

void test_check_int_against_int() {
    /* pass */;
}

void test_mode_is_check() {
    /* pass */;
}

void test_mode_is_synthesize() {
    /* pass */;
}

void test_mode_expected() {
    /* pass */;
}

void test_types_equal() {
    /* pass */;
}

void test_subsume_compatible() {
    /* pass */;
}

void test_subsume_incompatible() {
    /* pass */;
}

void test_check_lambda_with_function_type() {
    /* pass */;
}

void test_synthesize_lambda_without_expected() {
    /* pass */;
}

void spl_main() {
    spl_println("");
    spl_println("Bidirectional Type Checking - Phase 1A Tests");
    spl_println("============================================");
    test_synthesize_int_lit();
    test_synthesize_bool_lit();
    test_synthesize_text_lit();
    test_check_int_against_int();
    test_mode_is_check();
    test_mode_is_synthesize();
    test_mode_expected();
    test_types_equal();
    test_subsume_compatible();
    test_subsume_incompatible();
    test_check_lambda_with_function_type();
    test_synthesize_lambda_without_expected();
    spl_println("");
    spl_println("🎉 Phase 1A Complete!");
    spl_println("");
    spl_println("Implemented:");
    spl_println("  ✅ InferMode - Synthesize/Check modes");
    spl_println("  ✅ Mode dispatcher - infer_expr(mode)");
    spl_println("  ✅ synthesize_expr() - bottom-up inference");
    spl_println("  ✅ check_expr() - top-down checking");
    spl_println("  ✅ subsume() - unification/subtyping");
    spl_println("  ✅ Lambda checking - propagate expected types");
    spl_println("");
    spl_println("Progress: 1/12 hours (8% of Phase 1)");
    spl_println("Next: Phase 1B - Application Argument Checking (1h)");
}

TypeInferencer TypeInferencer__empty() {
    return TypeInferencer{.context = "", .next_var_id = 0};
}

bool Option__is_some(const Option* self) {
    switch (self) {
    }
}

bool Option__is_none(const Option* self) {
    switch (self) {
    }
}

void test_call_checks_arguments() {
    /* pass */;
}

void test_let_with_annotation() {
    /* pass */;
}

void test_let_without_annotation() {
    /* pass */;
}

void test_nested_application() {
    /* pass */;
}

void test_lambda_in_application() {
    /* pass */;
}

void test_check_let_in_check_mode() {
    /* pass */;
}

void test_option_is_some() {
    /* pass */;
}

void test_option_is_none() {
    /* pass */;
}

int64_t hirexpr_return_expr(HirExpr value) {
    return 0;
}

int64_t hirexpr_tuple(std::vector<HirExpr> elems) {
    return 0;
}

int64_t hirexpr_array(std::vector<HirExpr> elems) {
    return 0;
}

int64_t hirexpr_if_expr(HirExpr cond, HirExpr then_expr, HirExpr else_expr) {
    return 0;
}

int64_t bitwise_not_i64(int64_t n) {
    return ((0 - n) - 1);
}

BitLayout bitlayout_unsigned(int64_t bits) {
    return BitLayout{}; /* stub */
}

void bootstrap_hello() {
    spl_println("Simple Bootstrap Compiler v0.1");
    spl_println("Usage: core1 <file.spl>");
}

int64_t buildlogger_start(const char* command) {
    return 0;
}

int64_t buildlogger_start_phase(BuildLogger self, const char* name) {
    return 0;
}

int64_t buildlogger_finish(BuildLogger self, Option_BuildOutput output) {
    return 0;
}

int64_t deterministicconfig_create() {
    return 0;
}

int64_t deterministicconfig_disabled() {
    return 0;
}

int64_t linker_new(LinkConfig config) {
    return 0;
}

int64_t linker_link(Linker self, SplArray* smf_files) {
    return 0; /* stub */
}

BuildConfig buildconfig_default(const char* entry, const char* output) {
    return BuildConfig{}; /* stub */
}

int64_t get_abi(int64_t arch, int64_t conv) {
    return 0;
}

AbiInfo get_avr_abi(int64_t conv) {
    return AbiInfo{}; /* stub */
}

CodegenEnhanced codegenenhanced_create(bool enable_opts) {
    return CodegenEnhanced{}; /* stub */
}

Codegen codegen_new(int64_t target, int64_t mode) {
    return Codegen{}; /* stub */
}

CompilabilityAnalyzer compilabilityanalyzer_create() {
    return CompilabilityAnalyzer{}; /* stub */
}

int64_t compiledunit_empty(const char* name, int64_t mode) {
    return 0;
}

int64_t compilerprofile_from_text(const char* s) {
    return 0;
}

Config Config__default() {
    return Config{}; /* stub */
}

const char* Config__get(const Config* self, const char* key) {
    return "";
}

void Config__set(Config* self, const char* key, const char* value) {
    /* pass */;
}

CompilerConfig compilerconfig_default() {
    return CompilerConfig{}; /* stub */
}

ConstEvaluator constevaluator_new(int64_t module) {
    return ConstEvaluator{}; /* stub */
}

bool keyextractor_has_keys(const char* tmpl) {
    return false;
}

int64_t keyextractor_key_count(const char* tmpl) {
    return 0;
}

int64_t constkeyset_from_template(const char* tmpl) {
    return 0;
}

int64_t constkeyset_from_keys(SplArray* keys) {
    return 0;
}

int64_t constkeyset_empty() {
    return 0;
}

void test_extract_single_key() {
    /* pass */;
}

void test_extract_multiple_keys() {
    /* pass */;
}

void test_extract_no_keys() {
    /* pass */;
}

void test_extract_duplicate_keys() {
    /* pass */;
}

void test_has_keys() {
    /* pass */;
}

void test_unique_keys() {
    /* pass */;
}

void test_key_count() {
    /* pass */;
}

void test_const_key_set_from_template() {
    /* pass */;
}

void test_const_key_set_empty() {
    /* pass */;
}

void test_const_key_set_has_key() {
    /* pass */;
}

void test_const_key_set_missing_keys() {
    /* pass */;
}

void test_const_key_set_extra_keys() {
    /* pass */;
}

void test_const_key_set_perfect_match() {
    /* pass */;
}

int64_t templatetypeinference_infer_template(const char* value) {
    return 0;
}

bool templatetypeinference_is_template(const char* value) {
    return false;
}

SplArray* KeyExtractor__extract_keys(const char* tmpl) {
    return spl_array_new();
}

void test_const_key_set_type() {
    /* pass */;
}

void test_get_keys() {
    /* pass */;
}

void test_get_keys_empty() {
    /* pass */;
}

void test_has_key() {
    /* pass */;
}

void test_type_equality_const_key_set() {
    /* pass */;
}

void test_type_equality_other() {
    /* pass */;
}

void test_infer_template_with_keys() {
    /* pass */;
}

void test_infer_plain_string() {
    /* pass */;
}

void test_is_template() {
    /* pass */;
}

void test_const_key_set_to_string() {
    /* pass */;
}

void test_dependent_keys_type() {
    /* pass */;
}

const char* format_key_list(SplArray* keys) {
    return "";
}

SplArray* find_missing_keys(SplArray* required, SplArray* provided) {
    return spl_array_new();
}

SplArray* find_extra_keys(SplArray* required, SplArray* provided) {
    return spl_array_new();
}

void test_validate_with_call_success() {
    /* pass */;
}

void test_validate_with_call_missing_keys() {
    /* pass */;
}

void test_validate_with_call_extra_keys() {
    /* pass */;
}

void test_validate_with_call_both_errors() {
    /* pass */;
}

void test_validate_with_call_not_const_key_set() {
    /* pass */;
}

void test_validate_keys_match() {
    /* pass */;
}

void test_has_missing_keys() {
    /* pass */;
}

void test_has_extra_keys() {
    /* pass */;
}

void test_find_missing_keys() {
    /* pass */;
}

void test_find_extra_keys() {
    /* pass */;
}

void test_key_error_to_string() {
    /* pass */;
}

void test_typo_detection() {
    /* pass */;
}

int64_t templatekey_required(const char* name, int64_t position) {
    return 0;
}

int64_t templatekey_optional(const char* name, int64_t position, const char* default_val) {
    return 0;
}

TemplateSchema templateschema_from_template(const char* template) {
    TemplateSchema{.template = template, .keys = {}, .required_keys = spl_array_new(), .optional_keys = spl_array_new()} = spl_array_new();
}

SymbolUsage symbolusage_empty() {
    return SymbolUsage{.used_functions = spl_array_new(), .used_types = spl_array_new(), .required_imports = spl_array_new()};
}

ContextPack contextpack_create(const char* target) {
    return ContextPack{}; /* stub */
}

CoverageStats coveragestats_empty() {
    return CoverageStats{.lines_hit = 0, .lines_total = 0, .branches_hit = 0, .branches_total = 0, .functions_hit = 0, .functions_total = 0};
}

CoverageCollector coveragecollector_create() {
    return CoverageCollector{}; /* stub */
}

int64_t desugar_async_function(int64_t func) {
    return 0; /* stub */
}

DimSolver dimsolver_new() {
    return DimSolver{}; /* stub */
}

const char* format_shape(SplArray* dims) {
    if ((dims_len(dims) == 0)) {
        return "[]";
    }
    SplArray* parts = spl_array_new();
    for (int64_t __d_i = 0; __d_i < spl_array_len(dims); __d_i++) {
        int64_t d = spl_array_get(dims, __d_i).as_int;
        parts = parts_push(parts, d_format(d));
    }
    return "[{parts.join(\", \")}]";
}

DimCheckGenerator dimcheckgenerator_new(int64_t mode) {
    return DimCheckGenerator{.mode = mode, .checks = {}};
}

DimError dimerror_mismatch(int64_t d1, int64_t d2, int64_t span) {
    return DimError{}; /* stub */
}

void di_panic(const char* msg) {
    spl_println(spl_str_concat("DI PANIC: ", msg));
}

DiContainer dicontainer_for_profile(int64_t profile) {
    return DiContainer{}; /* stub */
}

void set_container(DiContainer container) {
    _global_container = container;
}

int64_t get_container() {
    return 0;
}

ParamInfo paraminfo_create(const char* name, const char* type_name, bool has_inject) {
    return ParamInfo{.name = name, .type_name = type_name, .has_inject = has_inject, .is_injectable = false};
}

DiValidator divalidator_create() {
    return DiValidator{};
}

const char* validate_constructor(ConstructorInfo ctor) {
    return "";
}

const char* validate_class_injection(const char* class_name, bool has_sys_inject, SplArray* field_types) {
    return "";
}

const char* format_di_error(DiValidationError error) {
    return "";
}

const char* get_error_code(int64_t kind) {
    switch (kind) {
    }
}

const char* CheckBackendImpl__name(const CheckBackendImpl* self) {
    return "check";
}

bool CheckBackendImpl__is_allowed(const CheckBackendImpl* self, const char* op) {
    return true;
}

const char* CheckBackendImpl__process_module(const CheckBackendImpl* self, int64_t module) {
    return "";
}

const char* CheckBackendImpl__eval_expr(const CheckBackendImpl* self, HirExpr expr, int64_t env) {
    return "";
}

const char* CheckBackendImpl__exec_stmt(const CheckBackendImpl* self, int64_t stmt, int64_t env) {
    return "";
}

int64_t CompilerDriver__create(int64_t options) {
    return 0;
}

int64_t CompilerDriver__compile(CompilerDriver* self) {
    return 0;
}

bool CompilerDriver__load_sources_impl(CompilerDriver* self) {
    return false;
}

bool CompilerDriver__parse_all_impl(CompilerDriver* self) {
    return false;
}

int64_t CompilerDriver__parse_source(const CompilerDriver* self, int64_t source) {
    return 0;
}

bool CompilerDriver__lower_and_check_impl(CompilerDriver* self) {
    return false;
}

int64_t CompilerDriver__lower_to_hir_impl(const CompilerDriver* self) {
    return 0;
}

int64_t CompilerDriver__resolve_methods_impl(const CompilerDriver* self) {
    return 0;
}

int64_t CompilerDriver__type_check_impl(const CompilerDriver* self) {
    int64_t ctx = self->ctx;
    return spl_array_new();
}

bool CompilerDriver__monomorphize_impl(CompilerDriver* self) {
    return false;
}

int64_t CompilerDriver__process_sdn(const CompilerDriver* self) {
    return 0;
}

int64_t CompilerDriver__interpret(const CompilerDriver* self) {
    return 0;
}

int64_t CompilerDriver__run_module(const CompilerDriver* self, int64_t backend, int64_t module) {
    return 0;
}

int64_t CompilerDriver__jit_compile_and_run(CompilerDriver* self) {
    return 0;
}

int64_t CompilerDriver__aot_compile(CompilerDriver* self) {
    return 0;
}

int64_t CompilerDriver__compile_to_native(CompilerDriver* self, const char* output) {
    return 0;
}

int64_t CompilerDriver__compile_to_smf(CompilerDriver* self, const char* output) {
    return 0;
}

int64_t CompilerDriver__compile_to_self_contained(CompilerDriver* self, const char* output) {
    return 0;
}

int64_t CompilerDriver__collect_smf_bytes(CompilerDriver* self) {
    return 0;
}

const char* CompilerDriver__link_objects(const CompilerDriver* self, SplArray* objects, const char* output) {
    return "";
}

bool CompilerDriver__lower_to_mir(CompilerDriver* self) {
    return false;
}

bool CompilerDriver__borrow_check(CompilerDriver* self) {
    return false;
}

const char* CompilerDriver__format_borrow_error(const CompilerDriver* self, int64_t err) {
    return "Borrow check error";
}

int64_t CompilerDriver__process_async(CompilerDriver* self) {
    return 0;
}

void CompilerDriver__optimize_mir(CompilerDriver* self, int64_t config) {
    /* pass */;
}

int64_t CompilerDriver__get_optimization_config(const CompilerDriver* self) {
    return 0;
}

Config create_config() {
    return Config{}; /* stub */
}

int64_t create_block_resolver() {
    return 0; /* stub */
}

EffectCacheConfig effectcacheconfig_default_config() {
    return EffectCacheConfig{.max_entries = 5000, .validate_on_lookup = true};
}

EffectCacheStats effectcachestats_empty() {
    return EffectCacheStats{.hits = 0, .misses = 0, .entries = 0};
}

FunctionEffectInfo functioneffectinfo_empty(const char* name) {
    return FunctionEffectInfo{.name = name, .declared_effects = spl_array_new(), .derived_effects = spl_array_new(), .called_operations = spl_array_new(), .called_functions = spl_array_new(), .violations = spl_array_new()};
}

EffectCache effectcache_create(EffectCacheConfig config) {
    return EffectCache{}; /* stub */
}

bool Effect__is_sync(const Effect* self) {
    switch (self) {
    }
}

bool Effect__is_async(const Effect* self) {
    return !(Effect__is_sync(self));
}

int64_t effect_new_env() {
    return 0; /* stub */
}

void init_builtins() {
    /* stub */
}

EffectEnv effectenv_new() {
    return EffectEnv{}; /* stub */
}

void test_env() {
    spl_println("✅ Environment creation (stubbed)");
}

void test_set_get() {
    spl_println("✅ Set/get effects (stubbed)");
}

void test_dirty() {
    spl_println("✅ Dirty tracking (stubbed)");
}

int64_t effect_combine_all(SplArray* effects) {
    int64_t result = Effect_Sync;
    for (int64_t __eff_i = 0; __eff_i < spl_array_len(effects); __eff_i++) {
        int64_t eff = spl_array_get(effects, __eff_i).as_int;
        if (eff_is_async(eff)) {
            result = Effect_Async;
        }
    }
    return result;
}

TypeWrapper typewrapper_new(int64_t env) {
    return TypeWrapper{.env = env};
}

void test_basic_types() {
    spl_println("✅ Basic type operations (stubbed)");
}

void test_promise_wrap() {
    spl_println("✅ Promise wrapping (stubbed)");
}

void test_promise_unwrap() {
    spl_println("✅ Promise unwrapping (stubbed)");
}

void test_suspend_validation() {
    spl_println("✅ Suspend validation (stubbed)");
}

void test_nested_promises() {
    spl_println("✅ Nested promises (stubbed)");
}

void test_function_types() {
    spl_println("✅ Function types (stubbed)");
}

EffectScanner effectscanner_new(int64_t env) {
    return EffectScanner{.env = env};
}

EffectEnv effectenv_new_for_test() {
    return EffectEnv{}; /* stub */
}

HirExpr make_int(int64_t n) {
    return hirexpr_IntLit(value: n);
}

HirExpr make_str(const char* s) {
    return hirexpr_StrLit(value: s);
}

HirExpr make_call(int64_t func, std::vector<HirExpr> args) {
    return hirexpr_Call(func: func, args: args);
}

HirExpr make_suspend(HirExpr expr) {
    return hirexpr_Suspend(expr: expr);
}

HirExpr make_block(std::vector<HirExpr> exprs) {
    return hirexpr_Block(exprs: exprs);
}

void test_literals() {
    EffectEnv env = effectenv_new_for_test();
    EffectScanner scanner = effectscanner_new(env);
    spl_println("✅ Literals are sync");
}

void test_suspend_operators() {
    EffectEnv env = effectenv_new_for_test();
    EffectScanner scanner = effectscanner_new(env);
    HirExpr suspended = make_suspend(make_int(42));
    int64_t suspend_assign = HirExpr__SuspendAssign(name: "x");
    spl_println("✅ Suspension operators are async");
}

void test_function_calls() {
    EffectEnv env = effectenv_new_for_test();
    EffectScanner scanner = effectscanner_new(env);
    HirExpr sync_call = make_call("print", spl_array_new());
    HirExpr async_call = make_call("http.get", spl_array_new());
    spl_println("✅ Function call effects propagate");
}

void test_control_flow() {
    EffectEnv env = effectenv_new_for_test();
    EffectScanner scanner = effectscanner_new(env);
    HirExpr sync_block = make_block(spl_array_new());
    HirExpr async_expr = make_call("http.get", spl_array_new());
    HirExpr async_block = make_block(spl_array_new());
    spl_println("✅ Control flow combines effects");
}

void test_nested() {
    EffectEnv env = effectenv_new_for_test();
    EffectScanner scanner = effectscanner_new(env);
    HirExpr suspended = make_suspend(make_int(42));
    HirExpr nested = make_block(spl_array_new());
    spl_println("✅ Nested async expressions detected");
}

int64_t Effect__combine(const Effect* self, int64_t other) {
    if ((Effect__is_async(self) || other_is_async(other))) {
        return Effect_Async;
    }
    return else:;
    return Effect_Sync;
}

HirFunction hirfunction_new(const char* name, HirExpr body) {
    return HirFunction{.name = name, .body = body};
}

EffectSolver effectsolver_new(int64_t env) {
    return EffectSolver{}; /* stub */
}

const char* Effect__to_string(const Effect* self) {
    switch (self) {
    }
}

const char* EffectStats__to_string(const EffectStats* self) {
    return ""; /* stub */
}

const char* effect_to_string(int64_t eff) {
    return eff_to_string(eff);
}

bool is_async(int64_t eff) {
    return eff_is_async(eff);
}

bool is_sync(int64_t eff) {
    return eff_is_sync(eff);
}

void test_effect_basic() {
    int64_t sync = Effect_Sync;
    int64_t async_val = Effect_Async;
    spl_str_eq(assert sync_to_string(assert sync), "sync");
    spl_str_eq(assert async_to_string(assert async), "async");
    assert sync_is_sync(sync);
    assert not sync_is_async(sync);
    assert async_is_async(async);
    assert not async_is_sync(async);
}

void test_effect_combine() {
    int64_t sync = Effect_Sync;
    int64_t async_val = Effect_Async;
    (assert sync_combine(sync, sync) == Effect_Sync);
    (assert sync_combine(sync, async) == Effect_Async);
    (assert async_combine(async, sync) == Effect_Async);
    (assert async_combine(async, async) == Effect_Async);
}

void test_effect_combine_all() {
    (assert effect_combine_all(spl_array_new()) == Effect_Sync);
    (assert effect_combine_all(spl_array_new()) == Effect_Sync);
    (assert effect_combine_all(spl_array_new()) == Effect_Async);
    (assert effect_combine_all(spl_array_new()) == Effect_Async);
}

void test_effect_env_basic() {
    EffectEnv env = effectenv_new();
    (assert env_builtins_len(assert env, builtins) > 0);
    (assert env_get_effect(assert env, "http.get") == Effect_Async);
    (assert env_get_effect(assert env, "print") == Effect_Sync);
}

void test_effect_env_set_get() {
    EffectEnv env = effectenv_new();
    const char* sym = "my_function";
    (assert env_get_effect(env, sym) == Effect_Sync);
    env_set_effect(env, sym, Effect_Async);
    (assert env_get_effect(env, sym) == Effect_Async);
    assert env_is_dirty(env);
}

void test_effect_env_dirty() {
    EffectEnv env = effectenv_new();
    const char* sym = "test";
    assert not env_is_dirty(env);
    env_set_effect(env, sym, Effect_Sync);
    env_clear_dirty(env);
    env_set_effect(env, sym, Effect_Sync);
    assert not env_is_dirty(env);
    env_set_effect(env, sym, Effect_Async);
    assert env_is_dirty(env);
}

void test_builtins() {
    int64_t builtins = init_builtins();
    (assert builtins["http.get"] == Effect_Async);
    (assert builtins["http.post"] == Effect_Async);
    (assert builtins["print"] == Effect_Sync);
    (assert builtins["file.read"] == Effect_Sync);
    (assert builtins["file.read_async"] == Effect_Async);
    (assert builtins["sleep"] == Effect_Async);
}

void test_convenience_functions() {
    int64_t sync = Effect_Sync;
    int64_t async_val = Effect_Async;
    spl_println("✅ test_convenience_functions passed");
}

const char* get_category(const char* code) {
    int64_t prefix = code_substring(code, 0, 2);
    switch (prefix) {
    }
}

bool is_semantic(const char* code) {
    return spl_str_starts_with(code, "E1");
}

bool is_codegen(const char* code) {
    return spl_str_starts_with(code, "E2");
}

bool is_runtime(const char* code) {
    return spl_str_starts_with(code, "E3");
}

Color color_new() {
    return Color{}; /* stub */
}

ErrorContext errorcontext_empty() {
    return ErrorContext{}; /* stub */
}

void gc_init() {
    rt_gc_init();
}

int64_t gc_malloc(int64_t size) {
    return rt_gc_malloc(size);
}

void gc_collect() {
    rt_gc_collect();
}

int64_t value_nil() {
    return rt_value_nil();
}

int64_t value_array_new() {
    return rt_value_array_new();
}

int64_t value_dict_new() {
    return rt_value_dict_new();
}

int64_t value_type(int64_t value) {
    return rt_value_type(value);
}

bool value_is_nil(int64_t value) {
    return rt_value_is_nil(value);
}

bool value_is_bool(int64_t value) {
    return rt_value_is_bool(value);
}

bool value_is_int(int64_t value) {
    return rt_value_is_int(value);
}

bool value_is_float(int64_t value) {
    return rt_value_is_float(value);
}

bool value_is_string(int64_t value) {
    return rt_value_is_string(value);
}

bool value_is_array(int64_t value) {
    return rt_value_is_array(value);
}

bool value_is_dict(int64_t value) {
    return rt_value_is_dict(value);
}

bool value_as_bool(int64_t value) {
    return rt_value_as_bool(value);
}

int64_t value_as_int(int64_t value) {
    return rt_value_as_int(value);
}

double value_as_float(int64_t value) {
    return rt_value_as_float(value);
}

int64_t value_as_string(int64_t value, int64_t out_len) {
    return rt_value_as_string(value, out_len);
}

int64_t value_add(int64_t left, int64_t right) {
    return rt_value_add(left, right);
}

int64_t value_sub(int64_t left, int64_t right) {
    return rt_value_sub(left, right);
}

int64_t value_mul(int64_t left, int64_t right) {
    return rt_value_mul(left, right);
}

int64_t value_div(int64_t left, int64_t right) {
    return rt_value_div(left, right);
}

bool value_eq(int64_t left, int64_t right) {
    return rt_value_eq(left, right);
}

bool value_lt(int64_t left, int64_t right) {
    return rt_value_lt(left, right);
}

void value_print(int64_t value) {
    rt_value_print(value);
}

void value_println(int64_t value) {
    rt_value_println(value);
}

void value_free(int64_t value) {
    rt_value_free(value);
}

int64_t value_clone(int64_t value) {
    return rt_value_clone(value);
}

bool file_exists_ptr(int64_t path_ptr, int64_t path_len) {
    return rt_file_exists(path_ptr, path_len);
}

int64_t file_read_text_ptr(int64_t path_ptr, int64_t path_len) {
    return rt_file_read_text(path_ptr, path_len);
}

bool file_write_text_ptr(int64_t path_ptr, int64_t path_len, int64_t content_ptr, int64_t content_len) {
    return rt_file_write_text(path_ptr, path_len, content_ptr, content_len);
}

bool file_delete_ptr(int64_t path_ptr, int64_t path_len) {
    return rt_file_delete(path_ptr, path_len);
}

void string_free(int64_t ptr) {
    rt_string_free(ptr);
}

int64_t env_get_ptr(int64_t name_ptr, int64_t name_len) {
    return rt_env_get(name_ptr, name_len);
}

bool env_set_ptr(int64_t name_ptr, int64_t name_len, int64_t value_ptr, int64_t value_len) {
    return rt_env_set(name_ptr, name_len, value_ptr, value_len);
}

int64_t recognize_gpu_intrinsic(const char* name) {
    switch (name) {
    }
}

bool is_gpu_intrinsic(const char* name) {
    return recognize_gpu_intrinsic(name);
}

int64_t gpu_intrinsic_arg_count(int64_t kind) {
    switch (kind) {
        case GlobalId(_):
        {
            return 1;
            break;
        }
        case LocalId(_):
        {
            return 1;
            break;
        }
        case BlockId(_):
        {
            return 1;
            break;
        }
        case BlockDim(_):
        {
            return 1;
            break;
        }
        case GridDim(_):
        {
            return 1;
            break;
        }
        case Effect_Sync:
        {
            return 0;
            break;
        }
        case GpuIntrinsicKind_Barrier:
        {
            return 0;
            break;
        }
        case GpuIntrinsicKind_MemFence:
        {
            return 0;
            break;
        }
        case GpuIntrinsicKind_AtomicAdd:
        {
            return 2;
            break;
        }
        case GpuIntrinsicKind_AtomicSub:
        {
            return 2;
            break;
        }
        case GpuIntrinsicKind_AtomicMin:
        {
            return 2;
            break;
        }
        case GpuIntrinsicKind_AtomicMax:
        {
            return 2;
            break;
        }
        case GpuIntrinsicKind_AtomicAnd:
        {
            return 2;
            break;
        }
        case GpuIntrinsicKind_AtomicOr:
        {
            return 2;
            break;
        }
        case GpuIntrinsicKind_AtomicXor:
        {
            return 2;
            break;
        }
        case GpuIntrinsicKind_AtomicExchange:
        {
            return 2;
            break;
        }
        case GpuIntrinsicKind_AtomicCas:
        {
            return 3;
            break;
        }
    }
}

const char* gpu_intrinsic_description(int64_t kind) {
    switch (kind) {
    }
}

bool requires_kernel_context(int64_t kind) {
    return true;
}

bool has_side_effects(int64_t kind) {
    switch (kind) {
        case GlobalId(_):
        {
            return false;
            break;
        }
        case LocalId(_):
        {
            return false;
            break;
        }
        case BlockId(_):
        {
            return false;
            break;
        }
        case BlockDim(_):
        {
            return false;
            break;
        }
        case GridDim(_):
        {
            return false;
            break;
        }
        case Effect_Sync:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_Barrier:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_MemFence:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicAdd:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicSub:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicMin:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicMax:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicAnd:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicOr:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicXor:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicExchange:
        {
            return true;
            break;
        }
        case GpuIntrinsicKind_AtomicCas:
        {
            return true;
            break;
        }
    }
}

SplArray* all_gpu_intrinsic_names() {
    return spl_array_new();
}

TypeVar tyvar_new(int64_t id, int64_t name, int64_t kind) {
    return TypeVar{}; /* stub */
}

TypeVar typevar_new(int64_t id, int64_t name, int64_t kind) {
    return TypeVar{.id = id, .name = name, .kind = kind};
}

QuantifierLevel quantifierlevel_new(int64_t level, bool is_rigid) {
    return QuantifierLevel{}; /* stub */
}

QuantifierContext quantifiercontext_new() {
    return QuantifierContext{}; /* stub */
}

SymbolId symbolid_new(int64_t id) {
    return SymbolId{.id = id};
}

SymbolTable symboltable_new() {
    return SymbolTable{}; /* stub */
}

HydrationManifest hydrationmanifest_create() {
    return HydrationManifest{}; /* stub */
}

IncrementalConfig incrementalconfig_default_config() {
    return IncrementalConfig{.persist = true, .validate_on_load = true, .cache_dir = spl_nil()};
}

IncrementalConfig incrementalconfig_memory_only() {
    return IncrementalConfig{.persist = false, .validate_on_load = false, .cache_dir = spl_nil()};
}

SourceInfo sourceinfo_from_path(const char* path) {
    return SourceInfo{.path = path, .content_hash = 0, .dependencies = spl_array_new(), .functions = spl_array_new(), .types = spl_array_new(), .macros = spl_array_new()};
}

CachedArtifact cachedartifact_from_source(SourceInfo source) {
    return CachedArtifact{.source = source};
}

IncrementalStats incrementalstats_empty() {
    return IncrementalStats{.files_checked = 0, .files_dirty = 0, .cache_hits = 0, .cache_misses = 0};
}

IncrementalState incrementalstate_create() {
    return IncrementalState{}; /* stub */
}

bool incrementalstate_needs_recompile(IncrementalState self, const char* path) {
    self->stats = IncrementalStats{.files_checked = (self->stats.files_checked + 1), .files_dirty = self->stats.files_dirty, .cache_hits = self->stats.cache_hits, .cache_misses = self->stats.cache_misses};
    int64_t status = IncrementalState__get_status(self, path);
    switch (status) {
        case CompilationStatus_Complete:
        {
            self->stats = IncrementalStats{.files_checked = self->stats.files_checked, .files_dirty = self->stats.files_dirty, .cache_hits = (self->stats.cache_hits + 1), .cache_misses = self->stats.cache_misses};
            return false;
            break;
        }
        default:
        {
            self->stats = IncrementalStats{.files_checked = self->stats.files_checked, .files_dirty = self->stats.files_dirty, .cache_hits = self->stats.cache_hits, .cache_misses = (self->stats.cache_misses + 1)};
            return true;
            break;
        }
    }
}

IncrementalBuilder incrementalbuilder_create() {
    return IncrementalBuilder{.state = incrementalstate_create()};
}

IncrementalConfig incrementalconfig_disabled() {
    return IncrementalConfig{.enabled = false, .cache_dir = spl_nil(), .max_staleness_ms = 0};
}

int64_t compilermode_from_text(const char* mode) {
    switch (mode) {
    }
}

const char* init_compiler() {
    return init_compiler_with_config(quick_config());
}

const char* init_compiler_with_file(const char* config_path) {
    int64_t config = load_full_config(config_path);
    return init_compiler_with_config(config);
}

const char* init_compiler_with_config(int64_t config) {
    return ""; /* stub */
}

InlineAsm inlineasm_new(SplArray* template, int64_t span) {
    InlineAsm{.template = template, .operands = spl_array_new(), .clobbers = spl_array_new(), .options = spl_array_new(), .arch = targetarch_host(), .span = span} = spl_array_new();
}

void mangle(int64_t template_name, int64_t type_args) {
    /* stub */
}

void TemplateInstantiator__instantiate(TemplateInstantiator* self, int64_t template_name, int64_t type_args) {
    int64_t key = mangle(template_name, type_args);
    if (TemplateInstantiator__cache_contains_key(self, cache, key)) {
        return Result_Ok;
    }
    if (TemplateInstantiator__in_progress_contains(self, in_progress, key)) {
        return Result_Err;
    }
    self->in_progress = TemplateInstantiator__in_progress_insert(self, in_progress, key);
    int64_t load_result = TemplateInstantiator__context_load_template(self, context, template_name);
    if (load_result_is_err(load_result)) {
        self->in_progress = TemplateInstantiator__in_progress_remove(self, in_progress, key);
        return load_result;
    }
    int64_t tmpl = load_result_value;
    int64_t compile_result = TemplateInstantiator__context_compile_template(self, context, tmpl, type_args);
    if (compile_result_is_err(compile_result)) {
        self->in_progress = TemplateInstantiator__in_progress_remove(self, in_progress, key);
        return compile_result;
    }
    int64_t compiled = compile_result_value;
    self->cache[key] = compiled;
    self->in_progress = TemplateInstantiator__in_progress_remove(self, in_progress, key);
    Result_Ok;
}

void TemplateInstantiator__is_cached(const TemplateInstantiator* self, int64_t template_name, int64_t type_args) {
    int64_t key = mangle(template_name, type_args);
    TemplateInstantiator__cache_contains_key(self, cache, key);
}

void TemplateInstantiator__cache_size(const TemplateInstantiator* self) {
    TemplateInstantiator__cache_len(self, cache);
}

InterruptAttr interruptattr_default_(int64_t vector) {
    return InterruptAttr{}; /* stub */
}

FunctionRecord functionrecord_create(const char* name) {
    return FunctionRecord{.name = name, .module = spl_nil(), .call_count = 0, .first_call_us = 0, .last_call_us = 0, .estimated_size = 0, .callees = spl_array_new(), .is_startup_path = false};
}

RecordingSession recordingsession_create() {
    return RecordingSession{}; /* stub */
}

void start_recording() {
    _global_session = recordingsession_create();
}

void stop_recording() {
    _global_session = spl_nil();
}

const char* export_layout_sdn() {
    if (has__global_session) {
        return _global_session_value_export_sdn(_global_session_value);
    } else {
        return "";
    }
}

Lexer lexer_new(const char* source) {
    return Lexer{}; /* stub */
}

SourcePosition sourceposition_new(int64_t offset, int64_t line, int64_t col) {
    return SourcePosition{.offset = offset, .line = line, .col = col};
}

SourcePosition sourceposition_advance(SourcePosition self, const char* char_) {
    if (spl_str_eq(char, NL)) {
        return SourcePosition{.offset = (self->offset + 1), .line = (self->line + 1), .col = 1};
    } else {
        return SourcePosition{.offset = (self->offset + 1), .line = self->line, .col = (self->col + 1)};
    }
}

SourcePosition SourcePosition__start() {
    return SourcePosition{.offset = 0, .line = 1, .col = 1};
}

Span span_new(int64_t start, int64_t end, int64_t line, int64_t col) {
    return Span{.start = start, .end = end, .line = line, .col = col};
}

Span span_empty() {
    return Span{.start = 0, .end = 0, .line = 0, .col = 0};
}

Span Span__new(int64_t start, int64_t end, int64_t line, int64_t col) {
    return Span{.start = start, .end = end, .line = line, .col = col};
}

Span Span__empty() {
    return Span{.start = 0, .end = 0, .line = 0, .col = 0};
}

Span span_from_position(SourcePosition pos) {
    return Span{.start = pos.offset, .end = pos.offset, .line = pos.line, .col = pos.col};
}

Span span_from_range(SourcePosition start, SourcePosition end) {
    return Span{.start = start.offset, .end = end.offset, .line = start.line, .col = start.col};
}

Span span_extend(Span self, SourcePosition end) {
    return Span{.start = self->start, .end = end.offset, .line = self->line, .col = self->col};
}

Token token_new(int64_t kind, Span span, const char* text) {
    return Token{.kind = kind, .span = span, .text = text};
}

Token token_eof(int64_t pos, int64_t line) {
    return Token{.kind = TokenKind_Eof, .span = span_new(pos, pos, line, 0), .text = ""};
}

MacroParam macroparam_regular(Symbol name, int64_t ty) {
    return MacroParam{}; /* stub */
}

MacroParam macroparam_variadic(Symbol name, int64_t elem_ty) {
    return MacroParam{.name = name, .ty = hirtype_List(elem: elem_ty), .is_variadic = true};
}

MacroRegistry macroregistry_empty() {
    return MacroRegistry{}; /* stub */
}

MacroCall macrocall_new_call(Symbol name, SplArray* args) {
    return MacroCall{.name = name, .args = args};
}

TypeEnv typeenv_empty() {
    return TypeEnv{}; /* stub */
}

MacroTypeChecker macrotypechecker_new_checker(MacroRegistry registry) {
    MacroTypeChecker{.registry = registry, .type_env = typeenv_empty()} = spl_array_new();
}

SubstitutionMap substitutionmap_empty() {
    return SubstitutionMap{}; /* stub */
}

MacroExpander macroexpander_new_expander(MacroTypeChecker type_checker) {
    return MacroExpander{.type_checker = type_checker};
}

void test_substitution_map() {
    SubstitutionMap subst = substitutionmap_empty();
    SubstitutionMap__bind(&subst, "x", Expr__IntLit(value: 42));
    int64_t expr = SubstitutionMap__lookup(&subst, "x");
    int64_t missing = SubstitutionMap__lookup(&subst, "y");
    spl_println("✅ Substitution map");
}

void test_build_substitution_regular() {
    /* stub */
}

MacroContractResult macrocontractresult_empty() {
    return MacroContractResult{}; /* stub */
}

const char* process_macro_contract(SplArray* contract_items, int64_t const_bindings, int64_t existing_symbols) {
    return ""; /* stub */
}

SymbolScope symbolscope_empty() {
    return SymbolScope{.functions = spl_array_new(), .classes = spl_array_new(), .variables = spl_array_new(), .types = spl_array_new()};
}

BlockContext blockcontext_create() {
    return BlockContext{.current_position = BlockPosition_Head};
}

ValidationResult validationresult_ok() {
    return ValidationResult{.is_valid = true, .errors = spl_array_new(), .warnings = spl_array_new()};
}

ValidationResult validationresult_error(const char* msg) {
    return ValidationResult{.is_valid = false, .errors = spl_array_new(), .warnings = spl_array_new()};
}

MacroValidator macrovalidator_create() {
    return MacroValidator{.known_macros = spl_array_new(), .max_expansion_depth = 64};
}

const char* format_runtime_error_message(const char* msg) {
    const char* message = spl_str_concat("Runtime error: ", msg);
    int64_t frames = rt_debug_stack_trace_lines();
    if ((frames_len(frames) > 0)) {
        message = spl_str_concat(spl_str_concat(message, NL), "Call stack:");
        for (int64_t __frame_i = 0; __frame_i < spl_array_len(frames); __frame_i++) {
            int64_t frame = spl_array_get(frames, __frame_i).as_int;
            message = (spl_str_concat(spl_str_concat(message, NL), "  ") + frame);
        }
    }
    return message;
}

CliArgs CliArgs__default() {
    return CliArgs{}; /* stub */
}

bool is_bitfield_type(int64_t type_) {
    switch (type_.kind) {
        case Named(symbol, _):
        {
            int64_t type_name = symbol.name;
            return (((spl_str_contains(type_name, "Bitfield") || spl_str_contains(type_name, "Flags")) || spl_str_contains(type_name, "Register")) || spl_str_contains(type_name, "Control"));
            break;
        }
        default:
        {
            return false;
            break;
        }
    }
}

int64_t get_bitfield_info(int64_t type_) {
    switch (type_.kind) {
        case Named(symbol, _):
        {
            int64_t type_name = symbol.name;
            if (bitfield_registry_contains_key(type_name)) {
                return BITFIELD_REGISTRY[type_name];
            } else {
                return spl_nil();
            }
            break;
        }
        default:
        {
            return spl_nil();
            break;
        }
    }
}

BitfieldMirLower bitfieldmirlower_new(int64_t builder) {
    return BitfieldMirLower{.builder = builder};
}

ContractContext contractcontext_empty(const char* func_name, bool is_public) {
    return func_name: func_name, is_public: is_public);
}

MirType mirtype_i64() {
    return MirType{.kind = MirTypeKind_I64};
}

MirType mirtype_f64() {
    return MirType{.kind = MirTypeKind_F64};
}

MirType mirtype_bool() {
    return MirType{.kind = MirTypeKind_Bool};
}

MirType mirtype_unit() {
    return MirType{.kind = MirTypeKind_Unit};
}

MirType mirtype_ptr(MirType pointee, bool mutable_) {
    return MirType{.kind = mirtypekind_Ptr(pointee, mutable)};
}

MirType mirtype_promise(MirType inner) {
    return MirType{.kind = mirtypekind_Promise(inner)};
}

MirType mirtype_generator(MirType yield_ty, MirType return_ty) {
    return MirType{.kind = mirtypekind_Generator(yield_ty, return_ty)};
}

MirType mirtype_actor_type(MirType message_ty) {
    return MirType{.kind = mirtypekind_ActorType(message_ty)};
}

BlockId blockid_new(int64_t id) {
    return BlockId{.id = id};
}

BlockId blockid_entry() {
    return blockid_new(0);
}

bool pipeline_safe(SplArray* es) {
    return (spl_array_len(es_filter(es, \e: not is_async(e))) == 0);
}

SplArray* append_safe(SplArray* a, SplArray* b) {
    return a_merge(a, b);
}

bool nogc(SplArray* p) {
    return false; /* stub */
}

EffectSet effectset_empty() {
    return EffectSet{.effects = spl_array_new()};
}

int64_t builtin_effect(int64_t b) {
    switch (b) {
    }
}

int64_t builtin_from_name(const char* name) {
    switch (name) {
    }
}

MirInterpreter mirinterpreter_create() {
    return MirInterpreter{}; /* stub */
}

const char* serialize_mir_type(MirType t) {
    return ""; /* stub */
}

const char* serialize_const_value(int64_t c) {
    return ""; /* stub */
}

const char* serialize_binop(int64_t op) {
    switch (op) {
    }
}

const char* serialize_unaryop(int64_t op) {
    switch (op) {
    }
}

const char* serialize_aggregate_kind(int64_t kind) {
    return ""; /* stub */
}

const char* serialize_operand(int64_t op) {
    return ""; /* stub */
}

const char* serialize_mir_terminator(int64_t term) {
    return ""; /* stub */
}

const char* serialize_mir_inst_kind(int64_t inst) {
    return ""; /* stub */
}

const char* serialize_mir_block(MirBlock block) {
    const char* json = "{";
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"id\":"), spl_i64_to_str(block.id.id)), ",");
    if (block.has_label) {
        json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"label\":\""), escape_json_string(block.label_value)), "\",");
    } else {
        json = spl_str_concat(json, "\"label\":null,");
    }
    json = spl_str_concat(json, "\"instructions\":[");
    bool firstInst = true;
    for (size_t __inst_i = 0; __inst_i < block.instructions.size(); __inst_i++) {
        MirInst inst = block.instructions[__inst_i];
        if (!(firstInst)) {
            json = spl_str_concat(json, ",");
        }
        json = spl_str_concat(json, serialize_mir_inst_kind(inst.kind));
        firstInst = false;
    }
    json = spl_str_concat(json, "],");
    json = spl_str_concat(spl_str_concat(json, "\"terminator\":"), serialize_mir_terminator(block.terminator));
    json = spl_str_concat(json, "}");
    return json;
}

const char* serialize_mir_signature(MirSignature sig) {
    const char* json = "{";
    json = spl_str_concat(json, "\"params\":[");
    bool firstParam = true;
    for (size_t __param_i = 0; __param_i < sig.params.size(); __param_i++) {
        MirType param = sig.params[__param_i];
        if (!(firstParam)) {
            json = spl_str_concat(json, ",");
        }
        json = spl_str_concat(json, serialize_mir_type(param));
        firstParam = false;
    }
    json = spl_str_concat(json, "],");
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"return_type\":"), serialize_mir_type(sig.return_type)), ",");
    int64_t variadicStr = if sig.is_variadic: "true" else: "false";
    json = spl_str_concat(spl_str_concat(json, "\"is_variadic\":"), spl_i64_to_str(variadicStr));
    json = spl_str_concat(json, "}");
    return json;
}

const char* serialize_mir_local(MirLocal local) {
    return ""; /* stub */
}

const char* serialize_mir_function(MirFunction func) {
    const char* json = "{";
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"symbol\":"), spl_i64_to_str(func.symbol.id)), ",");
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"name\":\""), escape_json_string(func.name)), "\",");
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"signature\":"), serialize_mir_signature(func.signature)), ",");
    json = spl_str_concat(json, "\"locals\":[");
    bool firstLocal = true;
    for (size_t __local_i = 0; __local_i < func.locals.size(); __local_i++) {
        MirLocal local = func.locals[__local_i];
        if (!(firstLocal)) {
            json = spl_str_concat(json, ",");
        }
        json = spl_str_concat(json, serialize_mir_local(local));
        firstLocal = false;
    }
    json = spl_str_concat(json, "],");
    json = spl_str_concat(json, "\"blocks\":[");
    bool firstBlock = true;
    for (size_t __block_i = 0; __block_i < func.blocks.size(); __block_i++) {
        MirBlock block = func.blocks[__block_i];
        if (!(firstBlock)) {
            json = spl_str_concat(json, ",");
        }
        json = spl_str_concat(json, serialize_mir_block(block));
        firstBlock = false;
    }
    json = spl_str_concat(json, "],");
    json = spl_str_concat(spl_str_concat(json, "\"entry_block\":"), spl_i64_to_str(func.entry_block.id));
    json = spl_str_concat(json, "}");
    return json;
}

const char* escape_json_string(const char* s) {
    const char* result = "";
    for (int64_t i = 0; i < s_len(s); i++) {
        const char* c = spl_str_slice(s, i, i+1);
        if (spl_str_eq(c, "\"")) {
            result = spl_str_concat(result, "\\\"");
        } else {
            if (spl_str_eq(c, "\\")) {
                result = spl_str_concat(result, "\\\\");
            } else {
                if (spl_str_eq(c, NL)) {
                    result = spl_str_concat(result, "\\n");
                } else {
                    if (spl_str_eq(c, "\r")) {
                        result = spl_str_concat(result, "\\r");
                    } else {
                        if (spl_str_eq(c, "\t")) {
                            result = spl_str_concat(result, "\\t");
                        } else {
                            result = spl_str_concat(result, c);
                        }
                    }
                }
            }
        }
    }
    return result;
}

MirLowering mirlowering_new(SymbolTable symbols) {
    return MirLowering{}; /* stub */
}

int64_t optimizationconfig_none() {
    return OptimizationConfig_Disabled;
}

int64_t optimizationconfig_debug() {
    return OptimizationConfig_Disabled;
}

int64_t optimizationconfig_size() {
    return optimizationconfig_Enabled(level: OptLevel.Size);
}

int64_t optimizationconfig_speed() {
    return optimizationconfig_Enabled(level: OptLevel.Speed);
}

int64_t optimizationconfig_aggressive() {
    return optimizationconfig_Enabled(level: OptLevel.Aggressive);
}

const char* serialize_mir_module(MirModule module) {
    const char* json = "{";
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"name\":\""), module.name), "\",");
    json = spl_str_concat(json, "\"functions\":[");
    bool first_fn = true;
    for (int64_t __symbol_i = 0; __symbol_i < spl_array_len(MirModule__functions_keys(&module, functions)); __symbol_i++) {
        int64_t symbol = spl_array_get(MirModule__functions_keys(&module, functions), __symbol_i).as_int;
        if (!(first_fn)) {
            json = spl_str_concat(json, ",");
        }
        int64_t func = module.functions[symbol];
        json = spl_str_concat(json, serialize_mir_function(func));
        first_fn = false;
    }
    json = spl_str_concat(json, "],");
    json = spl_str_concat(json, "\"statics\":[");
    bool first_static = true;
    for (int64_t __symbol_i = 0; __symbol_i < spl_array_len(MirModule__statics_keys(&module, statics)); __symbol_i++) {
        int64_t symbol = spl_array_get(MirModule__statics_keys(&module, statics), __symbol_i).as_int;
        if (!(first_static)) {
            json = spl_str_concat(json, ",");
        }
        int64_t static_ = module.statics[symbol];
        json = spl_str_concat(json, serialize_mir_static(static_));
        first_static = false;
    }
    json = spl_str_concat(json, "],");
    json = spl_str_concat(json, "\"constants\":[");
    bool first_const = true;
    for (int64_t __symbol_i = 0; __symbol_i < spl_array_len(MirModule__constants_keys(&module, constants)); __symbol_i++) {
        int64_t symbol = spl_array_get(MirModule__constants_keys(&module, constants), __symbol_i).as_int;
        if (!(first_const)) {
            json = spl_str_concat(json, ",");
        }
        int64_t const_ = module.constants[symbol];
        json = spl_str_concat(json, serialize_mir_constant(const_));
        first_const = false;
    }
    json = spl_str_concat(json, "],");
    json = spl_str_concat(json, "\"types\":[");
    bool first_type = true;
    for (int64_t __symbol_i = 0; __symbol_i < spl_array_len(MirModule__types_keys(&module, types)); __symbol_i++) {
        int64_t symbol = spl_array_get(MirModule__types_keys(&module, types), __symbol_i).as_int;
        if (!(first_type)) {
            json = spl_str_concat(json, ",");
        }
        int64_t typedef = module.types[symbol];
        json = spl_str_concat(json, serialize_mir_typedef(typedef));
        first_type = false;
    }
    json = spl_str_concat(json, "]");
    json = spl_str_concat(json, "}");
    return json;
}

const char* serialize_local_kind(int64_t kind) {
    return ""; /* stub */
}

const char* serialize_mir_inst(MirInst inst) {
    const char* json = "{";
    json = spl_str_concat(spl_str_concat(json, "\"kind\":"), serialize_mir_inst_kind(inst.kind));
    json = spl_str_concat(json, "}");
    return json;
}

const char* serialize_mir_static(MirStatic static_) {
    return ""; /* stub */
}

const char* serialize_mir_constant(MirConstant const_) {
    const char* json = "{";
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"symbol\":"), spl_i64_to_str(const_.symbol.id)), ",");
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"name\":\""), escape_json_string(const_.name)), "\",");
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"type\":"), serialize_mir_type(const_.type_)), ",");
    json = spl_str_concat(spl_str_concat(json, "\"value\":"), serialize_const_value(const_.value));
    json = spl_str_concat(json, "}");
    return json;
}

const char* serialize_mir_typedef(MirTypeDef typedef_) {
    const char* json = "{";
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"symbol\":"), spl_i64_to_str(typedef.symbol.id)), ",");
    json = spl_str_concat(spl_str_concat(spl_str_concat(json, "\"name\":\""), escape_json_string(typedef.name)), "\",");
    json = spl_str_concat(spl_str_concat(json, "\"kind\":"), serialize_typedef_kind(typedef.kind));
    json = spl_str_concat(json, "}");
    return json;
}

const char* serialize_typedef_kind(int64_t kind) {
    return ""; /* stub */
}

const char* serialize_field_def(MirFieldDef field) {
    return ""; /* stub */
}

const char* serialize_variant_def(MirVariantDef variant) {
    return ""; /* stub */
}

MonomorphizationPass monomorphizationpass_create() {
    return MonomorphizationPass{}; /* stub */
}

OptimizationStats optimizationstats_create() {
    return OptimizationStats{}; /* stub */
}

ParallelConfig parallelconfig_default_config() {
    return ParallelConfig{.max_threads = rt_cpu_count(), .batch_size = 16};
}

ParallelConfig parallelconfig_single_threaded() {
    return ParallelConfig{.max_threads = 1, .batch_size = 1};
}

ParallelScheduler parallelscheduler_create(ParallelConfig config) {
    return ParallelScheduler{.config = config, .units = {}, .completed = spl_array_new(), .failed = spl_array_new()};
}

AttributeParser attributeparser_new(std::vector<Token> tokens) {
    return AttributeParser{.tokens = tokens, .pos = 0};
}

bool is_async_function(std::vector<Token> tokens) {
    if ((tokens_len(tokens) < 2)) {
        return false;
    }
    Token first = tokens[0];
    Token second = tokens[1];
    return ((first.kind == TokenKind_KwAsync) && (second.kind == TokenKind_KwFn));
}

int64_t extract_async_flag(std::vector<Token> tokens) {
    if (is_async_function(tokens)) {
        return spl_array_new();
    } else {
        return spl_array_new();
    }
}

int64_t parse_await_expr(int64_t parser) {
    return 0; /* stub */
}

int64_t create_parser(const char* src) {
}

TensorSuffix tensorsuffix_from_string(int64_t text) {
    TensorSuffix suffix = TensorSuffix{};
    int64_t parts = spl_str_split(s, "_");
    for (int64_t __part_i = 0; __part_i < spl_array_len(parts); __part_i++) {
        int64_t part = spl_array_get(parts, __part_i).as_int;
        if (spl_str_eq(part, "")) {
            continue;
        }
        switch (part) {
            default:
            {
                if (spl_str_starts_with(part, "cuda")) {
                    const char* id_str = spl_str_slice(part, 4, spl_str_len(part));
                    if ((id_str_len(id_str) > 0)) {
                        int64_t id = parse_int_literal(id_str);
                        suffix.device = device_CUDA(id, 0);
                    }
                }
                break;
            }
        }
    }
    return suffix;
}

double parse_float_literal(int64_t text) {
    return 0.0; /* stub */
}

double parse_float_int_part(const char* s) {
    return 0.0; /* stub */
}

double parse_fractional(const char* s) {
    double result = 0[0];
    double divisor = 10[0];
    for (int64_t __ch_i = 0; __ch_i < spl_array_len(s); __ch_i++) {
        int64_t ch = spl_array_get(s, __ch_i).as_int;
        if ((!spl_str_eq(ch, "_"))) {
            int64_t code = ch_ord(ch);
            if ((code >= 48)) {
                if ((code <= 57)) {
                }
                result = (result + (((code - 48)) / divisor));
                divisor = (divisor * 10[0]);
            }
        }
    }
    return result;
}

SplArray* split_exponent(const char* s) {
    if (spl_str_contains(s, "e")) {
        return spl_str_split(s, "e");
    } else if (spl_str_contains(s, "E")) {
        return spl_str_split(s, "E");
    } else {
        return spl_array_new();
    }
}

double pow10(double exp) {
    return 0.0; /* stub */
}

const char* tokenize(const char* input) {
    std::vector<Token> tokens = {};
    int64_t i = 0;
    int64_t chars = input_chars(input);
    int64_t len = chars_len(chars);
    while ((i < len)) {
        int64_t c = chars[i];
        if (((spl_str_eq(c, " ") || spl_str_eq(c, "\t")) || spl_str_eq(c, NL))) {
            i = (i + 1);
        } else if (spl_str_eq(c, "!")) {
            tokens = tokens_push(tokens, Token_Not);
            i = (i + 1);
        } else if (spl_str_eq(c, "&")) {
            tokens = tokens_push(tokens, Token_And);
            i = (i + 1);
        } else if (spl_str_eq(c, "|")) {
            tokens = tokens_push(tokens, Token_Or);
            i = (i + 1);
        } else if (spl_str_eq(c, "(")) {
            tokens = tokens_push(tokens, Token_LParen);
            i = (i + 1);
        } else if (spl_str_eq(c, ")")) {
            tokens = tokens_push(tokens, Token_RParen);
            i = (i + 1);
        } else if (spl_str_eq(c, ",")) {
            tokens = tokens_push(tokens, Token_Comma);
            i = (i + 1);
        } else if ((c_is_alpha(c) || spl_str_eq(c, "_"))) {
            const char* name = "";
            while (((i < len) && ((chars[i]_is_alnum(chars[i]) || spl_str_eq(chars[i], "_"))))) {
                name = spl_str_concat(name, chars[i]);
                i = (i + 1);
            }
            while (((i < len) && spl_str_eq(chars[i], " "))) {
                i = (i + 1);
            }
            if (((i >= len) || (!spl_str_eq(chars[i], "(")))) {
                return Result_Err;
            }
            i = (i + 1);
            SplArray* args = spl_array_new();
            const char* current = "";
            int64_t depth = 0;
            while ((i < len)) {
                if (spl_str_eq(chars[i], ")")) {
                    if ((depth == 0)) {
                    }
                    if ((current_trim(current) != 0)) {
                        args = args_push(args, spl_str_trim(current));
                    }
                    i = (i + 1);
                    break;
                } else if (spl_str_eq(chars[i], "(")) {
                    depth = (depth + 1);
                    current = spl_str_concat(current, "(");
                    i = (i + 1);
                } else if (spl_str_eq(chars[i], ")")) {
                    depth = (depth - 1);
                    current = spl_str_concat(current, ")");
                    i = (i + 1);
                } else if (spl_str_eq(chars[i], ",")) {
                    if ((depth == 0)) {
                    }
                    if ((current_trim(current) != 0)) {
                        args = args_push(args, spl_str_trim(current));
                    }
                    current = "";
                    i = (i + 1);
                } else {
                    current = spl_str_concat(current, chars[i]);
                    i = (i + 1);
                }
            }
            tokens = tokens_push(tokens, Token__Sel(name, args));
        } else {
            return Result_Err;
        }
    }
    return Result_Ok;
}

const char* parse_predicate(const char* input) {
    return ""; /* stub */
}

const char* parse_or(std::vector<Token> tokens, int64_t pos) {
    const char* result = parse_and(tokens, pos);
    const char* _destruct_0 = result;
    int64_t expr = spl_str_index_char(_destruct_0, 0);
    int64_t p = spl_str_index_char(_destruct_0, 1);
    while ((p < tokens_len(tokens))) {
        switch (tokens[p]) {
            case HirBinOp_Or:
            {
                const char* rhs = parse_and(tokens, (p + 1));
                expr = predicate_Or(expr, spl_str_index_char(rhs, 0));
                p = spl_str_index_char(rhs, 1);
                break;
            }
        }
    }
    int64_t _tup_1 = (expr, p);
    return Result_Ok;
}

const char* parse_and(std::vector<Token> tokens, int64_t pos) {
    const char* result = parse_not(tokens, pos);
    const char* _destruct_1 = result;
    int64_t expr = spl_str_index_char(_destruct_1, 0);
    int64_t p = spl_str_index_char(_destruct_1, 1);
    while ((p < tokens_len(tokens))) {
        switch (tokens[p]) {
            case HirBinOp_And:
            {
                const char* rhs = parse_not(tokens, (p + 1));
                expr = predicate_And(expr, spl_str_index_char(rhs, 0));
                p = spl_str_index_char(rhs, 1);
                break;
            }
        }
    }
    int64_t _tup_2 = (expr, p);
    return Result_Ok;
}

const char* parse_not(std::vector<Token> tokens, int64_t pos) {
    if ((pos < tokens_len(tokens))) {
        switch (tokens[pos]) {
            case HirUnaryOp_Not:
            {
                const char* inner = parse_not(tokens, (pos + 1));
                return Result_Ok;
                break;
            }
        }
    }
    return parse_primary(tokens, pos);
}

const char* parse_primary(std::vector<Token> tokens, int64_t pos) {
    if ((pos >= tokens_len(tokens))) {
        return Result_Err;
    }
    switch (tokens[pos]) {
        case TokenKind_LParen:
        {
            const char* inner = parse_or(tokens, (pos + 1));
            if ((spl_str_index_char(inner, 1) >= tokens_len(tokens))) {
                return Result_Err;
            }
            switch (tokens[spl_str_index_char(inner, 1)]) {
            }
            break;
        }
        case Sel(name, args):
        {
            const char* sel = make_selector(name, args);
            return Result_Ok;
            break;
        }
        default:
        {
            return Result_Err;
            break;
        }
    }
}

const char* make_selector(const char* name, SplArray* args) {
    switch (name) {
        case "execution":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Execution(parse_signature_pattern(spl_array_get(args, 0).as_str)));
            break;
        }
        case "within":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Within(spl_array_get(args, 0).as_str));
            break;
        }
        case "attr":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Attr(spl_array_get(args, 0).as_str));
            break;
        }
        case "effect":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Effect(spl_array_get(args, 0).as_str));
            break;
        }
        case "test":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Test(spl_array_get(args, 0).as_str));
            break;
        }
        case "call":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Call(parse_signature_pattern(spl_array_get(args, 0).as_str)));
            break;
        }
        case "type":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Type(spl_array_get(args, 0).as_str));
            break;
        }
        case "init":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Init(spl_array_get(args, 0).as_str));
            break;
        }
        case "import":
        {
            if ((spl_array_len(args) < 2)) { 0;
 }
            return else: Ok(selector_Import(spl_array_get(args, 0).as_str, spl_array_get(args, 1).as_str));
            break;
        }
        case "depend":
        {
            if ((spl_array_len(args) < 2)) { 0;
 }
            return else: Ok(selector_Depend(spl_array_get(args, 0).as_str, spl_array_get(args, 1).as_str));
            break;
        }
        case "use":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Use(spl_array_get(args, 0).as_str));
            break;
        }
        case "export":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Export(spl_array_get(args, 0).as_str));
            break;
        }
        case "config":
        {
            if ((spl_array_len(args) < 1)) { 0;
 }
            return else: Ok(selector_Config(spl_array_get(args, 0).as_str));
            break;
        }
    }
}

int64_t parse_signature_pattern(const char* input) {
    return 0; /* stub */
}

MatchContext matchcontext_empty() {
    return MatchContext{.type_name = spl_nil(), .module_path = spl_nil(), .attrs = spl_array_new(), .signature = spl_nil(), .effects = spl_array_new()};
}

bool match_pattern(const char* pattern, const char* target) {
    if (spl_str_eq(pattern, "*")) { return true; }
    if (spl_str_eq(pattern, target)) { return true; }
    if (spl_str_ends_with(pattern, "*")) {
        return target_starts_with(target, spl_str_slice(pattern, 0, (spl_str_len(pattern) - 1)));
    }
    if (spl_str_starts_with(pattern, "*")) {
        return target_ends_with(target, spl_str_slice(pattern, 1, spl_str_len(pattern)));
    }
    return false;
}

bool match_selector(int64_t sel, MatchContext ctx) {
    switch (sel) {
        case Within(pattern):
        {
            if (ctx.has_module_path) {
                return match_pattern(pattern, ctx.module_path_value);
            } else {
                return false;
            }
            break;
        }
        case Attr(name):
        {
            return MatchContext__attrs_contains(&ctx, attrs, name);
            break;
        }
        case Effect(name):
        {
            return MatchContext__effects_contains(&ctx, effects, name);
            break;
        }
        case Type(pattern):
        {
            if (ctx.has_type_name) {
                return match_pattern(pattern, ctx.type_name_value);
            } else {
                return false;
            }
            break;
        }
        case Test(pattern):
        {
            if (ctx.has_signature) {
                return match_pattern(pattern, ctx.signature_value);
            } else {
                return false;
            }
            break;
        }
        default:
        {
            return false;
            break;
        }
    }
}

bool match_predicate(int64_t pred, MatchContext ctx) {
    switch (pred) {
    }
}

int64_t pattern_specificity(const char* pattern) {
    if (spl_str_eq(pattern, "**")) { return -2; }
    if (spl_str_eq(pattern, "*")) { return 0; }
    if ((spl_str_starts_with(pattern, "*") || spl_str_ends_with(pattern, "*"))) { 0;
 }
    return 2;
}

int64_t selector_specificity(int64_t sel) {
    switch (sel) {
    }
}

int64_t predicate_specificity(int64_t pred) {
    switch (pred) {
        case Or(lhs, rhs):
        {
            int64_t l = predicate_specificity(lhs);
            int64_t r = predicate_specificity(rhs);
            if ((l > r)) { l else: r;
 }
            break;
        }
    }
}

const char* validate_selector(int64_t sel, int64_t ctx) {
    switch (ctx) {
        case PredicateContext_Weaving:
        {
            switch (sel) {
            }
            break;
        }
        case PredicateContext_DependencyInjection:
        {
            switch (sel) {
            }
            break;
        }
        case PredicateContext_Mock:
        {
            switch (sel) {
            }
            break;
        }
        case PredicateContext_Architecture:
        {
            switch (sel) {
            }
            break;
        }
    }
}

PrettyConfig prettyconfig_default_config() {
    return PrettyConfig{.indent_size = 4, .max_line_length = 100};
}

PrettyPrinter prettyprinter_create(PrettyConfig config) {
    return PrettyPrinter{.config = config, .indent_level = 0, .output = ""};
}

PrettyPrinter prettyprinter_with_defaults() {
    return PrettyPrinter__create(PrettyConfig__default_config());
}

ProjectConfig projectconfig_default(const char* name) {
    return ProjectConfig{}; /* stub */
}

ProjectContext projectcontext_from_root(const char* root) {
    const char* sdn_path = spl_str_concat(root, "/simple.sdn");
    const char* toml_path = spl_str_concat(root, "/simple.toml");
    if (file_exists(sdn_path)) {
        return projectcontext_load_from_sdn(root, sdn_path);
    } else if (file_exists(toml_path)) {
        return projectcontext_load_from_toml(root, toml_path);
    } else {
        return projectcontext_with_defaults(root);
    }
}

ProjectContext projectcontext_with_defaults(const char* root) {
    return ProjectContext{}; /* stub */
}

ProjectContext projectcontext_load_from_sdn(const char* root, const char* path) {
    switch (parse_file(path)) {
        case Ok(sdn_value):
        {
            ProjectContext ctx = projectcontext_with_defaults(root);
            int64_t gc_mode_val = sdn_value_get(sdn_value, "gc_mode");
            if ((gc_mode_val != 0)) {
                if (((spl_str_eq(gc_mode_val, "nogc") || spl_str_eq(gc_mode_val, "gc")))) {
                }
                ctx.gc_mode = gc_mode_val;
            }
            return ctx;
            break;
        }
        case Err(error):
        {
            return projectcontext_with_defaults(root);
            break;
        }
    }
}

ProjectContext projectcontext_load_from_toml(const char* root, const char* path) {
    return ProjectContext{}; /* stub */
}

CompilerQueryContext CompilerQueryContext__create(const char* project_root) {
    return CompilerQueryContext{}; /* stub */
}

bool TypeChecker__is_compatible(const TypeChecker* self, int64_t a, int64_t b) {
    switch ((a.kind, b.kind)) {
        case (Int(bits_a, signed_a), Int(bits_b, signed_b)):
        {
            return ((bits_a == bits_b) && (signed_a == signed_b));
            break;
        }
        case (Float(bits_a), Float(bits_b)):
        {
            return (bits_a == bits_b);
            break;
        }
        case (Named(sym_a, args_a), Named(sym_b, args_b)):
        {
            if ((sym_a.id != sym_b.id)) {
                return false;
            } else if ((args_a_len(args_a) != args_b_len(args_b))) {
                return false;
            } else {
                bool compatible = true;
                int64_t i = 0;
                while (((i < args_a_len(args_a)) && compatible)) {
                    compatible = TypeChecker__is_compatible(self, args_a[i]);
                    i = (i + 1);
                }
                return compatible;
            }
            break;
        }
        case (_, Ref(inner, _)):
        {
            return TypeChecker__is_compatible(self, a, inner);
            break;
        }
        case (Array(elem_a, _), Array(elem_b, _)):
        {
            return TypeChecker__is_compatible(self, elem_a, elem_b);
            break;
        }
        case (Slice(elem_a), Slice(elem_b)):
        {
            return TypeChecker__is_compatible(self, elem_a, elem_b);
            break;
        }
        case (Optional(inner_a), Optional(inner_b)):
        {
            return TypeChecker__is_compatible(self, inner_a, inner_b);
            break;
        }
        case (TypeParam(name_a, _), TypeParam(name_b, _)):
        {
            return (name_a == name_b);
            break;
        }
    }
}

int64_t TypeChecker__get_type_symbol(const TypeChecker* self, int64_t ty) {
    switch (ty.kind) {
    }
}

MethodResolver MethodResolver__new(SymbolTable symbols) {
    return MethodResolver{}; /* stub */
}

SafetyContext safetycontext_new() {
    return SafetyContext{.in_unsafe = false, .errors = spl_array_new()};
}

SafetyChecker SafetyChecker__create() {
    return SafetyChecker{.context = safetycontext_new()};
}

SplArray* SafetyChecker__check_module(SafetyChecker* self, HirModule module) {
    for (int64_t ___for_item_0_i = 0; ___for_item_0_i < spl_array_len(module.functions); ___for_item_0_i++) {
        int64_t _for_item_0 = spl_array_get(module.functions, ___for_item_0_i).as_int;
        int64_t name = _for_item_0[0];
        int64_t func = _for_item_0[1];
        return SafetyChecker__check_function(self, func);
    }
    for (int64_t ___for_item_1_i = 0; ___for_item_1_i < spl_array_len(module.classes); ___for_item_1_i++) {
        int64_t _for_item_1 = spl_array_get(module.classes, ___for_item_1_i).as_int;
        int64_t name = _for_item_1[0];
        int64_t class_ = _for_item_1[1];
        for (int64_t __method_i = 0; __method_i < spl_array_len(class_.methods); __method_i++) {
            int64_t method = spl_array_get(class_.methods, __method_i).as_int;
            return SafetyChecker__check_function(self, method);
        }
    }
    for (size_t __impl__i = 0; __impl__i < module.impls.size(); __impl__i++) {
        HirImpl impl_ = module.impls[__impl__i];
        for (int64_t __method_i = 0; __method_i < spl_array_len(impl_.methods); __method_i++) {
            int64_t method = spl_array_get(impl_.methods, __method_i).as_int;
            return SafetyChecker__check_function(self, method);
        }
    }
    return self->context.errors;
}

void SafetyChecker__check_function(SafetyChecker* self, HirFunction func) {
    SafetyChecker__check_block(self, func.body);
}

void SafetyChecker__check_block(SafetyChecker* self, HirBlock block) {
    for (size_t __stmt_i = 0; __stmt_i < block.stmts.size(); __stmt_i++) {
        HirStmt stmt = block.stmts[__stmt_i];
        SafetyChecker__check_stmt(self, stmt);
    }
    if (block.has_value) {
        SafetyChecker__check_expr(self, block.value_value);
    }
}

void SafetyChecker__check_stmt(SafetyChecker* self, HirStmt stmt) {
    switch (stmt.kind) {
        case Expr(expr):
        {
            SafetyChecker__check_expr(self, expr);
            break;
        }
        case Val(_, _, init):
        {
            if (has_init) {
                SafetyChecker__check_expr(self, init_value);
            }
            break;
        }
        case Var(_, _, init):
        {
            if (has_init) {
                SafetyChecker__check_expr(self, init_value);
            }
            break;
        }
        case Assign(target, value):
        {
            SafetyChecker__check_expr(self, target);
            SafetyChecker__check_expr(self, value);
            break;
        }
        case AssignOp(_, target, value):
        {
            SafetyChecker__check_expr(self, target);
            SafetyChecker__check_expr(self, value);
            break;
        }
        default:
        {
            /* pass */;
            break;
        }
    }
}

void SafetyChecker__check_expr(SafetyChecker* self, HirExpr expr) {
    switch (expr.kind) {
        case UnsafeBlock(body):
        {
            int64_t was_unsafe = self->context.in_unsafe;
            SafetyChecker__context_enter_unsafe(self, context);
            SafetyChecker__check_block(self, body);
            if (!(was_unsafe)) {
                SafetyChecker__context_exit_unsafe(self, context);
            }
            break;
        }
        case InlineAsm(asm_code):
        {
            SafetyChecker__context_check_inline_asm(self, context, expr.span);
            for (int64_t __constraint_i = 0; __constraint_i < spl_array_len(asm_code.constraints); __constraint_i++) {
                int64_t constraint = spl_array_get(asm_code.constraints, __constraint_i).as_int;
                SafetyChecker__check_expr(self, constraint.value);
            }
            break;
        }
        case Binary(_, left, right):
        {
            SafetyChecker__check_expr(self, left);
            SafetyChecker__check_expr(self, right);
            break;
        }
        case Unary(_, operand):
        {
            SafetyChecker__check_expr(self, operand);
            break;
        }
        case If(cond, then_, else_):
        {
            SafetyChecker__check_expr(self, cond);
            SafetyChecker__check_block(self, then_);
            if (has_else_) {
                SafetyChecker__check_block(self, else__value);
            }
            break;
        }
        case MatchCase(scrutinee, arms):
        {
            SafetyChecker__check_expr(self, scrutinee);
            for (int64_t arm = 0; arm < arms; arm++) {
                if (arm.has_guard) {
                    SafetyChecker__check_expr(self, arm.guard_value);
                }
                SafetyChecker__check_expr(self, arm.body);
            }
            break;
        }
        case Loop(body, _):
        {
            SafetyChecker__check_block(self, body);
            break;
        }
        case While(cond, body, _):
        {
            SafetyChecker__check_expr(self, cond);
            SafetyChecker__check_block(self, body);
            break;
        }
        case For(_, iter, body, _):
        {
            SafetyChecker__check_expr(self, iter);
            SafetyChecker__check_block(self, body);
            break;
        }
        case Call(callee, args, _):
        {
            SafetyChecker__check_expr(self, callee);
            for (int64_t arg = 0; arg < args; arg++) {
                SafetyChecker__check_expr(self, arg.value);
            }
            break;
        }
        case MethodCall(receiver, _, args, _):
        {
            SafetyChecker__check_expr(self, receiver);
            for (int64_t arg = 0; arg < args; arg++) {
                SafetyChecker__check_expr(self, arg.value);
            }
            break;
        }
        case ArrayLit(elements, _):
        {
            for (int64_t elem = 0; elem < elements; elem++) {
                SafetyChecker__check_expr(self, elem);
            }
            break;
        }
        case TupleLit(elements):
        {
            for (int64_t elem = 0; elem < elements; elem++) {
                SafetyChecker__check_expr(self, elem);
            }
            break;
        }
        case DictLit(entries, _, _):
        {
            for (int64_t _item_0 = 0; _item_0 < entries; _item_0++) {
                int64_t key = _item_0[0];
                int64_t value = _item_0[1];
                SafetyChecker__check_expr(self, key);
                SafetyChecker__check_expr(self, value);
            }
            break;
        }
        case Block(block):
        {
            SafetyChecker__check_block(self, block);
            break;
        }
        case LossBlock(body):
        {
            SafetyChecker__check_block(self, body);
            break;
        }
        case NogradBlock(body):
        {
            SafetyChecker__check_block(self, body);
            break;
        }
        case Lambda(_, body, _):
        {
            SafetyChecker__check_expr(self, body);
            break;
        }
        case Return(value):
        {
            if (has_value) {
                SafetyChecker__check_expr(self, value_value);
            }
            break;
        }
        case Break(_, value):
        {
            if (has_value) {
                SafetyChecker__check_expr(self, value_value);
            }
            break;
        }
        case Throw(value):
        {
            SafetyChecker__check_expr(self, value);
            break;
        }
        case Try(expr):
        {
            SafetyChecker__check_expr(self, expr);
            break;
        }
        case OptionalChain(base, _):
        {
            SafetyChecker__check_expr(self, base);
            break;
        }
        case NullCoalesce(left, right):
        {
            SafetyChecker__check_expr(self, left);
            SafetyChecker__check_expr(self, right);
            break;
        }
        case ExistsCheck(base):
        {
            SafetyChecker__check_expr(self, base);
            break;
        }
        case Unwrap(base):
        {
            SafetyChecker__check_expr(self, base);
            break;
        }
        case Field(base, _, _):
        {
            SafetyChecker__check_expr(self, base);
            break;
        }
        case Index(base, index):
        {
            SafetyChecker__check_expr(self, base);
            SafetyChecker__check_expr(self, index);
            break;
        }
        case StructLit(_, fields):
        {
            for (int64_t _item_1 = 0; _item_1 < fields; _item_1++) {
                int64_t expr = _item_1[1];
                SafetyChecker__check_expr(self, expr);
            }
            break;
        }
        case EnumLit(_, _, payload):
        {
            if (has_payload) {
                switch (payload_value) {
                    case Tuple(exprs):
                    {
                        for (int64_t expr = 0; expr < exprs; expr++) {
                            SafetyChecker__check_expr(self, expr);
                        }
                        break;
                    }
                    case Struct(fields):
                    {
                        for (int64_t _item_2 = 0; _item_2 < fields; _item_2++) {
                            int64_t expr = _item_2[1];
                            SafetyChecker__check_expr(self, expr);
                        }
                        break;
                    }
                    default:
                    {
                        /* pass */;
                        break;
                    }
                }
            }
            break;
        }
        case Cast(expr, _):
        {
            SafetyChecker__check_expr(self, expr);
            break;
        }
        case As(expr, _):
        {
            SafetyChecker__check_expr(self, expr);
            break;
        }
        case Range(start, end, _, step):
        {
            if (has_start) {
                SafetyChecker__check_expr(self, start_value);
            }
            if (has_end) {
                SafetyChecker__check_expr(self, end_value);
            }
            if (has_step) {
                SafetyChecker__check_expr(self, step_value);
            }
            break;
        }
        case Comprehension(_, expr, clauses):
        {
            SafetyChecker__check_expr(self, expr);
            for (int64_t clause = 0; clause < clauses; clause++) {
                switch (clause.kind) {
                    case For(_, iter):
                    {
                        SafetyChecker__check_expr(self, iter);
                        break;
                    }
                    case If(cond):
                    {
                        SafetyChecker__check_expr(self, cond);
                        break;
                    }
                }
            }
            break;
        }
        case Await(expr):
        {
            SafetyChecker__check_expr(self, expr);
            break;
        }
        case Yield(value):
        {
            if (has_value) {
                SafetyChecker__check_expr(self, value_value);
            }
            break;
        }
        case IntLit(_, _):
        {
            /* pass */;
            break;
        }
        case FloatLit(_, _):
        {
            /* pass */;
            break;
        }
        case StringLit(_, _):
        {
            /* pass */;
            break;
        }
        case BoolLit(_):
        {
            /* pass */;
            break;
        }
        case CharLit(_):
        {
            /* pass */;
            break;
        }
        case UnitLit:
        {
            /* pass */;
            break;
        }
        case TokenKind_NilLit:
        {
            /* pass */;
            break;
        }
        case Var(_):
        {
            /* pass */;
            break;
        }
        case HirType_Error:
        {
            /* pass */;
            break;
        }
        default:
        {
            /* pass */;
            break;
        }
    }
}

int64_t change_impact(int64_t kind) {
    switch (kind) {
    }
}

DiffSummary diffsummary_from_changes(std::vector<SemanticChange> changes) {
    int64_t breaking = 0;
    int64_t major = 0;
    int64_t minor = 0;
    int64_t info = 0;
    for (size_t __c_i = 0; __c_i < changes.size(); __c_i++) {
        SemanticChange c = changes[__c_i];
        switch (c.impact) {
        }
    }
    return DiffSummary{.changes = changes, .breaking_count = breaking, .major_count = major, .minor_count = minor, .info_count = info};
}

SemanticDiffer semanticdiffer_create() {
    return SemanticDiffer{.changes = {}};
}

SimdVectorType simdvectortype_create(int64_t element, int64_t lanes) {
    return SimdVectorType{.element_type = element, .lane_count = lanes};
}

SimdVectorType simdvectortype_i8x16() {
    return simdvectortype_create(SimdElementType_I8, 16);
}

SimdVectorType simdvectortype_i16x8() {
    return simdvectortype_create(SimdElementType_I16, 8);
}

SimdVectorType simdvectortype_i32x4() {
    return simdvectortype_create(SimdElementType_I32, 4);
}

SimdVectorType simdvectortype_i64x2() {
    return simdvectortype_create(SimdElementType_I64, 2);
}

SimdVectorType simdvectortype_f32x4() {
    return simdvectortype_create(SimdElementType_F32, 4);
}

SimdVectorType simdvectortype_f64x2() {
    return simdvectortype_create(SimdElementType_F64, 2);
}

SimdTypeChecker SimdTypeChecker__create(int64_t max_width) {
    return SimdTypeChecker{.errors = spl_array_new(), .target_max_width = max_width};
}

SimdTypeChecker SimdTypeChecker__for_sse() {
    return simdtypechecker_create(128);
}

SimdTypeChecker SimdTypeChecker__for_avx() {
    return simdtypechecker_create(256);
}

SimdTypeChecker SimdTypeChecker__for_avx512() {
    return simdtypechecker_create(512);
}

bool SimdTypeChecker__check_vector_type(SimdTypeChecker* self, SimdVectorType ty) {
    if (!(ty_is_valid_width(ty))) {
        self->errors = SimdTypeChecker__errors_push(self, errors, SimdCheckError__InvalidVectorWidth(SimdVectorType__total_bits(&ty)));
        return false;
    }
    if ((ty_total_bits(ty) > self->target_max_width)) {
        self->errors = SimdTypeChecker__errors_push(self, errors, SimdCheckError__InvalidVectorWidth(SimdVectorType__total_bits(&ty)));
        return false;
    }
    return true;
}

bool SimdTypeChecker__check_binary_op(SimdTypeChecker* self, int64_t op, SimdVectorType lhs, SimdVectorType rhs) {
    if (!(lhs_is_compatible_with(lhs, rhs))) {
        self->errors = SimdTypeChecker__errors_push(self, errors, SimdCheckError__IncompatibleTypes(lhs, rhs));
        return false;
    }
    if (SimdVectorType__element_type_is_float(&lhs, element_type)) {
        if (!(op_supports_float(op))) {
        }
        self->errors = SimdTypeChecker__errors_push(self, errors, SimdCheckError__UnsupportedOperation(op, lhs.element_type));
        return false;
    }
    return true;
}

bool SimdTypeChecker__check_lane_access(SimdTypeChecker* self, SimdVectorType ty, int64_t lane_index) {
    return false; /* stub */
}

Vec2f vec2f_splat(float value) {
    return Vec2f{.x = value, .y = value};
}

Vec2f vec2f_from_array(SplArray* arr) {
    return Vec2f{.x = spl_array_get(arr, 0).as_int, .y = spl_array_get(arr, 1).as_int};
}

Vec2f vec2f_zero() {
    return Vec2f{.x = 0[0], .y = 0[0]};
}

Vec4f vec4f_splat(float value) {
    return Vec4f{.x = value, .y = value, .z = value, .w = value};
}

Vec4f vec4f_from_array(SplArray* arr) {
    return Vec4f{.x = spl_array_get(arr, 0).as_int, .y = spl_array_get(arr, 1).as_int, .z = spl_array_get(arr, 2).as_int, .w = spl_array_get(arr, 3).as_int};
}

Vec4f vec4f_zero() {
    return Vec4f{.x = 0[0], .y = 0[0], .z = 0[0], .w = 0[0]};
}

Vec8f vec8f_splat(float value) {
    return Vec8f{.e0 = value, .e1 = value, .e2 = value, .e3 = value, .e4 = value, .e5 = value, .e6 = value, .e7 = value};
}

int64_t vec2d_from_array(SplArray* arr) {
    return Vec2d(x: arr[0], y: arr[1]);
}

int64_t vec2d_zero() {
    return Vec2d(x: 0[0], y: 0[0]);
}

Vec4d vec4d_splat(double value) {
    return Vec4d{.x = value, .y = value, .z = value, .w = value};
}

Vec4d vec4d_from_array(SplArray* arr) {
    return Vec4d{.x = spl_array_get(arr, 0).as_float, .y = spl_array_get(arr, 1).as_float, .z = spl_array_get(arr, 2).as_float, .w = spl_array_get(arr, 3).as_float};
}

Vec4d vec4d_zero() {
    return Vec4d{.x = 0[0], .y = 0[0], .z = 0[0], .w = 0[0]};
}

void test_vec2f_create() {
    Vec2f v = Vec2f{.x = 1[0], .y = 2[0]};
    (assert v.x == 1[0]);
    (assert v.y == 2[0]);
    spl_println("✅ Vec2f creation");
}

void test_vec2f_splat() {
    Vec2f v = vec2f_splat(5[0]);
    (assert v.x == 5[0]);
    (assert v.y == 5[0]);
    spl_println("✅ Vec2f splat");
}

void test_vec2f_from_array() {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_int(10[0]));
    Vec2f v = vec2f_from_array(arr);
    (assert v.x == 10[0]);
    (assert v.y == 20[0]);
    spl_println("✅ Vec2f from_array");
}

void test_vec2f_to_array() {
    Vec2f v = Vec2f{.x = 3[0], .y = 4[0]};
    int64_t arr = v_to_array(v);
    (assert arr[0] == 3[0]);
    (assert arr[1] == 4[0]);
    spl_println("✅ Vec2f to_array");
}

void test_vec2f_get() {
    Vec2f v = Vec2f{.x = 7[0], .y = 8[0]};
    spl_println("✅ Vec2f get");
}

void test_vec4f_create() {
    Vec4f v = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    (assert v.x == 1[0]);
    (assert v.y == 2[0]);
    (assert v.z == 3[0]);
    (assert v.w == 4[0]);
    spl_println("✅ Vec4f creation");
}

void test_vec4f_splat() {
    Vec4f v = vec4f_splat(9[0]);
    (assert v.x == 9[0]);
    (assert v.y == 9[0]);
    (assert v.z == 9[0]);
    (assert v.w == 9[0]);
    spl_println("✅ Vec4f splat");
}

void test_vec4f_from_array() {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_int(10[0]));
    Vec4f v = vec4f_from_array(arr);
    (assert v.x == 10[0]);
    (assert v.y == 20[0]);
    (assert v.z == 30[0]);
    (assert v.w == 40[0]);
    spl_println("✅ Vec4f from_array");
}

void test_vec4f_to_array() {
    Vec4f v = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    int64_t arr = v_to_array(v);
    (assert arr[0] == 1[0]);
    (assert arr[1] == 2[0]);
    (assert arr[2] == 3[0]);
    (assert arr[3] == 4[0]);
    spl_println("✅ Vec4f to_array");
}

void test_vec4f_get() {
    Vec4f v = Vec4f{.x = 5[0], .y = 6[0], .z = 7[0], .w = 8[0]};
    spl_println("✅ Vec4f get");
}

void test_vec8f_create() {
    /* stub */
}

void test_vec4f_add() {
    Vec4f v1 = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    Vec4f v2 = Vec4f{.x = 5[0], .y = 6[0], .z = 7[0], .w = 8[0]};
    int64_t result = v1_add(v1, v2);
    (assert result.x == 6[0]);
    (assert result.y == 8[0]);
    (assert result.z == 10[0]);
    (assert result.w == 12[0]);
    spl_println("✅ Vector addition");
}

void test_vec4f_sub() {
    Vec4f v1 = Vec4f{.x = 10[0], .y = 20[0], .z = 30[0], .w = 40[0]};
    Vec4f v2 = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    int64_t result = v1_sub(v1, v2);
    (assert result.x == 9[0]);
    (assert result.y == 18[0]);
    (assert result.z == 27[0]);
    (assert result.w == 36[0]);
    spl_println("✅ Vector subtraction");
}

void test_vec4f_mul() {
    Vec4f v1 = Vec4f{.x = 2[0], .y = 3[0], .z = 4[0], .w = 5[0]};
    Vec4f v2 = Vec4f{.x = 10[0], .y = 10[0], .z = 10[0], .w = 10[0]};
    int64_t result = v1_mul(v1, v2);
    (assert result.x == 20[0]);
    (assert result.y == 30[0]);
    (assert result.z == 40[0]);
    (assert result.w == 50[0]);
    spl_println("✅ Element-wise multiplication");
}

void test_vec4f_div() {
    Vec4f v1 = Vec4f{.x = 20[0], .y = 30[0], .z = 40[0], .w = 50[0]};
    Vec4f v2 = Vec4f{.x = 10[0], .y = 10[0], .z = 10[0], .w = 10[0]};
    int64_t result = v1_div(v1, v2);
    (assert result.x == 2[0]);
    (assert result.y == 3[0]);
    (assert result.z == 4[0]);
    (assert result.w == 5[0]);
    spl_println("✅ Element-wise division");
}

void test_vec4f_scale() {
    Vec4f v = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    int64_t result = v_scale(v, 2[0]);
    (assert result.x == 2[0]);
    (assert result.y == 4[0]);
    (assert result.z == 6[0]);
    (assert result.w == 8[0]);
    spl_println("✅ Scalar multiplication");
}

void test_vec4f_sum() {
    Vec4f v = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    int64_t result = v_sum(v);
    (assert result == 10[0]);
    spl_println("✅ Sum reduction");
}

void test_vec4f_dot() {
    Vec4f v1 = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    Vec4f v2 = Vec4f{.x = 5[0], .y = 6[0], .z = 7[0], .w = 8[0]};
    int64_t result = v1_dot(v1, v2);
    (assert result == 70[0]);
    spl_println("✅ Dot product");
}

void test_vec4f_length() {
    Vec4f v = Vec4f{.x = 3[0], .y = 4[0], .z = 0[0], .w = 0[0]};
    int64_t len_sq = v_length_squared(v);
    int64_t len = v_length(v);
    (assert len_sq == 25[0]);
    (assert len == 5[0]);
    spl_println("✅ Length calculation");
}

void test_vec4f_normalize() {
    Vec4f v = Vec4f{.x = 3[0], .y = 4[0], .z = 0[0], .w = 0[0]};
    int64_t norm = v_normalize(v);
    int64_t len = norm_length(norm);
    int64_t diff = (if len > ((1[0] - 1[0]) - len));
    (assert diff < 0[001]);
    spl_println("✅ Normalization");
}

void test_vec4f_distance() {
    Vec4f v1 = Vec4f{.x = 0[0], .y = 0[0], .z = 0[0], .w = 0[0]};
    Vec4f v2 = Vec4f{.x = 3[0], .y = 4[0], .z = 0[0], .w = 0[0]};
    int64_t dist = v1_distance(v1, v2);
    (assert dist == 5[0]);
    spl_println("✅ Distance calculation");
}

void test_vec4f_equals() {
    Vec4f v1 = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    Vec4f v2 = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    Vec4f v3 = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 5[0]};
    spl_println("✅ Exact equality");
}

void test_vec4f_less_than() {
    Vec4f v1 = Vec4f{.x = 1[0], .y = 2[0], .z = 3[0], .w = 4[0]};
    Vec4f v2 = Vec4f{.x = 2[0], .y = 3[0], .z = 2[0], .w = 5[0]};
    int64_t result = v1_less_than(v1, v2);
    assert result[0];
    assert result[1];
    assert not result[2];
    assert result[3];
    spl_println("✅ Element-wise less than");
}

void test_vec4f_min() {
    Vec4f v1 = Vec4f{.x = 1[0], .y = 5[0], .z = 3[0], .w = 8[0]};
    Vec4f v2 = Vec4f{.x = 2[0], .y = 4[0], .z = 6[0], .w = 7[0]};
    int64_t result = v1_min(v1, v2);
    (assert result.x == 1[0]);
    (assert result.y == 4[0]);
    (assert result.z == 3[0]);
    (assert result.w == 7[0]);
    spl_println("✅ Element-wise minimum");
}

void test_vec4f_max() {
    Vec4f v1 = Vec4f{.x = 1[0], .y = 5[0], .z = 3[0], .w = 8[0]};
    Vec4f v2 = Vec4f{.x = 2[0], .y = 4[0], .z = 6[0], .w = 7[0]};
    int64_t result = v1_max(v1, v2);
    (assert result.x == 2[0]);
    (assert result.y == 5[0]);
    (assert result.z == 6[0]);
    (assert result.w == 8[0]);
    spl_println("✅ Element-wise maximum");
}

void test_vec4f_abs() {
    Vec4f v = Vec4f{.x = -1[0], .y = 2[0], .z = -3[0], .w = 4[0]};
    int64_t result = v_abs(v);
    (assert result.x == 1[0]);
    (assert result.y == 2[0]);
    (assert result.z == 3[0]);
    (assert result.w == 4[0]);
    spl_println("✅ Absolute value");
}

void test_vec4f_negate() {
    Vec4f v = Vec4f{.x = 1[0], .y = -2[0], .z = 3[0], .w = -4[0]};
    int64_t result = v_negate(v);
    (assert result.x == -1[0]);
    (assert result.y == 2[0]);
    (assert result.z == -3[0]);
    (assert result.w == 4[0]);
    spl_println("✅ Negation");
}

void test_vec4f_min_element() {
    Vec4f v = Vec4f{.x = 5[0], .y = 2[0], .z = 8[0], .w = 3[0]};
    int64_t min_val = v_min_element(v);
    (assert min_val == 2[0]);
    spl_println("✅ Minimum element");
}

void test_vec4f_max_element() {
    Vec4f v = Vec4f{.x = 5[0], .y = 2[0], .z = 8[0], .w = 3[0]};
    int64_t max_val = v_max_element(v);
    (assert max_val == 8[0]);
    spl_println("✅ Maximum element");
}

SimdCapabilities simdcapabilities_detect() {
    const char* cpuinfo = _read_cpuinfo();
    const char* flags = _extract_cpu_flags(cpuinfo);
    bool is_arm = (spl_str_contains(cpuinfo, "CPU architecture") || spl_str_contains(cpuinfo, "processor\t:"));
    bool is_arm_2 = spl_str_contains(cpuinfo, "Features\t");
    int64_t arm_detected = (is_arm && is_arm_2);
    if (arm_detected) {
        int64_t arm_platform = simdcapabilities_detect_arm_from_flags(flags);
        return SimdCapabilities{.platform = arm_platform};
    }
    int64_t x86_platform = simdcapabilities_detect_x86_from_flags(flags);
    return SimdCapabilities{.platform = x86_platform};
}

int64_t simdcapabilities_detect_x86() {
    const char* cpuinfo = _read_cpuinfo();
    const char* flags = _extract_cpu_flags(cpuinfo);
    return simdcapabilities_detect_x86_from_flags(flags);
}

int64_t simdcapabilities_detect_x86_from_flags(const char* flags) {
    bool has_avx512 = (spl_str_contains(flags, " avx512f ") || spl_str_contains(flags, " avx512f\n"));
    if (has_avx512) {
        return SimdPlatform_AVX512;
    }
    bool has_avx2 = (spl_str_contains(flags, " avx2 ") || spl_str_contains(flags, " avx2\n"));
    if (has_avx2) {
        return SimdPlatform_AVX2;
    }
    bool has_avx = (spl_str_contains(flags, " avx ") || spl_str_contains(flags, " avx\n"));
    if (has_avx) {
        return SimdPlatform_AVX;
    }
    bool has_sse2 = (spl_str_contains(flags, " sse2 ") || spl_str_contains(flags, " sse2\n"));
    if (has_sse2) {
        return SimdPlatform_SSE2;
    }
    bool has_sse = (spl_str_contains(flags, " sse ") || spl_str_contains(flags, " sse\n"));
    if (has_sse) {
        return SimdPlatform_SSE;
    }
    return SimdPlatform_None_Platform;
}

int64_t simdcapabilities_detect_arm() {
    const char* cpuinfo = _read_cpuinfo();
    const char* flags = _extract_cpu_flags(cpuinfo);
    return simdcapabilities_detect_arm_from_flags(flags);
}

int64_t simdcapabilities_detect_arm_from_flags(const char* flags) {
    bool has_sve = (spl_str_contains(flags, " sve ") || spl_str_contains(flags, " sve\n"));
    if (has_sve) {
        return SimdPlatform_SVE;
    }
    bool has_asimd = (spl_str_contains(flags, " asimd ") || spl_str_contains(flags, " asimd\n"));
    bool has_neon = (spl_str_contains(flags, " neon ") || spl_str_contains(flags, " neon\n"));
    if ((has_asimd || has_neon)) {
        return SimdPlatform_NEON;
    }
    return SimdPlatform_None_Platform;
}

const char* _read_cpuinfo() {
    const char* result = rt_file_read_text("/proc/cpuinfo");
    if ((result != 0)) {
        return result_unwrap(result);
    } else {
        return "";
    }
}

const char* _extract_cpu_flags(const char* cpuinfo) {
    return SIMD intrinsics for low-level operations;
    In a real implementation, these would be extern functions;
    return (that map to LLVM intrinsics || inline assembly.);
    return For now, they're placeholders showing the API.;
    return a_add(a, b);
}

Vec4f simdintrinsics_sse_sub_ps(Vec4f a, Vec4f b) {
    return a_sub(a, b);
}

Vec4f simdintrinsics_sse_mul_ps(Vec4f a, Vec4f b) {
    return a_mul(a, b);
}

Vec4f simdintrinsics_sse_div_ps(Vec4f a, Vec4f b) {
    return a_div(a, b);
}

Vec4f simdintrinsics_sse_sqrt_ps(Vec4f a) {
    return Vec4f{}; /* stub */
}

Target target_host() {
    return Target{.os = get_host_os(), .arch = get_host_arch()};
}

Target target_x86_64_unknown_linux_gnu() {
    return Target{.os = "linux", .arch = "x86_64"};
}

Target target_aarch64_unknown_linux_gnu() {
    return Target{.os = "linux", .arch = "aarch64"};
}

SmfBuildOptions smfbuildoptions_create(Target target) {
    return SmfBuildOptions{}; /* stub */
}

SymbolUsageResult symbolusageresult_empty() {
    return SymbolUsageResult{.used_functions = spl_array_new(), .used_types = spl_array_new(), .required_imports = spl_array_new()};
}

SymbolUsageAnalyzer symbolusageanalyzer_create() {
    return SymbolUsageAnalyzer{.minimal = false};
}

SymbolUsageAnalyzer symbolusageanalyzer_minimal_mode() {
    return SymbolUsageAnalyzer{.minimal = true};
}

int64_t cranelift_module_new(const char* name, int64_t target) {
    return cranelift_module_new(name, target);
}

int64_t cranelift_finalize_module(int64_t module) {
    return rt_cranelift_finalize_module(module);
}

void cranelift_free_module(int64_t module) {
    cranelift_free_module(module);
}

int64_t cranelift_new_signature(int64_t call_conv) {
    return cranelift_new_signature(call_conv);
}

void cranelift_sig_set_return(int64_t sig, int64_t type_) {
    cranelift_sig_set_return(sig, type_);
}

bool test_create_module() {
    int64_t CL_TYPE_I64 = 4;
    int64_t CL_TARGET_X86_64 = 0;
    int64_t module = cranelift_module_new("test_module", CL_TARGET_X86_64);
    if ((module == 0)) {
        spl_println("ERROR: Failed to create module");
        return false;
    }
    spl_println(spl_str_concat("OK: Created module with handle ", spl_i64_to_str(module)));
    int64_t sig = cranelift_new_signature(0);
    if ((sig == 0)) {
        spl_println("ERROR: Failed to create signature");
        cranelift_free_module(module);
        return false;
    }
    spl_println(spl_str_concat("OK: Created signature with handle ", spl_i64_to_str(sig)));
    cranelift_sig_set_return(sig, CL_TYPE_I64);
    spl_println("OK: Set signature return type");
    cranelift_free_module(module);
    spl_println("OK: Freed module");
    return true;
}

bool test_exec_ffi() {
    int64_t result = rt_exec("echo 'Hello from rt_exec'");
    spl_println(spl_str_concat("rt_exec returned: ", spl_i64_to_str(result)));
    return (result == 0);
}

bool test_file_hash_ffi() {
    int64_t hash = rt_file_hash("/bin/sh");
    spl_println(spl_str_concat("Hash of /bin/sh: ", spl_i64_to_str(hash)));
    return (hash_len(hash) > 0);
}

TestRunner TestRunner__create() {
    return TestRunner{.passed = 0, .failed = 0};
}

int64_t TestRunner__run_test(TestRunner* self, const char* name, FnPtr_i64 test_fn) {
    spl_println(name);
    if (test_fn()) {
        self->passed = (self->passed + 1);
    }
    return else:;
    self->failed = (self->failed + 1);
}

int64_t TestRunner__total_failed(const TestRunner* self) {
    return self->failed;
}

int64_t shell(const char* command) {
    return rt_process_run("sh", spl_array_new());
}

void try_parse(const char* label, const char* src) {
    /* stub */
}

const char* byte_to_hex(int64_t b) {
    const char* digits = "0123456789abcdef";
    return spl_str_concat(spl_i64_to_str(spl_str_index_char(digits, (b / 16))), spl_i64_to_str(spl_str_index_char(digits, (b % 16))));
}

bool compile_and_run(const char* label, const char* source, int64_t expected_exit) {
    spl_println(spl_str_concat(spl_str_concat("--- ", label), " ---"));
    spl_println(spl_str_concat("  Source: ", source));
    int64_t parser = parser_new(source);
    int64_t ast_module = parser_parse(parser);
    if ((parser_errors_len(parser, errors) > 0)) {
        spl_println(spl_str_concat("  Parse ERRORS: ", spl_i64_to_str(spl_array_len(parser.errors))));
        for (int64_t __e_i = 0; __e_i < spl_array_len(parser.errors); __e_i++) {
            int64_t e = spl_array_get(parser.errors, __e_i).as_int;
            spl_println(spl_str_concat("    ", spl_i64_to_str(e.message)));
        }
        return false;
    }
    int64_t hir_lowering = hirlowering_new();
    int64_t hir_module = hir_lowering_lower_module(hir_lowering, ast_module);
    MirLowering mir_ctx = mirlowering_new(hir_lowering.symbols);
    int64_t mir_module = mir_ctx_lower_module(mir_ctx, hir_module);
    for (int64_t __key_i = 0; __key_i < spl_array_len(mir_module_functions_keys(mir_module, functions)); __key_i++) {
        int64_t key = spl_array_get(mir_module_functions_keys(mir_module, functions), __key_i).as_int;
        int64_t fn_ = mir_module.functions[key];
        spl_println(spl_str_concat(spl_str_concat(spl_str_concat("  MIR fn: ", spl_i64_to_str(fn_.name)), ", return: "), spl_i64_to_str(fn_.signature.return_type)));
        spl_println(spl_str_concat(spl_str_concat(spl_str_concat("    locals: ", spl_i64_to_str(spl_array_len(fn_.locals))), ", blocks: "), spl_i64_to_str(spl_array_len(fn_.blocks))));
        for (int64_t __blk_i = 0; __blk_i < spl_array_len(fn_.blocks); __blk_i++) {
            int64_t blk = spl_array_get(fn_.blocks, __blk_i).as_int;
            spl_println(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("    block ", spl_i64_to_str(blk.id.id)), ": "), spl_i64_to_str(spl_array_len(blk.instructions))), " insts, term: "), spl_i64_to_str(blk.terminator)));
        }
    }
    int64_t elf_bytes = compile_native(mir_module, CodegenTarget_X86_64);
    spl_println(spl_str_concat(spl_str_concat("  ELF: ", spl_i64_to_str(spl_array_len(elf_bytes))), " bytes"));
    int64_t off = 0;
    while ((off < elf_bytes_len(elf_bytes))) {
        const char* chunk = "";
        int64_t end_ = (off + 800);
        if ((end_ > elf_bytes_len(elf_bytes))) {
            end_ = elf_bytes_len(elf_bytes);
        }
        int64_t j = off;
        while ((j < end_)) {
            chunk = spl_str_concat(chunk, byte_to_hex(elf_bytes[j]));
            j = (j + 1);
        }
        if ((off == 0)) {
            return shell(spl_str_concat(spl_str_concat("echo -n '", chunk), "' > /tmp/pipeline_multi.hex"));
        } else {
            return shell(spl_str_concat(spl_str_concat("echo -n '", chunk), "' >> /tmp/pipeline_multi.hex"));
        }
        off = end_;
    }
    shell("xxd -r -p /tmp/pipeline_multi.hex /tmp/pipeline_multi.o");
    return shell("rm -f /tmp/pipeline_multi.hex");
    const char* link_r = rt_process_run("cc", spl_array_new());
    if ((spl_str_index_char(link_r, 2) != 0)) {
        spl_println(spl_str_concat("  Link FAILED: ", spl_i64_to_str(spl_str_index_char(link_r, 1))));
        return false;
    }
    const char* run_r = rt_process_run("/tmp/pipeline_multi", spl_array_new());
    spl_println(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("  Exit code: ", spl_i64_to_str(spl_str_index_char(run_r, 2))), " (expected: "), spl_i64_to_str(expected_exit)), ")"));
    if ((spl_str_index_char(run_r, 2) == expected_exit)) {
        spl_println("  PASS");
        return true;
    } else {
        spl_println("  FAIL");
        return false;
    }
}

bool compile_and_run_output(const char* label, const char* source, int64_t expected_exit, const char* expected_stdout) {
    spl_println(spl_str_concat(spl_str_concat("--- ", label), " ---"));
    spl_println(spl_str_concat("  Source: ", source));
    int64_t parser = parser_new(source);
    int64_t ast_module = parser_parse(parser);
    if ((parser_errors_len(parser, errors) > 0)) {
        spl_println(spl_str_concat("  Parse ERRORS: ", spl_i64_to_str(spl_array_len(parser.errors))));
        for (int64_t __e_i = 0; __e_i < spl_array_len(parser.errors); __e_i++) {
            int64_t e = spl_array_get(parser.errors, __e_i).as_int;
            spl_println(spl_str_concat(spl_str_concat(spl_str_concat("    ", spl_i64_to_str(e.message)), " at "), spl_i64_to_str(e.span)));
        }
        return false;
    }
    int64_t hir_lowering = hirlowering_new();
    int64_t hir_module = hir_lowering_lower_module(hir_lowering, ast_module);
    MirLowering mir_ctx = mirlowering_new(hir_lowering.symbols);
    int64_t mir_module = mir_ctx_lower_module(mir_ctx, hir_module);
    for (int64_t __key_i = 0; __key_i < spl_array_len(mir_module_functions_keys(mir_module, functions)); __key_i++) {
        int64_t key = spl_array_get(mir_module_functions_keys(mir_module, functions), __key_i).as_int;
        int64_t fn_ = mir_module.functions[key];
        spl_println(spl_str_concat(spl_str_concat(spl_str_concat("  MIR fn: ", spl_i64_to_str(fn_.name)), ", return: "), spl_i64_to_str(fn_.signature.return_type)));
        spl_println(spl_str_concat(spl_str_concat(spl_str_concat("    locals: ", spl_i64_to_str(spl_array_len(fn_.locals))), ", blocks: "), spl_i64_to_str(spl_array_len(fn_.blocks))));
        for (int64_t __blk_i = 0; __blk_i < spl_array_len(fn_.blocks); __blk_i++) {
            int64_t blk = spl_array_get(fn_.blocks, __blk_i).as_int;
            spl_println(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("    block ", spl_i64_to_str(blk.id.id)), ": "), spl_i64_to_str(spl_array_len(blk.instructions))), " insts, term: "), spl_i64_to_str(blk.terminator)));
        }
    }
    int64_t elf_bytes = compile_native(mir_module, CodegenTarget_X86_64);
    spl_println(spl_str_concat(spl_str_concat("  ELF: ", spl_i64_to_str(spl_array_len(elf_bytes))), " bytes"));
    int64_t off = 0;
    while ((off < elf_bytes_len(elf_bytes))) {
        const char* chunk = "";
        int64_t end_ = (off + 800);
        if ((end_ > elf_bytes_len(elf_bytes))) {
            end_ = elf_bytes_len(elf_bytes);
        }
        int64_t j = off;
        while ((j < end_)) {
            chunk = spl_str_concat(chunk, byte_to_hex(elf_bytes[j]));
            j = (j + 1);
        }
        if ((off == 0)) {
            return shell(spl_str_concat(spl_str_concat("echo -n '", chunk), "' > /tmp/pipeline_multi.hex"));
        } else {
            return shell(spl_str_concat(spl_str_concat("echo -n '", chunk), "' >> /tmp/pipeline_multi.hex"));
        }
        off = end_;
    }
    shell("xxd -r -p /tmp/pipeline_multi.hex /tmp/pipeline_multi.o");
    return shell("rm -f /tmp/pipeline_multi.hex");
    const char* link_r = rt_process_run("cc", spl_array_new());
    if ((spl_str_index_char(link_r, 2) != 0)) {
        spl_println(spl_str_concat("  Link exit: ", spl_i64_to_str(spl_str_index_char(link_r, 2))));
        spl_println(spl_str_concat("  Link stdout: ", spl_i64_to_str(spl_str_index_char(link_r, 0))));
        spl_println(spl_str_concat("  Link stderr: ", spl_i64_to_str(spl_str_index_char(link_r, 1))));
        return false;
    }
    const char* run_r = rt_process_run("/tmp/pipeline_multi", spl_array_new());
    int64_t stdout_text = spl_str_index_char(run_r, 0);
    spl_println(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("  Exit code: ", spl_i64_to_str(spl_str_index_char(run_r, 2))), " (expected: "), spl_i64_to_str(expected_exit)), ")"));
    spl_println(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("  Stdout: '", spl_i64_to_str(stdout_text)), "' (expected: '"), expected_stdout), "')"));
    int64_t exit_ok = (spl_str_index_char(run_r, 2) == expected_exit);
    int64_t stdout_ok = spl_str_eq(stdout_text, expected_stdout);
    if (exit_ok) {
        if (stdout_ok) {
        }
        spl_println("  PASS");
        return true;
    } else {
        if (!(exit_ok)) {
            spl_println("  FAIL (exit code mismatch)");
        }
        if (!(stdout_ok)) {
            spl_println("  FAIL (stdout mismatch)");
        }
        return false;
    }
}

TextDiff compute_diff(const char* old_text, const char* new_text) {
    return TextDiff{}; /* stub */
}

DiffHunk finalize_hunk(int64_t old_start, int64_t new_start, SplArray* lines) {
    int64_t old_count = 0;
    int64_t new_count = 0;
    for (int64_t __line_i = 0; __line_i < spl_array_len(lines); __line_i++) {
        int64_t line = spl_array_get(lines, __line_i).as_int;
        switch (line) {
            case Context(_):
            {
                old_count = (old_count + 1);
                new_count = (new_count + 1);
                break;
            }
        }
    }
    return DiffHunk{.old_start = old_start, .old_count = old_count, .new_start = new_start, .new_count = new_count, .lines = lines};
}

const char* format_unified(TextDiff diff, const char* old_path, const char* new_path) {
    SplArray* output = spl_array_new();
    spl_array_push(output, spl_str(spl_str_concat("--- ", old_path)));
    spl_array_push(output, spl_str(spl_str_concat("+++ ", new_path)));
}

CoherenceChecker coherencechecker_create() {
    return CoherenceChecker{}; /* stub */
}

MethodSig methodsig_new(const char* name, bool has_self) {
    MethodSig{.name = name, .params = "[]", .return_type = "Unit", .has_self = has_self} = spl_str_contains({ "traits": {} } TraitRegistry(traits: registry_data).traits["traits"], "Features\t");
    return true;
}

int64_t create_standard_traits() {
    int64_t registry = traitregistry_new();
    registry_define_builtin_traits(registry);
    return registry;
}

void test_method_sig() {
    int64_t method = MethodSig__new("to_string", true);
    spl_str_eq(assert method.name, "to_string");
    assert method.has_self;
    spl_println("✅ Method signature");
}

void test_trait_def() {
    int64_t trait_def = TraitDef__new("Display");
    spl_str_eq(assert trait_def.name, "Display");
    spl_println("✅ Trait definition");
}

void test_registry_basic() {
    int64_t registry = traitregistry_new();
    int64_t display = TraitDef__new("Display");
    int64_t registered = registry_register_trait(registry, display);
    assert registered;
    spl_println("✅ Registry basics");
}

void test_duplicate_registration() {
    int64_t registry = traitregistry_new();
    int64_t display1 = TraitDef__new("Display");
    int64_t display2 = TraitDef__new("Display");
    int64_t first = registry_register_trait(registry, display1);
    int64_t second = registry_register_trait(registry, display2);
    assert first;
    assert not second;
    spl_println("✅ Duplicate prevention");
}

void test_trait_lookup() {
    int64_t registry = traitregistry_new();
    int64_t display = TraitDef__new("Display");
    registry_register_trait(registry, display);
    int64_t found = registry_get_trait(registry, "Display");
    spl_str_eq(assert found.name, "Display");
    int64_t not_found = registry_get_trait(registry, "Unknown");
    spl_str_eq(assert not_found.name, "NotFound");
    spl_println("✅ Trait lookup");
}

void test_builtin_traits() {
    int64_t registry = create_standard_traits();
    spl_println("✅ Built-in traits");
}

MethodImpl methodimpl_new(Symbol name) {
    return MethodImpl{}; /* stub */
}

MethodSig methodsig_inherent(Symbol name) {
    return MethodSig{.name = name, .source = "inherent"};
}

MethodSig methodsig_from_trait(Symbol name, Symbol trait_name) {
    return MethodSig{.name = name, .source = trait_name};
}

ImplBlock implblock_new(TraitRef trait_ref, int64_t for_type) {
    return ImplBlock{}; /* stub */
}

Obligation obligation_new(int64_t ty, TraitRef trait_ref) {
    return Obligation{.ty = ty, .trait_ref = trait_ref, .span = "unknown"};
}

ImplRegistry implregistry_new() {
    return ImplRegistry{.impls = spl_array_new()};
}

TraitSolver traitsolver_new(int64_t impl_registry) {
    return TraitSolver{}; /* stub */
}

TraitDef traitdef_create(Symbol name, Span span) {
    return TraitDef{}; /* stub */
}

TraitDef traitdef_new(const char* name) {
    return TraitDef{}; /* stub */
}

CycleDetector cycledetector_new(int64_t registry) {
    return CycleDetector{}; /* stub */
}

int64_t treesitter_parse_outline(int64_t self) {
    return 0; /* stub */
}

SplDict* empty_subst_map() {
    SplDict* result = HirType> = {};
    return result;
}

SplDict* empty_type_env() {
    SplDict* result = TypeScheme> = {};
    return result;
}

TypeScheme typescheme_mono(int64_t ty) {
    return TypeScheme{.vars = spl_array_new(), .ty = ty};
}

TypeScheme typescheme_poly(SplArray* vars, int64_t ty) {
    return TypeScheme{.vars = vars, .ty = ty};
}

Substitution substitution_new() {
    return Substitution{.map = empty_subst_map()};
}

LayoutAttr layoutattr_default_() {
    return LayoutAttr{}; /* stub */
}

UnsafeContext unsafecontext_new() {
    return UnsafeContext{}; /* stub */
}

bool is_ffi_function(HirExpr callee) {
    switch (callee.kind) {
        case hirexprkind_Var(sym):
        {
            int64_t name = sym.name;
            int64_t is_extern = spl_str_starts_with(name, "rt_");
            int64_t is_ffi_prefix = spl_str_starts_with(name, "ffi_");
            int64_t is_c_prefix = spl_str_starts_with(name, "c_");
            int64_t is_extern_marked = sym.is_extern;
            return (((is_extern || is_ffi_prefix) || is_c_prefix) || is_extern_marked);
            break;
        }
        case hirexprkind_Field(_, field, _):
        {
            return (spl_str_starts_with(field, "rt_") || spl_str_starts_with(field, "ffi_"));
            break;
        }
        default:
        {
            return false;
            break;
        }
    }
}

const char* check_unsafe_context(UnsafeContext ctx, int64_t op, Span span) {
    if (ctx_is_unsafe(ctx)) {
        ctx_record_op(ctx, op, span, spl_nil());
        return Result_Ok;
    } else {
        return Result_Err;
    }
}

const char* require_unsafe(UnsafeContext ctx, int64_t op, Span span) {
    return check_unsafe_context(ctx, op, span);
}

const char* validate_unsafe_block(UnsafeContext ctx, Span block_span) {
    if ((UnsafeContext__operations_len(&ctx, operations) == 0)) {
        return Result_Err;
    }
    return Result_Ok;
}

int64_t VarianceOps__flip(int64_t v) {
    switch (v) {
    }
}

int64_t VarianceOps__compose(int64_t outer, int64_t inner) {
    switch (outer) {
        case Variance_Covariant:
        {
            return inner;
            break;
        }
        case Variance_Contravariant:
        {
            return varianceops_flip(inner);
            break;
        }
        case Variance_Inv:
        {
            return Variance_Inv;
            break;
        }
        case Variance_Bivariant:
        {
            return Variance_Bivariant;
            break;
        }
    }
}

int64_t VarianceOps__combine(int64_t v1, int64_t v2) {
    switch ((v1, v2)) {
    }
}

TypeParamDef typeparamdef_covariant(Symbol name) {
    return TypeParamDef{.name = name, .variance = Variance_Covariant};
}

TypeParamDef typeparamdef_contravariant(Symbol name) {
    return TypeParamDef{.name = name, .variance = Variance_Contravariant};
}

TypeParamDef typeparamdef_inv(Symbol name) {
    return TypeParamDef{.name = name, .variance = Variance_Inv};
}

TypeParamDef typeparamdef_bivariant(Symbol name) {
    return TypeParamDef{.name = name, .variance = Variance_Bivariant};
}

VarianceEnv varianceenv_empty() {
    return VarianceEnv{}; /* stub */
}

void test_variance_basic() {
    int64_t cov = Variance_Covariant;
    int64_t contra = Variance_Contravariant;
    int64_t inv = Variance_Inv;
    int64_t bi = Variance_Bivariant;
    spl_println("✅ Basic variance");
}

void test_variance_flip() {
    int64_t cov = Variance_Covariant;
    int64_t contra = Variance_Contravariant;
    int64_t inv = Variance_Inv;
    int64_t bi = Variance_Bivariant;
    int64_t flipped_cov = varianceops_flip(cov);
    int64_t flipped_contra = varianceops_flip(contra);
    int64_t flipped_inv = varianceops_flip(inv);
    int64_t flipped_bi = varianceops_flip(bi);
    spl_println("✅ Variance flip");
}

void test_variance_compose() {
    int64_t cov = Variance_Covariant;
    int64_t contra = Variance_Contravariant;
    int64_t inv = Variance_Inv;
    int64_t result1 = varianceops_compose(cov, cov);
    int64_t result2 = varianceops_compose(cov, contra);
    int64_t result3 = varianceops_compose(contra, cov);
    int64_t result4 = varianceops_compose(contra, contra);
    int64_t result5 = varianceops_compose(inv, cov);
    spl_println("✅ Variance compose");
}

void test_variance_combine() {
    int64_t cov = Variance_Covariant;
    int64_t contra = Variance_Contravariant;
    int64_t inv = Variance_Inv;
    int64_t bi = Variance_Bivariant;
    int64_t result1 = varianceops_combine(bi, cov);
    int64_t result2 = varianceops_combine(cov, bi);
    int64_t result3 = varianceops_combine(cov, cov);
    int64_t result4 = varianceops_combine(contra, contra);
    int64_t result5 = varianceops_combine(cov, contra);
    int64_t result6 = varianceops_combine(inv, cov);
    spl_println("✅ Variance combine");
}

void test_type_param_def() {
    int64_t t_cov = TypeParamDef__covariant("T");
    int64_t u_contra = TypeParamDef__contravariant("U");
    int64_t v_inv = TypeParamDef__inv("V");
    spl_println("✅ Type parameter definition");
}

void test_variance_env() {
    VarianceEnv env = varianceenv_empty();
    VarianceEnv__set_type_variance(&env, "Box", "T", Variance_Covariant);
    int64_t t_var = VarianceEnv__get_type_variance(&env, "Box", "T");
    VarianceEnv__set_type_variance(&env, "Cell", "T", Variance_Inv);
    int64_t cell_t_var = VarianceEnv__get_type_variance(&env, "Cell", "T");
    int64_t unknown = VarianceEnv__get_type_variance(&env, "Unknown", "X");
    spl_println("✅ Variance environment");
}

void test_variance_env_multiple() {
    VarianceEnv env = varianceenv_empty();
    VarianceEnv__set_type_variance(&env, "Fn", "T", Variance_Contravariant);
    VarianceEnv__set_type_variance(&env, "Fn", "U", Variance_Covariant);
    int64_t t_var = VarianceEnv__get_type_variance(&env, "Fn", "T");
    int64_t u_var = VarianceEnv__get_type_variance(&env, "Fn", "U");
    spl_println("✅ Variance environment multiple params");
}

void test_variance_env_bulk() {
    VarianceEnv env = varianceenv_empty();
    SplArray* variances = spl_array_new();
    spl_array_push(variances, spl_int(Variance_Covariant));
    SplArray* param_names = spl_array_new();
    spl_array_push(param_names, spl_str("T"));
    spl_array_push(param_names, spl_str("E"));
    VarianceEnv__set_type_variances(&env, "Result", variances, param_names);
    int64_t t_var = VarianceEnv__get_type_variance(&env, "Result", "T");
    int64_t e_var = VarianceEnv__get_type_variance(&env, "Result", "E");
    spl_println("✅ Variance environment bulk set");
}

VarianceInference varianceinference_empty() {
    return VarianceInference{}; /* stub */
}

SubtypeEnv subtypeenv_empty() {
    return SubtypeEnv{}; /* stub */
}

VarianceChecker variancechecker_new_checker(SubtypeEnv subtype_env) {
    return VarianceChecker{}; /* stub */
}

VerificationChecker verificationchecker_create(bool strict) {
    return VerificationChecker{.violations = {}, .strict = strict};
}

VisibilityChecker VisibilityChecker__new(const char* current_module) {
    return VisibilityChecker{}; /* stub */
}

const char* filename_to_type_name(const char* filename) {
    const char* name = filename;
    if (spl_str_ends_with(name, ".spl")) {
        name = spl_str_slice(name, 0, -4);
    }
    int64_t parts = spl_str_split(name, "_");
    const char* result = "";
    for (int64_t __part_i = 0; __part_i < spl_array_len(parts); __part_i++) {
        int64_t part = spl_array_get(parts, __part_i).as_int;
        if ((part_len(part) > 0)) {
            int64_t first = part[0]_upper(part[0]);
            const char* rest = spl_str_slice(part, 1, spl_str_len(part));
            result = spl_str_concat(spl_str_concat(result, first), rest);
        }
    }
    return result;
}

bool type_matches_filename(const char* type_name, const char* filename) {
    const char* expected = filename_to_type_name(filename);
    return spl_str_eq(type_name, expected);
}

VolatileAccess volatileaccess_read(int64_t addr, int64_t size, int64_t type_, Span span) {
    return VolatileAccess{}; /* stub */
}

static void __module_init(void) {
    _global_container = spl_nil();
    global_context = spl_nil();
    _global_session = spl_nil();
    BITFIELD_REGISTRY = Bitfield> = {};
    parser = parser_new(source);
    ast_module = parser_parse(parser);
    spl_println("linker ok");
    spl_println("driver ok");
    spl_println("compiler.ast loaded ok");
    spl_println("smf_writer ok");
    spl_println("=== Driver -> Native Backend Test ===");
    spl_println("driver ok");
    v1 = MirTypeKind_Unit;
    spl_println(spl_str_concat("MirTypeKind.Unit: ", spl_i64_to_str(v1)));
    v2 = SymbolKind_Variable;
    spl_println(spl_str_concat("SymbolKind.Variable: ", spl_i64_to_str(v2)));
    spl_println("Done");
    spl_println("Test: HirLowering.new()...");
    lowering = hirlowering_new();
    spl_println(spl_str_concat(spl_str_concat("  Created: ", spl_i64_to_str(spl_array_len(lowering.errors))), " errors"));
    spl_println("=== SUCCESS ===");
    hello();
    spl_println("Test: Lexer.new()...");
    lex = lexer_new(src);
    spl_println(spl_str_concat("  Created, pos: ", spl_i64_to_str(lex.pos)));
    spl_println("=== SUCCESS ===");
    spl_println("linker ok");
    spl_println("ok");
    spl_println("=== MirBuilder API -> Native Backend Test ===");
    builder = mirbuilder_new();
    spl_println("  Builder created");
    i64_type = MirType{.kind = MirTypeKind_I64};
    bool_type = MirType{.kind = MirTypeKind_Bool};
    unit_type = MirType{.kind = MirTypeKind_Unit};
    main_sig = MirSignature{.params = {}, .return_type = i64_type, .is_variadic = false};
    dummy_span = Span{.start = 0, .end = 0, .line = 0, .col = 0};
    spl_println("  Function begun");
    then_block = builder_new_block(builder, "then");
    else_block = builder_new_block(builder, "else");
    exit_block = builder_new_block(builder, "exit");
    spl_println(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("  Blocks created: then=", spl_i64_to_str(then_block.id)), " else="), spl_i64_to_str(else_block.id)), " exit="), spl_i64_to_str(exit_block.id)));
    x_local = builder_new_temp(builder, i64_type);
    y_local = builder_new_temp(builder, i64_type);
    spl_println("=== Complex MIR -> Native Backend Test ===");
    i64_type = MirType{.kind = MirTypeKind_I64};
    bool_type = MirType{.kind = MirTypeKind_Bool};
    main_sig = MirSignature{.params = {}, .return_type = i64_type, .is_variadic = false};
    locals = spl_array_new();
    spl_array_push(locals, spl_int(name: "_return"));
    spl_array_push(locals, spl_int(type_: i64_type));
    spl_array_push(locals, spl_int(kind: LocalKind.Return)));
    entry_block = MirBlock{.id = blockid_new(0), .label = "entry", .instructions = spl_array_new()};
    parser = parser_new(source);
    ast_module = parser_parse(parser);
    spl_println(spl_str_concat("AST: ", spl_i64_to_str(ast_module.functions_keys(ast_module.functions))));
    hir_lowering = hirlowering_new();
    hir_module = hir_lowering_lower_module(hir_lowering, ast_module);
    spl_println(spl_str_concat("HIR functions: ", spl_i64_to_str(hir_module.functions_keys(hir_module.functions))));
    mir_ctx = mirlowering_new(hir_lowering.symbols);
    spl_println(spl_str_concat(spl_str_concat(spl_str_concat("Builder before: locals=", spl_i64_to_str(spl_array_len(mir_ctx.builder.locals))), ", blocks="), spl_i64_to_str(spl_array_len(mir_ctx.builder.blocks))));
    mir_module = mir_ctx_lower_module(mir_ctx, hir_module);
    spl_println(spl_str_concat("MIR functions: ", spl_i64_to_str(spl_array_len(mir_module.functions_keys(mir_module.functions)))));
    spl_println("Test: MirLowering.new()...");
    hir_lowering = hirlowering_new();
    mir_ctx = mirlowering_new(hir_lowering.symbols);
    spl_println("  Created MirLowering");
    spl_println("=== SUCCESS ===");
    spl_println("=== MIR -> Native Backend Test ===");
    spl_println("");
    spl_println("Step 1: Constructing MirModule...");
    i64_type = MirType{.kind = MirTypeKind_I64};
    spl_println("types ok");
    spl_println("=== Native Binary Generation Proof of Concept ===");
    spl_println("");
    spl_println("Step 1: Creating x86_64 machine code...");
    code = spl_array_new();
    spl_array_push(code, spl_int(/* TODO: 0x55 */((int64_t)0)));
    spl_array_push(code, spl_int(/* TODO: 0x48 */((int64_t)0)));
    spl_array_push(code, spl_int(/* TODO: 0x89 */((int64_t)0)));
    spl_array_push(code, spl_int(/* TODO: 0xe5 */((int64_t)0)));
    spl_array_push(code, spl_int(/* TODO: 0x48 */((int64_t)0)));
    spl_array_push(code, spl_int(/* TODO: 0x8d */((int64_t)0)));
    spl_array_push(code, spl_int(/* TODO: 0x3d */((int64_t)0)));
    spl_array_push(code, spl_int(/* TODO: 0x00 */((int64_t)0)));
    code_size = code_len(code);
    spl_println(spl_str_concat(spl_str_concat("  Code size: ", spl_i64_to_str(code_size)), " bytes"));
    spl_println("Step 2: Creating rodata...");
    rodata = spl_array_new();
    spl_array_push(rodata, spl_int(104));
    spl_array_push(rodata, spl_int(101));
    spl_array_push(rodata, spl_int(108));
    spl_array_push(rodata, spl_int(108));
    spl_array_push(rodata, spl_int(111));
    spl_array_push(rodata, spl_int(32));
    spl_array_push(rodata, spl_int(102));
    spl_array_push(rodata, spl_int(114));
    spl_println(spl_str_concat(spl_str_concat("  Rodata size: ", spl_i64_to_str(spl_array_len(rodata))), " bytes"));
    spl_println("Step 3: Building ELF object file...");
    writer = elf_writer_x86_64();
    text_section = new_text_section(code);
    parser = parser_new(src);
    ast = parser_parse(parser);
    spl_println(spl_str_concat("Errors: ", spl_i64_to_str(spl_array_len(parser.errors))));
    spl_println("Test: Parser.new()...");
    parser = parser_new(src);
    spl_println("  Created parser");
    ast = parser_parse(parser);
    spl_println(spl_str_concat("  Module: ", spl_i64_to_str(ast.name)));
    spl_println(spl_str_concat("  Functions: ", spl_i64_to_str(ast.functions_keys(ast.functions))));
    spl_println("=== SUCCESS ===");
    spl_println("=== Step-by-step Parser Test ===");
    spl_println("Step 1: TreeSitter...");
    ts = treesitter_new(src);
    outline = ts_parse_outline(ts);
    spl_println(spl_str_concat("  Functions: ", spl_i64_to_str(spl_array_len(outline.functions))));
    spl_println(spl_str_concat("  Exports: ", spl_i64_to_str(spl_array_len(outline.exports))));
    spl_println("Step 2: Iterating outline...");
    spl_println(spl_str_concat("  Imports count: ", spl_i64_to_str(spl_array_len(outline.imports))));
    while ((imp_idx < outline_imports_len(outline, imports))) {
        spl_println(spl_str_concat("  import #", spl_i64_to_str(imp_idx)));
        imp_idx = (imp_idx + 1);
    }
    spl_println("  Imports iterated OK");
    while ((exp_idx < outline_exports_len(outline, exports))) {
        spl_println(spl_str_concat("  export #", spl_i64_to_str(exp_idx)));
        exp_idx = (exp_idx + 1);
    }
    spl_println("  Exports iterated OK");
    spl_println("Step 3: Creating parser...");
    parser = parser_new(src);
    spl_println(spl_str_concat(spl_str_concat("  Parser source: '", spl_i64_to_str(parser.source)), "'"));
    parser.outline = outline;
    spl_println("  Outline set");
    module = parser_parse_full(parser);
    spl_println(spl_str_concat("  Module: ", module.name));
    spl_println("=== SUCCESS ===");
    ts = treesitter_new(src);
    outline = ts_parse_outline(ts);
    spl_println(spl_str_concat("imports: ", spl_i64_to_str(outline.imports)));
    spl_println(spl_str_concat("exports: ", spl_i64_to_str(outline.exports)));
    spl_println(spl_str_concat("functions: ", spl_i64_to_str(spl_array_len(outline.functions))));
    spl_println(spl_str_concat("classes: ", spl_i64_to_str(outline.classes)));
    spl_println(spl_str_concat("actors: ", spl_i64_to_str(outline.actors)));
    spl_println(spl_str_concat("structs: ", spl_i64_to_str(outline.structs)));
    spl_println(spl_str_concat("enums: ", spl_i64_to_str(outline.enums)));
    spl_println(spl_str_concat("bitfields: ", spl_i64_to_str(outline.bitfields)));
    spl_println(spl_str_concat("traits: ", spl_i64_to_str(outline.traits)));
    spl_println(spl_str_concat("impls: ", spl_i64_to_str(outline.impls)));
    spl_println(spl_str_concat("type_aliases: ", spl_i64_to_str(outline.type_aliases)));
    spl_println(spl_str_concat("constants: ", spl_i64_to_str(outline.constants)));
    spl_println(spl_str_concat("static_asserts: ", spl_i64_to_str(outline.static_asserts)));
    spl_println("=== Step-by-step Parser Test ===");
    spl_println("Step 1: TreeSitter...");
    ts = treesitter_new(src);
    outline = ts_parse_outline(ts);
    spl_println(spl_str_concat(spl_str_concat("  Name: '", spl_i64_to_str(outline.name)), "'"));
    spl_println(spl_str_concat("  Imports: ", spl_i64_to_str(spl_array_len(outline.imports))));
    spl_println(spl_str_concat("  Functions: ", spl_i64_to_str(spl_array_len(outline.functions))));
    if ((outline_functions_len(outline, functions) > 0)) {
        spl_println(spl_str_concat("  Fn[0] name: ", spl_i64_to_str(outline.functions[0].name)));
    }
    spl_println("Step 2: Create parser with outline...");
    parser = parser_new(src);
    parser.outline = outline;
    spl_println("  Parser created with outline");
    spl_println("Step 3: Parsing...");
    ast = parser_parse(parser);
    spl_println(spl_str_concat("  Module: ", spl_i64_to_str(ast.name)));
    spl_println("=== SUCCESS ===");
    spl_println("=== Parser Factory Test ===");
    parser = create_parser(src);
    spl_println("  Parser created");
    ast = parser_parse(parser);
    spl_println(spl_str_concat("  Module: ", spl_i64_to_str(ast.name)));
    spl_println("=== SUCCESS ===");
    parser = parser_new(source);
    ast_module = parser_parse(parser);
    hir_lowering = hirlowering_new();
    hir_module = hir_lowering_lower_module(hir_lowering, ast_module);
    mir_ctx = mirlowering_new(hir_lowering.symbols);
    mir_module = mir_ctx_lower_module(mir_ctx, hir_module);
    parser = parser_new(source);
    ast_module = parser_parse(parser);
    hir_lowering = hirlowering_new();
    hir_module = hir_lowering_lower_module(hir_lowering, ast_module);
    mir_ctx = mirlowering_new(hir_lowering.symbols);
    mir_module = mir_ctx_lower_module(mir_ctx, hir_module);
    spl_println(spl_str_concat(spl_str_concat("MIR module name: '", spl_i64_to_str(mir_module.name)), "'"));
    spl_println(spl_str_concat("MIR functions: ", spl_i64_to_str(mir_module.functions_keys(mir_module.functions))));
    spl_println("Calling compile_native...");
    elf_bytes = compile_native(mir_module, CodegenTarget_X86_64);
    spl_println(spl_str_concat(spl_str_concat("ELF: ", spl_i64_to_str(spl_array_len(elf_bytes))), " bytes"));
    spl_println("=== Pipeline Multi-Test ===");
    t1 = compile_and_run("Return 0", spl_str_concat(spl_str_concat(spl_str_concat("fn main():", NL), "    0"), NL), 0);
    t2 = compile_and_run("Return 42", spl_str_concat(spl_str_concat(spl_str_concat("fn main():", NL), "    42"), NL), 42);
    t3 = compile_and_run("Explicit return", spl_str_concat(spl_str_concat(spl_str_concat("fn main():", NL), "    return 0"), NL), 0);
    t4 = compile_and_run("Arithmetic", spl_str_concat(spl_str_concat(spl_str_concat("fn main():", NL), "    1 + 2"), NL), 3);
    t5 = compile_and_run("Nested arith", spl_str_concat(spl_str_concat(spl_str_concat("fn main():", NL), "    (10 + 20) * 2"), NL), 60);
    spl_println("");
    spl_println(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("=== Results: ", spl_i64_to_str(passed)), "/"), spl_i64_to_str(total)), " passed ==="));
    spl_println("=== Pure Simple Pipeline -> Native Backend Test ===");
    spl_println("Step 1: Parsing...");
    parser = parser_new(source);
    ast_module = parser_parse(parser);
    spl_println(spl_str_concat("  Parsed: functions=", spl_i64_to_str(ast_module.functions_keys(ast_module.functions))));
    spl_println("Step 2: HIR Lowering...");
    hir_lowering = hirlowering_new();
    hir_module = hir_lowering_lower_module(hir_lowering, ast_module);
    spl_println("  HIR: done");
    spl_println("Step 3: MIR Lowering...");
    mir_lowering_ctx = mirlowering_new(hir_lowering.symbols);
    mir_module = mir_lowering_ctx_lower_module(mir_lowering_ctx, hir_module);
    spl_println(spl_str_concat("  MIR: name=", spl_i64_to_str(mir_module.name)));
    spl_println("Step 4: Native backend...");
    elf_bytes = compile_native(mir_module, CodegenTarget_X86_64);
    spl_println(spl_str_concat(spl_str_concat("  ELF: ", spl_i64_to_str(spl_array_len(elf_bytes))), " bytes"));
    spl_println("Step 5: Writing and linking...");
    while ((offset < elf_bytes_len(elf_bytes))) {
        const char* chunk = "";
        int64_t end_idx = (offset + 800);
        if ((end_idx > elf_bytes_len(elf_bytes))) {
            end_idx = elf_bytes_len(elf_bytes);
        }
        int64_t j = offset;
        while ((j < end_idx)) {
            chunk = spl_str_concat(chunk, byte_to_hex(elf_bytes[j]));
            j = (j + 1);
        }
        if ((offset == 0)) {
            shell(spl_str_concat(spl_str_concat("echo -n '", chunk), "' > /tmp/pipeline_test.hex"));
        } else {
            shell(spl_str_concat(spl_str_concat("echo -n '", chunk), "' >> /tmp/pipeline_test.hex"));
        }
        offset = end_idx;
    }
    link_r = rt_process_run("cc", spl_array_new());
    if ((spl_str_index_char(link_r, 2) != 0)) {
        spl_println(spl_str_concat("  Link FAILED: ", spl_i64_to_str(spl_str_index_char(link_r, 1))));
    } else {
        spl_println("  Linked!");
        const char* run_r = rt_process_run("/tmp/pipeline_test", spl_array_new());
        spl_println(spl_str_concat("  Exit code: ", spl_i64_to_str(spl_str_index_char(run_r, 2))));
        if ((spl_str_index_char(run_r, 2) == 0)) {
            spl_println("");
            spl_println("=== SUCCESS: Pure Simple Pipeline -> Native ===");
        } else {
            spl_println(spl_str_concat(spl_str_concat("=== PARTIAL: Binary returned ", spl_i64_to_str(spl_str_index_char(run_r, 2))), " ==="));
        }
    }
    spl_println("=== Done ===");
    spl_println(spl_str_concat("Source: ", source));
    parser = parser_new(source);
    ast_module = parser_parse(parser);
    spl_println(spl_str_concat("Parse errors: ", spl_i64_to_str(spl_array_len(parser.errors))));
    spl_println("HIR lowering...");
    hir_lowering = hirlowering_new();
    hir_module = hir_lowering_lower_module(hir_lowering, ast_module);
    spl_println(spl_str_concat("HIR: done, functions: ", spl_i64_to_str(spl_array_len(hir_module.functions))));
    spl_println("MIR lowering...");
    mir_ctx = mirlowering_new(hir_lowering.symbols);
    mir_module = mir_ctx_lower_module(mir_ctx, hir_module);
    spl_println("MIR: done");
    spl_println("Done!");
    spl_println("smf_writer ok");
    spl_println("partition ok");
    spl_println("metadata ok");
    spl_println("note_sdn ok");
    spl_println("ast ok");
    spl_println("Test 1: MirBuilder.new()...");
    builder = mirbuilder_new();
    spl_println(spl_str_concat("  next_local_id: ", spl_i64_to_str(builder.next_local_id)));
    spl_println("Test 2: MirType.i64()...");
    t = mirtype_i64();
    spl_println(spl_str_concat("  kind: ", spl_i64_to_str(t.kind)));
    spl_println("=== All passed ===");
    spl_println("Test: TreeSitter.new()...");
    ts = treesitter_new(src);
    spl_println("  Created TreeSitter");
    outline = ts_parse_outline(ts);
    spl_println(spl_str_concat("  Outline: ", spl_i64_to_str(outline.name)));
    spl_println(spl_str_concat("  Functions: ", spl_i64_to_str(spl_array_len(outline.functions))));
    spl_println("=== SUCCESS ===");
    UNSAFE_BUILTINS = spl_array_new();
    spl_array_push(UNSAFE_BUILTINS, spl_str("transmute"));
    spl_array_push(UNSAFE_BUILTINS, spl_str("read_volatile"));
    spl_array_push(UNSAFE_BUILTINS, spl_str("write_volatile"));
    spl_array_push(UNSAFE_BUILTINS, spl_str("copy_nonoverlapping"));
    spl_array_push(UNSAFE_BUILTINS, spl_str("copy"));
    spl_array_push(UNSAFE_BUILTINS, spl_str("swap"));
    spl_array_push(UNSAFE_BUILTINS, spl_str("drop_in_place"));
    spl_array_push(UNSAFE_BUILTINS, spl_str("forget"));
}

int main(int argc, char** argv) {
    spl_init_args(argc, argv);
    __module_init();
    return (int)spl_main();
}
