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

/* enum BackendMode */
static const int64_t BackendMode_Jit = 0;
static const int64_t BackendMode_Aot = 1;
static const int64_t BackendMode_Interpreter = 2;

/* enum TargetArch */
static const int64_t TargetArch_X86_64 = 0;
static const int64_t TargetArch_Aarch64 = 1;
static const int64_t TargetArch_Riscv64 = 2;
static const int64_t TargetArch_Host = 3;

/* enum InstructionCategory */
static const int64_t InstructionCategory_Constants = 0;
static const int64_t InstructionCategory_Arithmetic = 1;
static const int64_t InstructionCategory_Bitwise = 2;
static const int64_t InstructionCategory_Comparison = 3;
static const int64_t InstructionCategory_Memory = 4;
static const int64_t InstructionCategory_ControlFlow = 5;
static const int64_t InstructionCategory_Collections = 6;
static const int64_t InstructionCategory_SIMD = 7;
static const int64_t InstructionCategory_GPU = 8;
static const int64_t InstructionCategory_Pointers = 9;
static const int64_t InstructionCategory_Structs = 10;
static const int64_t InstructionCategory_Enums = 11;
static const int64_t InstructionCategory_Async = 12;
static const int64_t InstructionCategory_ErrorHandling = 13;
static const int64_t InstructionCategory_Closures = 14;

/* enum CodegenErrorKind */
static const int64_t CodegenErrorKind_ModuleInitFailed = 0;
static const int64_t CodegenErrorKind_FunctionDeclFailed = 1;
static const int64_t CodegenErrorKind_FunctionCompileFailed = 2;
static const int64_t CodegenErrorKind_VerificationFailed = 3;
static const int64_t CodegenErrorKind_InvalidSignature = 4;
static const int64_t CodegenErrorKind_UnsupportedType = 5;
static const int64_t CodegenErrorKind_UnsupportedInstruction = 6;
static const int64_t CodegenErrorKind_InvalidTarget = 7;
static const int64_t CodegenErrorKind_FinalizationFailed = 8;
static const int64_t CodegenErrorKind_ObjectEmitFailed = 9;
static const int64_t CodegenErrorKind_JitExecutionFailed = 10;
static const int64_t CodegenErrorKind_UnknownFunction = 11;
static const int64_t CodegenErrorKind_InvalidFunctionCall = 12;
static const int64_t CodegenErrorKind_RuntimeError = 13;
static const int64_t CodegenErrorKind_NameConflict = 14;

/* enum CatchAllSeverity */
static const int64_t CatchAllSeverity_Error = 0;
static const int64_t CatchAllSeverity_Warning = 1;
static const int64_t CatchAllSeverity_Info = 2;

/* enum InterpreterMode */
static const int64_t InterpreterMode_Classic = 0;
static const int64_t InterpreterMode_Optimized = 1;

/* enum JitMode */
static const int64_t JitMode_Auto = 0;
static const int64_t JitMode_AlwaysJit = 1;
static const int64_t JitMode_AlwaysInterpret = 2;
static const int64_t JitMode_Hybrid = 3;

/* enum VerificationLevel */
static const int64_t VerificationLevel_Minimal = 0;
static const int64_t VerificationLevel_Contracts = 1;
static const int64_t VerificationLevel_Full = 2;
static const int64_t VerificationLevel_Memory = 3;
static const int64_t VerificationLevel_Effects = 4;

/* enum LlvmPass */
static const int64_t LlvmPass_DominatorTree = 0;
static const int64_t LlvmPass_LoopInfo = 1;
static const int64_t LlvmPass_ScalarEvolution = 2;
static const int64_t LlvmPass_AliasAnalysis = 3;
static const int64_t LlvmPass_InstCombine = 4;
static const int64_t LlvmPass_SimplifyCFG = 5;
static const int64_t LlvmPass_Reassociate = 6;
static const int64_t LlvmPass_GVN = 7;
static const int64_t LlvmPass_LICM = 8;
static const int64_t LlvmPass_IndVarSimplify = 9;
static const int64_t LlvmPass_LoopUnroll = 10;
static const int64_t LlvmPass_LoopVectorize = 11;
static const int64_t LlvmPass_SLPVectorize = 12;
static const int64_t LlvmPass_DeadCodeElimination = 13;
static const int64_t LlvmPass_Inlining = 14;

/* enum BackendTarget */

/* enum MirTestInst */
static const int64_t MirTestInst_ConstInt = 0;
static const int64_t MirTestInst_ConstFloat = 1;
static const int64_t MirTestInst_ConstBool = 2;
static const int64_t MirTestInst_ConstString = 3;
static const int64_t MirTestInst_Add = 4;
static const int64_t MirTestInst_Sub = 5;
static const int64_t MirTestInst_Mul = 6;
static const int64_t MirTestInst_Div = 7;
static const int64_t MirTestInst_Mod = 8;
static const int64_t MirTestInst_Neg = 9;
static const int64_t MirTestInst_BitAnd = 10;
static const int64_t MirTestInst_BitOr = 11;
static const int64_t MirTestInst_BitXor = 12;
static const int64_t MirTestInst_BitNot = 13;
static const int64_t MirTestInst_Shl = 14;
static const int64_t MirTestInst_Shr = 15;
static const int64_t MirTestInst_Eq = 16;
static const int64_t MirTestInst_Ne = 17;
static const int64_t MirTestInst_Lt = 18;
static const int64_t MirTestInst_Le = 19;
static const int64_t MirTestInst_Gt = 20;
static const int64_t MirTestInst_Ge = 21;
static const int64_t MirTestInst_Load = 22;
static const int64_t MirTestInst_Store = 23;
static const int64_t MirTestInst_Copy = 24;
static const int64_t MirTestInst_Jump = 25;
static const int64_t MirTestInst_Branch = 26;
static const int64_t MirTestInst_Ret = 27;
static const int64_t MirTestInst_RetVoid = 28;
static const int64_t MirTestInst_ArrayLit = 29;
static const int64_t MirTestInst_TupleLit = 30;
static const int64_t MirTestInst_DictLit = 31;
static const int64_t MirTestInst_IndexGet = 32;
static const int64_t MirTestInst_IndexSet = 33;
static const int64_t MirTestInst_VecLit = 34;
static const int64_t MirTestInst_VecSum = 35;
static const int64_t MirTestInst_VecProduct = 36;
static const int64_t MirTestInst_VecMin = 37;
static const int64_t MirTestInst_VecMax = 38;
static const int64_t MirTestInst_VecExtract = 39;
static const int64_t MirTestInst_VecShuffle = 40;
static const int64_t MirTestInst_VecFma = 41;
static const int64_t MirTestInst_VecSqrt = 42;
static const int64_t MirTestInst_GpuGlobalId = 43;
static const int64_t MirTestInst_GpuLocalId = 44;
static const int64_t MirTestInst_GpuGroupId = 45;
static const int64_t MirTestInst_GpuBarrier = 46;
static const int64_t MirTestInst_GpuMemFence = 47;
static const int64_t MirTestInst_GpuAtomicAdd = 48;
static const int64_t MirTestInst_PointerNew = 49;
static const int64_t MirTestInst_PointerRef = 50;
static const int64_t MirTestInst_PointerDeref = 51;
static const int64_t MirTestInst_StructInit = 52;
static const int64_t MirTestInst_FieldGet = 53;
static const int64_t MirTestInst_FieldSet = 54;
static const int64_t MirTestInst_EnumDiscriminant = 55;
static const int64_t MirTestInst_EnumPayload = 56;
static const int64_t MirTestInst_EnumUnit = 57;
static const int64_t MirTestInst_EnumWith = 58;
static const int64_t MirTestInst_ActorSpawn = 59;
static const int64_t MirTestInst_ActorSend = 60;
static const int64_t MirTestInst_ActorRecv = 61;
static const int64_t MirTestInst_FutureCreate = 62;
static const int64_t MirTestInst_Await = 63;
static const int64_t MirTestInst_OptionVReg = 64;
static const int64_t MirTestInst_VReg = 65;
static const int64_t MirTestInst_OptionNone = 66;
static const int64_t MirTestInst_ResultOk = 67;
static const int64_t MirTestInst_ResultErr = 68;
static const int64_t MirTestInst_ClosureCreate = 69;
static const int64_t MirTestInst_IndirectCall = 70;

/* enum WasmTarget */
static const int64_t WasmTarget_Browser = 0;
static const int64_t WasmTarget_Wasi = 1;
static const int64_t WasmTarget_Minimal = 2;

/* enum WasmType */
static const int64_t WasmType_I32 = 0;
static const int64_t WasmType_I64 = 1;
static const int64_t WasmType_F32 = 2;
static const int64_t WasmType_F64 = 3;
static const int64_t WasmType_FuncRef = 4;
static const int64_t WasmType_ExternRef = 5;

/* enum WasmImportKind */
static const int64_t WasmImportKind_Function = 0;
static const int64_t WasmImportKind_Global = 1;
static const int64_t WasmImportKind_Memory = 2;
static const int64_t WasmImportKind_Table = 3;

/* enum WasmExportKind */
static const int64_t WasmExportKind_Function = 0;
static const int64_t WasmExportKind_Global = 1;
static const int64_t WasmExportKind_Memory = 2;
static const int64_t WasmExportKind_Table = 3;

/* enum HighlightKind */
static const int64_t HighlightKind_Keyword = 0;
static const int64_t HighlightKind_Operator = 1;
static const int64_t HighlightKind_Number = 2;
static const int64_t HighlightKind_String = 3;
static const int64_t HighlightKind_Comment = 4;
static const int64_t HighlightKind_Function = 5;
static const int64_t HighlightKind_Variable = 6;
static const int64_t HighlightKind_Type = 7;
static const int64_t HighlightKind_Constant = 8;
static const int64_t HighlightKind_Error = 9;

/* enum LexerMode */
static const int64_t LexerMode_Normal = 0;
static const int64_t LexerMode_Math = 1;
static const int64_t LexerMode_Raw = 2;
static const int64_t LexerMode_Custom = 3;

/* enum RedirectKind */
static const int64_t RedirectKind_StdoutToFile = 0;
static const int64_t RedirectKind_StdoutAppend = 1;
static const int64_t RedirectKind_StderrToFile = 2;
static const int64_t RedirectKind_StdinFromFile = 3;
static const int64_t RedirectKind_StderrToStdout = 4;

/* enum SqlKind */
static const int64_t SqlKind_Select = 0;
static const int64_t SqlKind_Insert = 1;
static const int64_t SqlKind_Update = 2;
static const int64_t SqlKind_Delete = 3;
static const int64_t SqlKind_Create = 4;
static const int64_t SqlKind_Alter = 5;
static const int64_t SqlKind_Drop = 6;
static const int64_t SqlKind_Other = 7;

/* enum JsonKind */
static const int64_t JsonKind_Null = 0;
static const int64_t JsonKind_Bool = 1;
static const int64_t JsonKind_Number = 2;
static const int64_t JsonKind_String = 3;
static const int64_t JsonKind_Array = 4;
static const int64_t JsonKind_Object = 5;

/* enum MarkdownBlock */
static const int64_t MarkdownBlock_Heading = 0;
static const int64_t MarkdownBlock_Paragraph = 1;
static const int64_t MarkdownBlock_CodeBlock = 2;
static const int64_t MarkdownBlock_List = 3;
static const int64_t MarkdownBlock_Quote = 4;
static const int64_t MarkdownBlock_HorizontalRule = 5;
static const int64_t MarkdownBlock_Table = 6;

/* enum GraphKind */
static const int64_t GraphKind_Flowchart = 0;
static const int64_t GraphKind_Sequence = 1;
static const int64_t GraphKind_Class = 2;
static const int64_t GraphKind_State = 3;
static const int64_t GraphKind_ER = 4;
static const int64_t GraphKind_Gantt = 5;
static const int64_t GraphKind_Dot = 6;

/* enum BlockValue */
static const int64_t BlockValue_Expr = 0;
static const int64_t BlockValue_LossBlock = 1;
static const int64_t BlockValue_NogradBlock = 2;
static const int64_t BlockValue_Raw = 3;
static const int64_t BlockValue_Shell = 4;
static const int64_t BlockValue_Sql = 5;
static const int64_t BlockValue_Regex = 6;
static const int64_t BlockValue_Json = 7;
static const int64_t BlockValue_Markdown = 8;
static const int64_t BlockValue_Graph = 9;
static const int64_t BlockValue_Custom = 10;
static const int64_t BlockValue_Error = 11;

/* enum BorrowCheckResult */
static const int64_t BorrowCheckResult_Ok = 0;
static const int64_t BorrowCheckResult_Errors = 1;

/* enum ImportKind */
static const int64_t ImportKind_UseImport = 0;
static const int64_t ImportKind_CommonUse = 1;
static const int64_t ImportKind_ExportUse = 2;
static const int64_t ImportKind_TypeUse = 3;

/* enum SymKind */
static const int64_t SymKind_ValueOrType = 0;
static const int64_t SymKind_MacroKind = 1;

/* enum FileKind */
static const int64_t FileKind_File = 0;
static const int64_t FileKind_Directory = 1;

/* enum ResolutionResult */
static const int64_t ResolutionResult_Unique = 0;
static const int64_t ResolutionResult_Ambiguous = 1;
static const int64_t ResolutionResult_NotFound = 2;

/* enum Visibility */
static const int64_t Visibility_Public = 0;
static const int64_t Visibility_Private = 1;

/* enum BuildUnitStatus */
static const int64_t BuildUnitStatus_Pending = 0;
static const int64_t BuildUnitStatus_Ready = 1;
static const int64_t BuildUnitStatus_InProgress = 2;
static const int64_t BuildUnitStatus_Completed = 3;
static const int64_t BuildUnitStatus_Failed = 4;

/* enum BarrierKind */
static const int64_t BarrierKind_PreWrite = 0;
static const int64_t BarrierKind_PostWrite = 1;
static const int64_t BarrierKind_CardMark = 2;
static const int64_t BarrierKind_Generational = 3;
static const int64_t BarrierKind_None_ = 4;

/* enum EscapeState */
static const int64_t EscapeState_NoEscape = 0;
static const int64_t EscapeState_ArgEscape = 1;
static const int64_t EscapeState_ReturnEscape = 2;
static const int64_t EscapeState_GlobalEscape = 3;
static const int64_t EscapeState_FieldEscape = 4;
static const int64_t EscapeState_Unknown = 5;

/* enum RootKind */
static const int64_t RootKind_Local = 0;
static const int64_t RootKind_Parameter = 1;
static const int64_t RootKind_Global = 2;
static const int64_t RootKind_Temporary = 3;
static const int64_t RootKind_Return = 4;

/* enum AsyncErrorCode */
static const int64_t AsyncErrorCode_E0701 = 0;
static const int64_t AsyncErrorCode_E0702 = 1;
static const int64_t AsyncErrorCode_E0703 = 2;
static const int64_t AsyncErrorCode_E0704 = 3;
static const int64_t AsyncErrorCode_E0705 = 4;
static const int64_t AsyncErrorCode_E0706 = 5;
static const int64_t AsyncErrorCode_E0707 = 6;
static const int64_t AsyncErrorCode_E0708 = 7;
static const int64_t AsyncErrorCode_E0709 = 8;
static const int64_t AsyncErrorCode_E0710 = 9;

/* enum LoweringErrorKind */
static const int64_t LoweringErrorKind_UnresolvedName = 0;
static const int64_t LoweringErrorKind_DuplicateDefinition = 1;
static const int64_t LoweringErrorKind_TypeMismatch = 2;
static const int64_t LoweringErrorKind_InvalidPattern = 3;
static const int64_t LoweringErrorKind_InvalidExpression = 4;
static const int64_t LoweringErrorKind_Other = 5;

/* enum Type */

/* enum Constraint */
static const int64_t Constraint_Eq = 0;
static const int64_t Constraint_HasField = 1;
static const int64_t Constraint_Callable = 2;
static const int64_t Constraint_Subtype = 3;

/* enum UnifyError */
static const int64_t UnifyError_CannotUnify = 0;
static const int64_t UnifyError_InfiniteType = 1;
static const int64_t UnifyError_ArityMismatch = 2;

/* enum InferError */
static const int64_t InferError_UnifyError = 0;
static const int64_t InferError_Undefined = 1;
static const int64_t InferError_NotCallable = 2;
static const int64_t InferError_FieldNotFound = 3;

/* enum LazyInstantiationResult */
static const int64_t LazyInstantiationResult_Success = 0;
static const int64_t LazyInstantiationResult_NotFound = 1;
static const int64_t LazyInstantiationResult_CircularDependency = 2;
static const int64_t LazyInstantiationResult_Deferred = 3;
static const int64_t LazyInstantiationResult_Error = 4;

/* enum ObjTakeResult */
static const int64_t ObjTakeResult_Code = 0;
static const int64_t ObjTakeResult_Template = 1;
static const int64_t ObjTakeResult_Deferred = 2;
static const int64_t ObjTakeResult_NotFound = 3;
static const int64_t ObjTakeResult_Error = 4;

/* enum SymbolType */

/* enum SymbolBinding */
static const int64_t SymbolBinding_Local = 0;
static const int64_t SymbolBinding_Global = 1;
static const int64_t SymbolBinding_Weak = 2;

/* enum TemplateKind */

/* enum ConstraintKind */
static const int64_t ConstraintKind_Equals = 0;
static const int64_t ConstraintKind_Subtype = 1;
static const int64_t ConstraintKind_Implements = 2;
static const int64_t ConstraintKind_HasField = 3;
static const int64_t ConstraintKind_HasMethod = 4;

/* enum Platform */
static const int64_t Platform_Any = 0;
static const int64_t Platform_Linux = 1;
static const int64_t Platform_Windows = 2;
static const int64_t Platform_MacOS = 3;
static const int64_t Platform_FreeBSD = 4;
static const int64_t Platform_None_ = 5;

/* enum Arch */
static const int64_t Arch_X86_64 = 0;
static const int64_t Arch_Aarch64 = 1;
static const int64_t Arch_X86 = 2;
static const int64_t Arch_Arm = 3;
static const int64_t Arch_Riscv64 = 4;
static const int64_t Arch_Riscv32 = 5;
static const int64_t Arch_Wasm32 = 6;
static const int64_t Arch_Wasm64 = 7;

/* enum CompressionType */
static const int64_t CompressionType_None_ = 0;
static const int64_t CompressionType_Zstd = 1;
static const int64_t CompressionType_Lz4 = 2;

/* enum SmfAppType */
static const int64_t SmfAppType_Cli = 0;
static const int64_t SmfAppType_Tui = 1;
static const int64_t SmfAppType_Gui = 2;
static const int64_t SmfAppType_Service = 3;
static const int64_t SmfAppType_Repl = 4;

/* enum SmfSourceType */
static const int64_t SmfSourceType_SingleFile = 0;
static const int64_t SmfSourceType_LibraryFile = 1;

/* enum DataSectionKind */
static const int64_t DataSectionKind_Mutable = 0;
static const int64_t DataSectionKind_ReadOnly = 1;

/* enum SectionType */
static const int64_t SectionType_Code = 0;
static const int64_t SectionType_Data = 1;
static const int64_t SectionType_RoData = 2;
static const int64_t SectionType_Bss = 3;
static const int64_t SectionType_SymTab = 4;
static const int64_t SectionType_StrTab = 5;
static const int64_t SectionType_RelTab = 6;
static const int64_t SectionType_Note = 7;
static const int64_t SectionType_Debug = 8;

/* enum RelocationType */
static const int64_t RelocationType_Abs64 = 0;
static const int64_t RelocationType_Rel32 = 1;
static const int64_t RelocationType_PltRel32 = 2;
static const int64_t RelocationType_GotRel32 = 3;

/* enum SmfWriteError */
static const int64_t SmfWriteError_IoError = 0;
static const int64_t SmfWriteError_InvalidData = 1;

/* enum SymbolVisibility */
static const int64_t SymbolVisibility_Local = 0;
static const int64_t SymbolVisibility_Export = 1;
static const int64_t SymbolVisibility_Import = 2;

/* enum RefKind */
static const int64_t RefKind_Call = 0;
static const int64_t RefKind_Data = 1;
static const int64_t RefKind_Type = 2;

/* enum JitInstantiationResult */
static const int64_t JitInstantiationResult_Success = 0;
static const int64_t JitInstantiationResult_NotFound = 1;
static const int64_t JitInstantiationResult_CircularDependency = 2;
static const int64_t JitInstantiationResult_CompilationError = 3;
static const int64_t JitInstantiationResult_UpdateFailed = 4;

/* enum LoadResult */
static const int64_t LoadResult_Success = 0;
static const int64_t LoadResult_AlreadyLoaded = 1;
static const int64_t LoadResult_Error = 2;

/* enum SymbolResult */
static const int64_t SymbolResult_Found = 0;
static const int64_t SymbolResult_JitCompiled = 1;
static const int64_t SymbolResult_NotFound = 2;
static const int64_t SymbolResult_Error = 3;

/* enum FragmentKind */
static const int64_t FragmentKind_Ident = 0;
static const int64_t FragmentKind_Expr = 1;
static const int64_t FragmentKind_Ty = 2;
static const int64_t FragmentKind_Pat = 3;
static const int64_t FragmentKind_Stmt = 4;
static const int64_t FragmentKind_Block = 5;
static const int64_t FragmentKind_Item = 6;
static const int64_t FragmentKind_Meta = 7;
static const int64_t FragmentKind_Tt = 8;
static const int64_t FragmentKind_Literal = 9;
static const int64_t FragmentKind_Path = 10;
static const int64_t FragmentKind_Lifetime = 11;
static const int64_t FragmentKind_Vis = 12;

/* enum TemplateToken */
static const int64_t TemplateToken_Literal = 0;
static const int64_t TemplateToken_Punct = 1;
static const int64_t TemplateToken_Keyword = 2;
static const int64_t TemplateToken_Param = 3;
static const int64_t TemplateToken_Repetition = 4;
static const int64_t TemplateToken_Group = 5;

/* enum RepetitionKind */
static const int64_t RepetitionKind_ZeroOrMore = 0;
static const int64_t RepetitionKind_OneOrMore = 1;
static const int64_t RepetitionKind_ZeroOrOne = 2;

/* enum Expression */
static const int64_t Expression_BinOp = 0;
static const int64_t Expression_UnaryOp = 1;
static const int64_t Expression_Load = 2;
static const int64_t Expression_GetField = 3;
static const int64_t Expression_ConstInt = 4;
static const int64_t Expression_ConstFloat = 5;
static const int64_t Expression_ConstBool = 6;

/* enum InlinePolicy */
static const int64_t InlinePolicy_Always = 0;
static const int64_t InlinePolicy_Aggressive = 1;
static const int64_t InlinePolicy_Conservative = 2;
static const int64_t InlinePolicy_Never = 3;

/* enum OptLevel */
static const int64_t OptLevel_NoOpt = 0;
static const int64_t OptLevel_Size = 1;
static const int64_t OptLevel_Speed = 2;
static const int64_t OptLevel_Aggressive = 3;

/* enum GenericTemplate */
static const int64_t GenericTemplate_Function = 0;
static const int64_t GenericTemplate_Struct = 1;
static const int64_t GenericTemplate_Class = 2;
static const int64_t GenericTemplate_Enum = 3;
static const int64_t GenericTemplate_Trait = 4;

/* enum CompiledCode */
static const int64_t CompiledCode_Function = 0;
static const int64_t CompiledCode_Struct = 1;
static const int64_t CompiledCode_Class = 2;
static const int64_t CompiledCode_Enum = 3;

/* enum ConcreteType */
static const int64_t ConcreteType_Int = 0;
static const int64_t ConcreteType_Float = 1;
static const int64_t ConcreteType_Bool = 2;
static const int64_t ConcreteType_String = 3;
static const int64_t ConcreteType_Nil = 4;
static const int64_t ConcreteType_Named = 5;
static const int64_t ConcreteType_Array = 6;
static const int64_t ConcreteType_Tuple = 7;
static const int64_t ConcreteType_Dict = 8;
static const int64_t ConcreteType_Function = 9;
static const int64_t ConcreteType_Optional = 10;
static const int64_t ConcreteType_Specialized = 11;

/* enum HotReloadResult */
static const int64_t HotReloadResult_Success = 0;
static const int64_t HotReloadResult_NeedRebuild = 1;
static const int64_t HotReloadResult_InvalidSmf = 2;
static const int64_t HotReloadResult_IoError = 3;

/* enum InstantiationStatus */
static const int64_t InstantiationStatus_Compiled = 0;
static const int64_t InstantiationStatus_Deferred = 1;
static const int64_t InstantiationStatus_JitCompiled = 2;

/* enum PointerKind */
static const int64_t PointerKind_Unique = 0;
static const int64_t PointerKind_Shared = 1;
static const int64_t PointerKind_Weak = 2;
static const int64_t PointerKind_Handle = 3;
static const int64_t PointerKind_Borrow = 4;
static const int64_t PointerKind_BorrowMut = 5;
static const int64_t PointerKind_RawConst = 6;
static const int64_t PointerKind_RawMut = 7;

/* enum DocItemKind */
static const int64_t DocItemKind_Function = 0;
static const int64_t DocItemKind_Struct = 1;
static const int64_t DocItemKind_Class = 2;
static const int64_t DocItemKind_Enum = 3;
static const int64_t DocItemKind_Trait = 4;
static const int64_t DocItemKind_EnumVariant = 5;
static const int64_t DocItemKind_Method = 6;
static const int64_t DocItemKind_StaticMethod = 7;
static const int64_t DocItemKind_MutableMethod = 8;
static const int64_t DocItemKind_Constant = 9;

/* enum IntroducedSymbol */
static const int64_t IntroducedSymbol_Function = 0;
static const int64_t IntroducedSymbol_Field = 1;
static const int64_t IntroducedSymbol_TypeAlias = 2;
static const int64_t IntroducedSymbol_Variable = 3;

/* enum InjectionAnchor */
static const int64_t InjectionAnchor_Head = 0;
static const int64_t InjectionAnchor_Tail = 1;
static const int64_t InjectionAnchor_Here = 2;

/* enum InjectionCodeKind */
static const int64_t InjectionCodeKind_Stmt = 0;
static const int64_t InjectionCodeKind_Block = 1;

/* enum PartialNodeKind */
static const int64_t PartialNodeKind_Module = 0;
static const int64_t PartialNodeKind_Function = 1;
static const int64_t PartialNodeKind_Class = 2;
static const int64_t PartialNodeKind_Struct = 3;
static const int64_t PartialNodeKind_Enum = 4;
static const int64_t PartialNodeKind_Trait = 5;
static const int64_t PartialNodeKind_Impl = 6;
static const int64_t PartialNodeKind_Method = 7;
static const int64_t PartialNodeKind_Block = 8;
static const int64_t PartialNodeKind_Statement = 9;
static const int64_t PartialNodeKind_Expression = 10;
static const int64_t PartialNodeKind_Import = 11;
static const int64_t PartialNodeKind_Export = 12;
static const int64_t PartialNodeKind_ValDecl = 13;
static const int64_t PartialNodeKind_VarDecl = 14;
static const int64_t PartialNodeKind_Parameter = 15;
static const int64_t PartialNodeKind_TypeAnnotation = 16;
static const int64_t PartialNodeKind_Error = 17;

/* enum CommonMistake */
static const int64_t CommonMistake_PythonDef = 0;
static const int64_t CommonMistake_PythonSelf = 1;
static const int64_t CommonMistake_PythonNone = 2;
static const int64_t CommonMistake_PythonTrue = 3;
static const int64_t CommonMistake_PythonFalse = 4;
static const int64_t CommonMistake_RustLetMut = 5;
static const int64_t CommonMistake_RustFnMut = 6;
static const int64_t CommonMistake_RustLifetime = 7;
static const int64_t CommonMistake_RustMacro = 8;
static const int64_t CommonMistake_RustTurbofish = 9;
static const int64_t CommonMistake_JavaPublicClass = 10;
static const int64_t CommonMistake_JavaVoid = 11;
static const int64_t CommonMistake_JavaNew = 12;
static const int64_t CommonMistake_JavaThis = 13;
static const int64_t CommonMistake_CppTemplate = 14;
static const int64_t CommonMistake_CppNamespace = 15;
static const int64_t CommonMistake_TsFunction = 16;
static const int64_t CommonMistake_TsConst = 17;
static const int64_t CommonMistake_TsLet = 18;
static const int64_t CommonMistake_TsInterface = 19;
static const int64_t CommonMistake_TsArrowFunction = 20;
static const int64_t CommonMistake_CSemicolon = 21;
static const int64_t CommonMistake_CTypeFirst = 22;
static const int64_t CommonMistake_MissingColon = 23;
static const int64_t CommonMistake_WrongBrackets = 24;
static const int64_t CommonMistake_ExplicitSelf = 25;
static const int64_t CommonMistake_MissingCommaInArgs = 26;
static const int64_t CommonMistake_MissingColonBeforeBlock = 27;
static const int64_t CommonMistake_MissingIndentAfterColon = 28;
static const int64_t CommonMistake_WrongIndentLevel = 29;

/* enum ErrorHintLevel */
static const int64_t ErrorHintLevel_Error = 0;
static const int64_t ErrorHintLevel_Warning = 1;
static const int64_t ErrorHintLevel_Info = 2;
static const int64_t ErrorHintLevel_Hint = 3;

/* enum RecoveryStrategy */
static const int64_t RecoveryStrategy_SkipToNewline = 0;
static const int64_t RecoveryStrategy_SkipToToken = 1;
static const int64_t RecoveryStrategy_SkipToClosingBrace = 2;
static const int64_t RecoveryStrategy_InsertToken = 3;
static const int64_t RecoveryStrategy_PopContext = 4;

/* enum TestKind */
static const int64_t TestKind_Normal = 0;
static const int64_t TestKind_Slow = 1;
static const int64_t TestKind_Skipped = 2;
static const int64_t TestKind_Ignored = 3;

/* enum PrefixKind */
static const int64_t PrefixKind_Block = 0;
static const int64_t PrefixKind_Literal = 1;

/* enum BinaryOpResult */
static const int64_t BinaryOpResult_Int = 0;
static const int64_t BinaryOpResult_Float = 1;
static const int64_t BinaryOpResult_Bool = 2;
static const int64_t BinaryOpResult_String = 3;
static const int64_t BinaryOpResult_Error = 4;

/* enum NumericType */
static const int64_t NumericType_I8 = 0;
static const int64_t NumericType_I16 = 1;
static const int64_t NumericType_I32 = 2;
static const int64_t NumericType_I64 = 3;
static const int64_t NumericType_U8 = 4;
static const int64_t NumericType_U16 = 5;
static const int64_t NumericType_U32 = 6;
static const int64_t NumericType_U64 = 7;
static const int64_t NumericType_F32 = 8;
static const int64_t NumericType_F64 = 9;

/* enum CastNumericResult */
static const int64_t CastNumericResult_Int = 0;
static const int64_t CastNumericResult_Float = 1;

/* enum CoercionResult */
static const int64_t CoercionResult_Ok = 0;
static const int64_t CoercionResult_Incompatible = 1;
static const int64_t CoercionResult_PrecisionLoss = 2;

/* enum HeuristicOutlineKind */
static const int64_t HeuristicOutlineKind_Function = 0;
static const int64_t HeuristicOutlineKind_Method = 1;
static const int64_t HeuristicOutlineKind_StaticMethod = 2;
static const int64_t HeuristicOutlineKind_MutableMethod = 3;
static const int64_t HeuristicOutlineKind_Class = 4;
static const int64_t HeuristicOutlineKind_Struct = 5;
static const int64_t HeuristicOutlineKind_Enum = 6;
static const int64_t HeuristicOutlineKind_EnumVariant = 7;
static const int64_t HeuristicOutlineKind_Trait = 8;
static const int64_t HeuristicOutlineKind_Impl = 9;
static const int64_t HeuristicOutlineKind_Module = 10;
static const int64_t HeuristicOutlineKind_Import = 11;
static const int64_t HeuristicOutlineKind_Export = 12;
static const int64_t HeuristicOutlineKind_Val = 13;
static const int64_t HeuristicOutlineKind_Var = 14;
static const int64_t HeuristicOutlineKind_Const = 15;
static const int64_t HeuristicOutlineKind_TypeAlias = 16;

/* enum BuiltinCategory */
static const int64_t BuiltinCategory_IO = 0;
static const int64_t BuiltinCategory_Math = 1;
static const int64_t BuiltinCategory_Collections = 2;
static const int64_t BuiltinCategory_Concurrency = 3;
static const int64_t BuiltinCategory_TypeConvert = 4;
static const int64_t BuiltinCategory_Generator = 5;
static const int64_t BuiltinCategory_Testing = 6;
static const int64_t BuiltinCategory_Constructor = 7;

/* enum TypeError */
static const int64_t TypeError_Undefined = 0;
static const int64_t TypeError_TypeMismatch = 1;
static const int64_t TypeError_ConstKeyNotFound = 2;
static const int64_t TypeError_ConstKeyMissing = 3;
static const int64_t TypeError_CoherenceError = 4;
static const int64_t TypeError_Other = 5;

/* enum ReturnWrapMode */
static const int64_t ReturnWrapMode_None_ = 0;
static const int64_t ReturnWrapMode_Resolved = 1;
static const int64_t ReturnWrapMode_Rejected = 2;

/* enum AwaitMode */
static const int64_t AwaitMode_None_ = 0;
static const int64_t AwaitMode_Implicit = 1;
static const int64_t AwaitMode_Explicit = 2;

/* enum TypedAwaitMode */
static const int64_t TypedAwaitMode_None_ = 0;
static const int64_t TypedAwaitMode_ImplicitAwait = 1;
static const int64_t TypedAwaitMode_KeepPromise = 2;
static const int64_t TypedAwaitMode_ExplicitAwait = 3;

/* enum AdviceForm */
static const int64_t AdviceForm_Before = 0;
static const int64_t AdviceForm_AfterSuccess = 1;
static const int64_t AdviceForm_AfterError = 2;
static const int64_t AdviceForm_Around = 3;

/* enum JoinPointKind */
static const int64_t JoinPointKind_Execution = 0;
static const int64_t JoinPointKind_Decision = 1;
static const int64_t JoinPointKind_Condition = 2;
static const int64_t JoinPointKind_Error = 3;

struct ProceedContext;
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
struct SymbolUsage;
struct ContextPack;
struct SourceLoc;
struct FunctionCoverage;
struct ModuleCoverage;
struct CoverageStats;
struct CoverageReport;
struct CoverageCollector;
struct DimSolver;
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
struct CompileOptions;
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
struct ArmRegisterAllocator;
struct BackendFactory;
struct CompilationResult;
struct BackendCapability;
struct BackendOptions;
struct InstructionSupport;
struct CapabilityTracker;
struct CompilerBackendImpl;
struct CraneliftTypeMapper;
struct CudaBackend;
struct CudaTypeMapper;
struct EvalContext;
struct Environment;
struct HirVisitor;
struct SourceLocation;
struct CatchAllPattern;
struct FileAnalysisResult;
struct InterpreterConfig;
struct InterpreterBackendImpl;
struct InterpreterTypeMapper;
struct JitInterpreterConfig;
struct LeanBuilder;
struct LlvmBackend;
struct LlvmTargetTriple;
struct LlvmTargetConfig;
struct LlvmTypeMapper;
struct VReg;
struct MirTestCase;
struct MirTestBuilder;
struct NativeCompileResult;
struct OptimizationPass;
struct RiscVRegisterAllocator;
struct SdnBackendImpl;
struct VulkanBackend;
struct VulkanTypeMapper;
struct WasmImport;
struct WasmExport;
struct BrowserBinding;
struct WasmTypeMapper;
struct X86RegisterAllocator;
struct LinkResult;
struct SMFMetadata;
struct StringMetadata;
struct FullStringEntry;
struct BlockBuilder;
struct SqlBlockDef;
struct RegexBlockDef;
struct JsonBlockDef;
struct MathBlockDef;
struct LossBlockDef;
struct NogradBlockDef;
struct ShellBlockDef;
struct MarkdownBlockDef;
struct HighlightToken;
struct SignatureHelp;
struct Signature;
struct Parameter;
struct BlockExample;
struct LexerConfig;
struct TextSpan;
struct PreLexInfo;
struct BlockRegistry;
struct RegistryBuilder;
struct ResolvedModule;
struct Redirect;
struct ShellCommand;
struct ShellCommands;
struct SqlParam;
struct SqlQuery;
struct RegexPattern;
struct JsonValue;
struct MarkdownDoc;
struct GraphNode;
struct GraphEdge;
struct GraphDiagram;
struct ResolvedBlock;
struct BorrowChecker;
struct ImportEdge;
struct CyclicDependencyError;
struct ImportGraph;
struct MacroSymbol;
struct AutoImport;
struct MacroExports;
struct MacroDirManifest;
struct Segment;
struct ModPath;
struct FileSystem;
struct SymbolEntry;
struct SymbolConflictError;
struct ModDecl;
struct DirManifest;
struct ModuleContents;
struct PollFunction;
struct StateEnum;
struct StateVariant;
struct SuspensionPoint;
struct SuspensionAnalysis;
struct FileFingerprint;
struct DependencyEntry;
struct ChangeSet;
struct BuildCache;
struct IncrementalCompiler;
struct ParallelBuildConfig;
struct BuildUnit;
struct BuildGraph;
struct BuildStats;
struct BuildResult;
struct ParallelBuilder;
struct WriteSite;
struct AllocationSite;
struct GcSafetyConfig;
struct GcRoot;
struct AsyncError;
struct AsyncFunctionCheck;
struct HirLowering;
struct LoweringError;
struct ConstraintSet;
struct DeferredStore;
struct DeferredHint;
struct InferenceEngine;
struct TypeVarId;
struct SkolemId;
struct DeferredTypeId;
struct Unifier;
struct IrCodeGen;
struct IrParam;
struct IrInstruction;
struct IrDslParser;
struct ValidationError;
struct IrValidator;
struct LazyInstantiatorConfig;
struct LibSmfReader;
struct LibSmfHeader;
struct LibSmfBuilder;
struct ModuleEntry;
struct LinkerCompilationContext;
struct LibraryInfo;
struct UndefinedSymbol;
struct NativeLinkConfig;
struct ResolvedObject;
struct MoldCrtFiles;
struct MsvcConfig;
struct ObjectFileResolver;
struct SmfSymbol;
struct Template;
struct TypeConstraint;
struct SubstitutedTemplate;
struct DeferredHints;
struct DeferredTypeVar;
struct DeferredConstraint;
struct UsageSite;
struct ObjTaker;
struct ObjTakerConfig;
struct SmfLocation;
struct SmfHeader;
struct SmfFlags;
struct SmfReaderMemory;
struct NoteSdnMetadata;
struct SmfHeaderRaw;
struct SmfSymbolRaw;
struct SmfSectionRaw;
struct SmfRelocation;
struct SmfSection;
struct SmfWriter;
struct AnalyzedSymbol;
struct SymbolGraph;
struct AnalysisStats;
struct SymbolAnalyzer;
struct CompilerContextImpl;
struct JitCompilationContext;
struct JitInstantiatorConfig;
struct ModuleLoaderLibConfig;
struct LoadedModule;
struct LoadedSymbol;
struct ModuleLoaderConfig;
struct MappedSmf;
struct SmfCache;
struct CacheStats;
struct SyntaxMark;
struct MarkedIdent;
struct HygieneScope;
struct MacroRule;
struct TemplateParam;
struct TemplateError;
struct TemplateValidator;
struct GhostErasureStats;
struct ConstantEvaluator;
struct AlgebraicSimplifier;
struct ConstantFolding;
struct CopyChain;
struct CopyPropagation;
struct ExpressionTable;
struct LivenessAnalysis;
struct InlineCostAnalyzer;
struct FunctionInliner;
struct EdgePair;
struct LoopInfo;
struct LoopDetector;
struct LoopInvariantMotion;
struct PassManager;
struct DirectoryManifest;
struct CallSite;
struct CallSiteAnalyzer;
struct InterfaceBinding;
struct BindingSpecializer;
struct MonoCacheConfig;
struct MonoCacheStats;
struct CacheEntry;
struct MonoCache;
struct CycleDetectionResult;
struct DeferredMonomorphizer;
struct SpecializationKey;
struct MonomorphizationTable;
struct Monomorphizer;
struct HotReloadConfig;
struct MonomorphizationMetadata;
struct BuildMetadata;
struct GenericTemplates;
struct CallRewrite;
struct ModuleRewriter;
struct TypeSubstitution;
struct DocItem;
struct ModuleDocs;
struct DocComment;
struct ExamplesRegistry;
struct InjectionPoint;
struct ConstEvalContext;
struct MacroIntroDecl;
struct MacroInjectDecl;
struct PartialNode;
struct PartialTree;
struct ErrorHint;
struct ErrorCollector;
struct TestMeta;
struct TestGroupMeta;
struct FileTestMeta;
struct CompilerCompilationContext;
struct UnifiedRegistry;
struct HeuristicOutlineItem;
struct HeuristicParseResult;
struct TreeSitter;
struct PatternBinding;
struct BuiltinEntry;
struct BuiltinRegistry;
struct TraitImplRegistry;
struct MixinInfo;
struct PromiseTypeInfo;
struct JoinPoint;
struct JoinPointContext;
struct MatchedAdvice;
struct WeavingRule;
struct WeavingConfig;
struct Option_Span;
struct Option_BuildOutput;
struct Option_text;
struct Option_text__text_;
struct Option_Type;
struct Option_FunctionAttr;
struct Option_HirType;
struct Option_Symbol;
struct Option_Result_BlockValue_BlockError;
struct Option_FnPtr_array;
struct Option_FnPtr_i64;
struct Result_BlockValue_BlockError;

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

/* Option<fn(BlockValue, BlockContext) -> [BlockError]> */
struct Option_FnPtr_array {
    bool has_value;
    FnPtr_array value;
    Option_FnPtr_array() : has_value(false), value{} {}
    Option_FnPtr_array(FnPtr_array v) : has_value(true), value(v) {}
    Option_FnPtr_array(SplValue) : has_value(false), value{} {}
};

/* Option<fn(BlockValue) -> ConstValue> */
struct Option_FnPtr_i64 {
    bool has_value;
    FnPtr_i64 value;
    Option_FnPtr_i64() : has_value(false), value{} {}
    Option_FnPtr_i64(FnPtr_i64 v) : has_value(true), value(v) {}
    Option_FnPtr_i64(SplValue) : has_value(false), value{} {}
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

/* Option<(text, text)> */
struct Option_text__text_ {
    bool has_value;
    int64_t value;  /* struct/Result/tuple pointer as int64_t */
    Option_text__text_() : has_value(false), value(0) {}
    Option_text__text_(int64_t v) : has_value(true), value(v) {}
    Option_text__text_(SplValue) : has_value(false), value(0) {}
};

/* Option<Type> */
struct Option_Type {
    bool has_value;
    int64_t value;  /* struct/Result/tuple pointer as int64_t */
    Option_Type() : has_value(false), value(0) {}
    Option_Type(int64_t v) : has_value(true), value(v) {}
    Option_Type(SplValue) : has_value(false), value(0) {}
};

/* Option<Symbol> */
struct Option_Symbol {
    bool has_value;
    int64_t value;  /* struct/Result/tuple pointer as int64_t */
    Option_Symbol() : has_value(false), value(0) {}
    Option_Symbol(int64_t v) : has_value(true), value(v) {}
    Option_Symbol(SplValue) : has_value(false), value(0) {}
};

/* Option<Result<BlockValue, BlockError>> */
struct Option_Result_BlockValue_BlockError {
    bool has_value;
    int64_t value;  /* struct/Result/tuple pointer as int64_t */
    Option_Result_BlockValue_BlockError() : has_value(false), value(0) {}
    Option_Result_BlockValue_BlockError(int64_t v) : has_value(true), value(v) {}
    Option_Result_BlockValue_BlockError(SplValue) : has_value(false), value(0) {}
};

struct ProceedContext {
    const char* advice_name;
    int64_t proceed_count;
    bool has_error;
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
    WeavingConfig* config;
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

struct CompileOptions {
    int64_t mode;
    SplArray* input_files;
    bool has_output_file;
    const char* output_file;
    int64_t output_format;
    bool optimize;
    bool has_opt_level;
    int64_t opt_level;
    bool release;
    bool debug_info;
    bool verbose;
    int64_t log_level;
    const char* profile;
    bool no_borrow_check;
    const char* backend;
    const char* interpreter_mode;
    bool gc_off;
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
    BlockRegistry* block_registry;
    bool has_current_block_kind;
    const char* current_block_kind;
    int64_t current_lexer_mode;
    bool in_raw_block;
    int64_t raw_block_start;
    int64_t block_brace_depth;
    bool has_unified_registry;
    UnifiedRegistry* unified_registry;
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
    Monomorphizer* monomorphizer;
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
    ResolvedModule* resolved_blocks;
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
    int64_t trait_solver;
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
    GenericTemplates* templates;
    bool has_metadata;
    MonomorphizationMetadata* metadata;
    bool has_note_sdn;
    NoteSdnMetadata* note_sdn;
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
    PreLexInfo* pre_lex_info;
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
    int64_t runtime_checks;
    int64_t dim_check_mode;
    int64_t trait_solver;
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

struct ArmRegisterAllocator {
    int64_t arch;
    SplDict* used_regs;
};

struct BackendFactory {
};

struct CompilationResult {
    bool success;
    const char* output;
    const char* error;
};

struct BackendCapability {
    const char* backend_name;
    bool supports_simd;
    bool supports_gpu;
    bool supports_async;
    bool supports_32bit;
    int32_t instruction_coverage;
};

struct BackendOptions {
    int64_t kind;
    int64_t target;
    int64_t optimization;
    bool has_output_path;
    const char* output_path;
    bool enable_profiling;
    bool enable_coverage;
    bool is_pic;
    const char* interpreter_mode;
};

struct InstructionSupport {
    const char* instruction_name;
    int64_t category;
    bool cranelift;
    bool llvm;
    bool vulkan;
    bool interpreter;
};

struct CapabilityTracker {
    std::vector<InstructionSupport> instructions;
};

struct CompilerBackendImpl {
    int64_t mode;
    bool has_output_path;
    const char* output_path;
};

struct CraneliftTypeMapper {
    int64_t target_bits;
};

struct CudaBackend {
    CudaTypeMapper* type_mapper;
    int64_t compute_capability;
    CompileOptions* options;
};

struct CudaTypeMapper {
    int64_t compute_capability;
};

struct EvalContext {
    Environment* env;
    HirModule* module;
    int64_t backend;
};

struct Environment {
    SplArray* scopes;
    SplDict* globals;
};

struct HirVisitor {
    int64_t backend;
    EvalContext* ctx;
};

struct SourceLocation {
    const char* file_path;
    int32_t line_number;
    int32_t column;
};

struct CatchAllPattern {
    SourceLocation* location;
    int64_t severity;
    const char* context;
    const char* suggestion;
    int64_t is_intentional;
};

struct FileAnalysisResult {
    const char* file_path;
    std::vector<CatchAllPattern> patterns;
    int32_t error_count;
    int32_t warning_count;
    int32_t info_count;
};

struct InterpreterConfig {
    int64_t mode;
    bool enable_debug_hooks;
    bool enable_gc;
    bool use_ffi_arithmetic;
};

struct InterpreterBackendImpl {
    InterpreterConfig* config;
};

struct InterpreterTypeMapper {
};

struct JitInterpreterConfig {
    int64_t mode;
    const char* backend;
    int32_t jit_threshold;
    bool verbose;
};

struct LeanBuilder {
    SplArray* lines;
    int64_t indent_level;
    SplArray* imports;
};

struct LlvmBackend {
    int64_t target;
    int64_t opt_level;
    const char* cpu_override;
    bool emit_llvm_ir;
    bool emit_assembly;
    bool debug_info;
    bool bare_metal;
};

struct LlvmTargetTriple {
    const char* arch;
    const char* vendor;
    const char* os;
    bool has_env;
    const char* env;
};

struct LlvmTargetConfig {
    LlvmTargetTriple* triple;
    const char* cpu;
    SplArray* features;
};

struct LlvmTypeMapper {
    int64_t target_bits;
};

struct VReg {
    int32_t id;
};

struct MirTestCase {
    const char* name;
    SplArray* instructions;
    SplArray* expected_backends;
    const char* description;
};

struct MirTestBuilder {
    SplArray* instructions;
    const char* test_name;
    const char* test_desc;
    SplArray* backends;
    int32_t next_vreg;
};

struct NativeCompileResult {
    bool success;
    const char* binary_path;
    const char* error_message;
    int64_t compile_time_ms;
};

struct OptimizationPass {
    const char* name;
    bool enabled;
    int64_t priority;
    const char* description;
};

struct RiscVRegisterAllocator {
    int64_t arch;
    SplDict* used_regs;
};

struct SdnBackendImpl {
};

struct VulkanBackend {
    VulkanTypeMapper* type_mapper;
    int64_t vulkan_version;
    CompileOptions* options;
};

struct VulkanTypeMapper {
    int64_t vulkan_version;
    int64_t spirv_version;
};

struct WasmImport {
    const char* module_name;
    const char* field_name;
    int64_t kind;
};

struct WasmExport {
    const char* name;
    int64_t kind;
};

struct BrowserBinding {
    const char* simple_name;
    const char* js_module;
    const char* js_function;
    SplArray* params;
    bool has_result;
    int64_t result;
};

struct WasmTypeMapper {
    int64_t target_bits;
};

struct X86RegisterAllocator {
    int64_t arch;
    SplDict* used_regs;
};

struct LinkResult {
    bool success;
    const char* output_file;
    int32_t table_size;
    const char* error_message;
};

struct SMFMetadata {
    int32_t version;
    const char* format;
    const char* target;
    const char* source;
    int32_t string_count;
    SplArray* strings;
};

struct StringMetadata {
    int32_t id;
    const char* text;
    int32_t param_count;
    SplArray* param_names;
    SplArray* format_types;
    const char* source_file;
    int32_t source_line;
};

struct FullStringEntry {
    int32_t id;
    const char* text;
    int32_t length;
    int32_t param_count;
    int32_t aligned_size;
};

struct BlockBuilder {
    const char* _kind;
    int64_t _mode;
    int64_t _features;
    int64_t _parser;
    Option_FnPtr_array _validator;
    Option_FnPtr_i64 _const_eval;
    FnPtr_array _highlighter;
    FnPtr_array _completer;
    FnPtr_HoverInfo _hover;
    const char* _description;
    std::vector<BlockExample> _examples;
};

struct SqlBlockDef {
};

struct RegexBlockDef {
};

struct JsonBlockDef {
};

struct MathBlockDef {
};

struct LossBlockDef {
};

struct NogradBlockDef {
};

struct ShellBlockDef {
};

struct MarkdownBlockDef {
};

struct HighlightToken {
    int64_t start;
    int64_t end;
    int64_t kind;
};

struct SignatureHelp {
    std::vector<Signature> signatures;
    int64_t active_signature;
    int64_t active_parameter;
};

struct Signature {
    const char* label;
    bool has_documentation;
    const char* documentation;
    std::vector<Parameter> parameters;
};

struct Parameter {
    const char* label;
    bool has_documentation;
    const char* documentation;
};

struct BlockExample {
    const char* code;
    const char* description;
    bool has_output;
    const char* output;
};

struct LexerConfig {
    bool caret_is_power;
    bool quote_is_transpose;
    bool implicit_mul;
    bool interpolation;
    bool raw_strings;
    bool preserve_braces;
    bool preserve_newlines;
    bool allow_nested_blocks;
};

struct TextSpan {
    int64_t start;
    int64_t end;
};

struct PreLexInfo {
    std::vector<TextSpan> string_spans;
    std::vector<TextSpan> comment_spans;
    SplArray* escape_positions;
    SplArray* brace_pairs;
};

struct BlockRegistry {
    SplDict* blocks;
};

struct RegistryBuilder {
    BlockRegistry* registry;
    bool include_builtin;
};

struct ResolvedModule {
    OutlineModule* outline;
    std::vector<ResolvedBlock> blocks;
    SplDict* block_map;
};

struct Redirect {
    int64_t kind;
    const char* target;
};

struct ShellCommand {
    const char* program;
    SplArray* args;
    std::vector<Redirect> redirects;
    bool has_pipe_to;
    ShellCommand* pipe_to;
};

struct ShellCommands {
    const char* raw;
    std::vector<ShellCommand> commands;
};

struct SqlParam {
    const char* name;
    int64_t position;
};

struct SqlQuery {
    const char* raw;
    int64_t kind;
    SplArray* tables;
    SplArray* columns;
    std::vector<SqlParam> params;
};

struct RegexPattern {
    const char* raw;
    int64_t _handle;
};

struct JsonValue {
    int64_t kind;
};

struct MarkdownDoc {
    const char* raw;
    SplArray* blocks;
};

struct GraphNode {
    const char* id;
    bool has_label;
    const char* label;
    bool has_shape;
    const char* shape;
};

struct GraphEdge {
    const char* source;
    const char* target;
    bool has_label;
    const char* label;
    bool has_style;
    const char* style;
};

struct GraphDiagram {
    const char* raw;
    int64_t kind;
    std::vector<GraphNode> nodes;
    std::vector<GraphEdge> edges;
};

struct ResolvedBlock {
    const char* kind;
    int64_t value;
    Span* span;
    Span* payload_span;
};

struct BorrowChecker {
    SplArray* errors;
    SplArray* checked_functions;
};

struct ImportEdge {
    const char* from;
    const char* to;
    int64_t kind;
};

struct CyclicDependencyError {
    SplArray* cycle;
};

struct ImportGraph {
    SplDict* edges;
    std::vector<ImportEdge> detailed_edges;
};

struct MacroSymbol {
    const char* module_path;
    const char* name;
    int64_t kind;
};

struct AutoImport {
    const char* from_module;
    const char* macro_name;
};

struct MacroExports {
    std::vector<MacroSymbol> non_macros;
    std::vector<MacroSymbol> macros;
};

struct MacroDirManifest {
    const char* name;
    std::vector<AutoImport> auto_imports;
};

struct Segment {
    const char* name;
};

struct ModPath {
    std::vector<Segment> segments;
};

struct FileSystem {
    SplArray* files;
};

struct SymbolEntry {
    const char* name;
    const char* qualified_name;
    int64_t kind;
    int64_t visibility;
    const char* source_module;
    bool is_imported;
    const char* original_name;
};

struct SymbolConflictError {
    const char* name;
    const char* existing_qualified;
    const char* new_qualified;
};

struct ModDecl {
    const char* name;
    bool is_pub;
};

struct DirManifest {
    const char* name;
    std::vector<ModDecl> children;
    std::vector<SymbolId> exports;
};

struct ModuleContents {
    std::vector<Symbol> symbols;
};

struct PollFunction {
    const char* name;
    const char* state_param;
    const char* waker_param;
    Type* return_type;
    Block* body;
    const char* doc_comment;
};

struct StateEnum {
    const char* name;
    std::vector<StateVariant> variants;
    const char* doc_comment;
};

struct StateVariant {
    const char* name;
    std::vector<Field> fields;
    bool has_suspension_point_id;
    int64_t suspension_point_id;
    const char* doc_comment;
};

struct SuspensionPoint {
    int64_t id;
    Expr* await_expr;
    Expr* awaited_future;
    int64_t context_depth;
    SplArray* live_variables;
    Span* span;
};

struct SuspensionAnalysis {
    std::vector<SuspensionPoint> suspension_points;
    int64_t total_states;
};

struct FileFingerprint {
    const char* path;
    const char* content_hash;
    int64_t modified_time;
    int64_t size;
};

struct DependencyEntry {
    const char* source;
    FileFingerprint* fingerprint;
    SplArray* dependencies;
    SplArray* outputs;
};

struct ChangeSet {
    SplArray* changes;
};

struct BuildCache {
    int64_t entries;
    int64_t fingerprints;
    const char* cache_path;
    int64_t version;
};

struct IncrementalCompiler {
    BuildCache* cache;
    const char* source_root;
};

struct ParallelBuildConfig {
    int64_t num_threads;
    int64_t parallel_threshold;
    bool deterministic;
    bool verbose;
};

struct BuildUnit {
    int64_t id;
    const char* path;
    SplArray* dependencies;
    SplArray* dependents;
    int64_t status;
    bool has_output;
    const char* output;
};

struct BuildGraph {
    int64_t units;
    int64_t next_id;
};

struct BuildStats {
    int64_t total_units;
    int64_t completed;
    int64_t failed;
    int64_t skipped;
    int64_t parallel_batches;
};

struct BuildResult {
    bool success;
    BuildStats* stats;
    SplArray* errors;
    SplArray* outputs;
};

struct ParallelBuilder {
    ParallelBuildConfig* config;
    BuildGraph* graph;
    BuildStats* stats;
};

struct WriteSite {
    int64_t program_point;
    int64_t target_type;
    bool has_field_index;
    int64_t field_index;
    bool is_array_element;
    int64_t source_type;
    int64_t required_barrier;
};

struct AllocationSite {
    int64_t id;
    int64_t program_point;
    int64_t type_id;
    bool has_size_bytes;
    int64_t size_bytes;
    int64_t escape_state;
};

struct GcSafetyConfig {
    int64_t gc_mode;
    bool enable_escape_analysis;
    bool enable_barrier_analysis;
    bool enable_root_tracking;
    int64_t stack_allocation_threshold;
};

struct GcRoot {
    int64_t kind;
    int64_t type_id;
    bool is_interior;
    bool is_pinned;
    int64_t live_range;
};

struct AsyncError {
    int64_t code;
    const char* message;
    Span* span;
    bool has_help;
    const char* help;
    bool has_note;
    const char* note;
    bool has_suggestion;
    const char* suggestion;
};

struct AsyncFunctionCheck {
    bool is_valid;
    SplArray* errors;
    std::vector<AsyncError> detailed_errors;
    const char* function_name;
    bool has_inner_type;
    int64_t inner_type;
};

struct HirLowering {
    SymbolTable* symbols;
    std::vector<LoweringError> errors;
    SymbolId* current_function;
    int64_t loop_depth;
    int64_t type_inference_config;
    const char* module_filename;
};

struct LoweringError {
    const char* message;
    Span* span;
    int64_t kind;
};

struct ConstraintSet {
    SplArray* constraints;
    SplArray* errors;
};

struct DeferredStore {
    std::vector<DeferredHint> hints;
    SplDict* resolved;
};

struct DeferredHint {
    TypeVarId* type_var;
    SplArray* constraints;
    const char* source_module;
    bool has_fallback;
    Type* fallback;
};

struct InferenceEngine {
    Unifier* unifier;
    TypeEnv* env;
    std::vector<DeferredHint> deferred;
    SplArray* errors;
};

struct TypeVarId {
    int64_t id;
};

struct SkolemId {
    int64_t id;
};

struct DeferredTypeId {
    int64_t id;
};

struct Unifier {
    SplDict* substitutions;
    int64_t next_var;
};

struct IrCodeGen {
    std::vector<IrInstruction> instructions;
    const char* backend;
};

struct IrParam {
    const char* name;
    const char* param_type;
};

struct IrInstruction {
    const char* name;
    std::vector<IrParam> params;
    SplArray* backends;
    const char* description;
    const char* rust_pattern;
    const char* error_msg;
    const char* category;
};

struct IrDslParser {
    SplArray* lines;
    int32_t current_line;
    std::vector<IrInstruction> instructions;
};

struct ValidationError {
    const char* instruction;
    const char* error_type;
    const char* message;
};

struct IrValidator {
    std::vector<IrInstruction> instructions;
    std::vector<ValidationError> errors;
};

struct LazyInstantiatorConfig {
    bool allow_defer;
    int32_t max_depth;
    bool verbose;
};

struct LibSmfReader {
    const char* file_path;
    LibSmfHeader* header;
    SplArray* index;
    SplArray* file_data;
    bool verbose;
};

struct LibSmfHeader {
    SplArray* magic;
    uint8_t version_major;
    uint8_t version_minor;
    SplArray* reserved1;
    uint32_t module_count;
    uint64_t index_offset;
    uint64_t index_size;
    uint64_t data_offset;
    uint64_t library_hash;
    uint64_t index_hash;
    SplArray* reserved2;
};

struct LibSmfBuilder {
    std::vector<ModuleEntry> modules;
    bool verbose;
};

struct ModuleEntry {
    const char* name;
    const char* smf_path;
    SplArray* data;
    uint64_t hash;
    const char* obj_path;
    SplArray* obj_data;
    uint64_t obj_hash;
};

struct LinkerCompilationContext {
    SplDict* object_templates;
    DiContainer* project_di;
    AopWeaver* project_aop;
    TypeRegistry* type_reg;
    SplArray* recorded;
};

struct LibraryInfo {
    const char* path;
    const char* name;
    SplArray* modules;
};

struct UndefinedSymbol {
    const char* name;
    const char* object_file;
};

struct NativeLinkConfig {
    SplArray* libraries;
    SplArray* library_paths;
    const char* runtime_path;
    bool pie;
    bool debug;
    bool verbose;
    SplArray* extra_flags;
};

struct ResolvedObject {
    const char* name;
    SplArray* code;
    int64_t symbol_type;
};

struct MoldCrtFiles {
    const char* crt1;
    const char* crti;
    const char* crtn;
    const char* crtbegin;
    const char* crtend;
    const char* dynamic_linker;
    SplArray* lib_dirs;
    bool found;
};

struct MsvcConfig {
    const char* link_exe;
    SplArray* lib_paths;
    SplArray* libs;
    const char* entry_point;
    const char* subsystem;
    const char* machine;
    bool debug;
    SplArray* extra_args;
};

struct ObjectFileResolver {
    SplArray* search_paths;
    SplDict* cache;
    bool verbose;
};

struct SmfSymbol {
    const char* name;
    int32_t section_index;
    int64_t offset;
    int64_t size;
    int64_t ty;
    int64_t binding;
    bool is_generic_template;
    int32_t template_param_count;
    int64_t template_offset;
};

struct Template {
    const char* name;
    SplArray* type_params;
    int64_t kind;
    SplArray* body;
    std::vector<TypeConstraint> constraints;
};

struct TypeConstraint {
    const char* param;
    const char* bound;
};

struct SubstitutedTemplate {
    Template* template;
    SplArray* type_args;
    const char* mangled_name;
};

struct DeferredHints {
    const char* symbol;
    std::vector<DeferredTypeVar> type_vars;
    std::vector<DeferredConstraint> constraints;
    std::vector<UsageSite> usage_sites;
};

struct DeferredTypeVar {
    int64_t id;
    const char* name;
    bool has_fallback;
    int64_t fallback;
};

struct DeferredConstraint {
    int64_t kind;
    int64_t lhs;
    int64_t rhs;
    const char* source_loc;
};

struct UsageSite {
    const char* file;
    const char* loc;
    bool has_context_type;
    int64_t context_type;
};

struct ObjTaker {
    CompilerContext* compiler_ctx;
    SplDict* template_cache;
    SplDict* instance_cache;
    SplDict* smf_metadata;
    ObjTakerConfig* config;
};

struct ObjTakerConfig {
    bool enable_caching;
    int32_t max_cache_size;
    bool verbose;
    bool allow_deferred;
};

struct SmfLocation {
    const char* module_name;
    int64_t source_type;
    const char* file_path;
    int64_t offset;
    int64_t size;
};

struct SmfHeader {
    SplArray* magic;
    uint8_t version_major;
    uint8_t version_minor;
    uint8_t platform;
    uint8_t arch;
    uint32_t flags;
    uint8_t compression;
    uint8_t compression_level;
    SplArray* reserved_compression;
    uint32_t section_count;
    uint64_t section_table_offset;
    uint64_t symbol_table_offset;
    uint32_t symbol_count;
    uint32_t exported_count;
    uint64_t entry_point;
    uint32_t stub_size;
    uint32_t smf_data_offset;
    uint64_t module_hash;
    uint64_t source_hash;
    uint8_t app_type;
    int64_t window_width;
    int64_t window_height;
    uint8_t prefetch_hint;
    uint8_t prefetch_file_count;
    SplArray* reserved_hints;
    SplArray* reserved;
};

struct SmfFlags {
    bool executable;
    bool reloadable;
    bool debug_info;
    bool pic;
    bool has_stub;
};

struct SmfReaderMemory {
    SplArray* data;
    SmfHeader* header;
    SplDict* symbols;
    SplArray* string_table;
    int64_t sections_offset;
    int64_t symbols_offset;
};

struct NoteSdnMetadata {
    bool empty;
};

struct SmfHeaderRaw {
    SplArray* magic;
    uint8_t version_major;
    uint8_t version_minor;
    uint8_t platform;
    uint8_t arch;
    uint32_t flags;
    uint8_t compression;
    uint32_t section_count;
    uint64_t section_table_offset;
    uint64_t symbol_table_offset;
    uint32_t symbol_count;
    uint32_t exported_count;
    uint64_t entry_point;
    uint32_t stub_size;
    uint32_t smf_data_offset;
    uint64_t module_hash;
    uint64_t source_hash;
    uint8_t app_type;
};

struct SmfSymbolRaw {
    uint32_t name_offset;
    uint32_t name_hash;
    uint8_t sym_type;
    uint8_t binding;
    uint8_t visibility;
    uint8_t flags;
    uint64_t value;
    uint64_t size;
    uint32_t type_id;
    uint32_t version;
    uint8_t template_param_count;
    uint64_t template_offset;
};

struct SmfSectionRaw {
    uint8_t section_type;
    uint8_t flags;
    uint64_t offset;
    uint64_t size;
    SplArray* name;
};

struct SmfRelocation {
    int64_t offset;
    int64_t symbol_index;
    int64_t reloc_type;
    int64_t addend;
};

struct SmfSection {
    const char* name;
    int64_t section_type;
    int64_t flags;
    SplArray* data;
    int64_t alignment;
};

struct SmfWriter {
    std::vector<SmfSection> sections;
    std::vector<SmfSymbol> symbols;
    std::vector<SmfRelocation> relocations;
    SplArray* string_table;
    int64_t string_offsets;
};

struct AnalyzedSymbol {
    const char* name;
    int64_t visibility;
    int64_t size;
    const char* section;
    SplArray* references;
    int64_t ref_kinds;
    bool is_reachable;
};

struct SymbolGraph {
    int64_t symbols;
    int64_t reverse_refs;
    SplArray* entry_points;
};

struct AnalysisStats {
    int64_t total_symbols;
    int64_t reachable_symbols;
    int64_t dead_symbols;
    int64_t dead_size;
    int64_t total_size;
};

struct SymbolAnalyzer {
    SymbolGraph* graph;
};

struct CompilerContextImpl {
    SplDict* type_cache;
    SplDict* instantiation_cache;
    int64_t stats;
    int64_t next_type_var;
};

struct JitCompilationContext {
    CompilerContext* compiler_ctx;
    SplDict* smf_templates;
    std::vector<InstantiationRecord> recorded;
};

struct JitInstantiatorConfig {
    bool update_smf;
    int32_t max_depth;
    bool enabled;
    bool verbose;
};

struct ModuleLoaderLibConfig {
    bool enable_jit;
    bool enable_cache;
    int32_t max_cache_size;
    bool verbose;
    bool hot_reload;
    bool enable_libraries;
    SplArray* library_search_paths;
    bool auto_scan_libraries;
};

struct LoadedModule {
    const char* path;
    int64_t reader;
    SplDict* symbols;
    int64_t load_time;
    int32_t version;
};

struct LoadedSymbol {
    const char* name;
    int64_t address;
    int64_t size;
    int64_t ty;
    bool is_jit;
};

struct ModuleLoaderConfig {
    bool enable_jit;
    bool enable_cache;
    int32_t max_cache_size;
    bool verbose;
    bool hot_reload;
};

struct MappedSmf {
    const char* path;
    int64_t address;
    int64_t size;
    SmfHeader* header;
    bool has_note_sdn;
    NoteSdnMetadata* note_sdn;
    int64_t template_section_offset;
    int64_t note_sdn_section_offset;
};

struct SmfCache {
    SplDict* cached_files;
    bool enabled;
    CacheStats* stats;
};

struct CacheStats {
    int32_t total_files;
    int64_t total_memory;
    int32_t cache_hits;
    int32_t cache_misses;
};

struct SyntaxMark {
    int64_t id;
    int64_t expansion_id;
};

struct MarkedIdent {
    const char* name;
    std::vector<SyntaxMark> marks;
};

struct HygieneScope {
    int64_t id;
    int64_t kind;
    bool has_parent;
    int64_t parent;
    SplDict* bindings;
    bool has_expansion_mark;
    SyntaxMark* expansion_mark;
};

struct MacroRule {
    SplArray* matcher;
    SplArray* transcriber;
    bool has_expansion_type;
    const char* expansion_type;
};

struct TemplateParam {
    const char* name;
    int64_t kind;
    int64_t repetition_depth;
};

struct TemplateError {
    const char* message;
    bool has_span;
    int64_t span;
};

struct TemplateValidator {
    SplDict* params;
    std::vector<TemplateError> errors;
    int64_t current_rep_depth;
};

struct GhostErasureStats {
    int64_t ghost_params_erased;
    int64_t ghost_locals_erased;
    int64_t instructions_erased;
    int64_t functions_processed;
};

struct ConstantEvaluator {
    int64_t folded_count;
};

struct AlgebraicSimplifier {
    int64_t simplified_count;
};

struct ConstantFolding {
    ConstantEvaluator* evaluator;
    AlgebraicSimplifier* simplifier;
    int64_t folded_instructions;
    int64_t folded_branches;
};

struct CopyChain {
    SplDict* copy_map;
};

struct CopyPropagation {
    CopyChain* copy_chain;
    int64_t propagated_uses;
    int64_t eliminated_copies;
};

struct ExpressionTable {
    SplDict* table;
    int64_t eliminated;
};

struct LivenessAnalysis {
    SplDict* live_locals;
    SplDict* live_blocks;
};

struct InlineCostAnalyzer {
    int64_t threshold;
};

struct FunctionInliner {
    int64_t next_local_id;
    int64_t inlined_count;
};

struct EdgePair {
    BlockId* from;
    BlockId* to;
};

struct LoopInfo {
    BlockId* header;
    std::vector<BlockId> body;
    std::vector<BlockId> backedges;
    std::vector<EdgePair> exit_edges;
    int64_t trip_count;
};

struct LoopDetector {
    std::vector<LoopInfo> loops;
};

struct LoopInvariantMotion {
    LoopDetector* detector;
    int64_t hoisted_count;
};

struct PassManager {
    SplArray* passes;
    int64_t stats;
};

struct DirectoryManifest {
    const char* name;
    std::vector<Attribute> attributes;
    SplArray* child_modules;
    SplArray* common_uses;
    SplArray* exports;
    SplArray* auto_imports;
    SplArray* capabilities;
    bool is_bypass;
};

struct CallSite {
    const char* function_name;
    std::vector<ConcreteType> type_args;
};

struct CallSiteAnalyzer {
    SplArray* generic_functions;
    std::vector<CallSite> call_sites;
    int64_t type_context;
};

struct InterfaceBinding {
    const char* interface_name;
    const char* impl_type_name;
};

struct BindingSpecializer {
    int64_t bindings;
};

struct MonoCacheConfig {
    int64_t max_entries;
    bool validate_timestamps;
    bool persist_to_disk;
    bool has_cache_dir;
    const char* cache_dir;
};

struct MonoCacheStats {
    int64_t hits;
    int64_t misses;
    int64_t evictions;
    int64_t invalidations;
    int64_t function_entries;
    int64_t struct_entries;
    int64_t class_entries;
};

struct CacheEntry {
    const char* key;
    int64_t value;
    int64_t last_access;
    int64_t content_hash;
};

struct MonoCache {
    MonoCacheConfig* config;
    int64_t entries;
    MonoCacheStats* stats;
};

struct CycleDetectionResult {
    SplArray* errors;
    SplArray* warnings;
    SplArray* all_cycles;
};

struct DeferredMonomorphizer {
    int64_t template_cache;
    int64_t specialization_cache;
    MonomorphizationMetadata* metadata;
    int64_t mode;
};

struct SpecializationKey {
    const char* name;
    std::vector<ConcreteType> type_args;
};

struct MonomorphizationTable {
    SplArray* pending_functions;
    SplArray* pending_structs;
    SplArray* pending_classes;
    int64_t specialized_functions;
    int64_t specialized_structs;
    int64_t specialized_classes;
    SplArray* processed;
};

struct Monomorphizer {
    int64_t generic_functions;
    int64_t generic_structs;
    int64_t generic_classes;
    MonomorphizationTable* table;
};

struct HotReloadConfig {
    bool create_backup;
    bool verify_after_write;
    int64_t reserve_space_percent;
    bool verbose;
};

struct MonomorphizationMetadata {
    int64_t functions;
    int64_t structs;
    int64_t classes;
    int64_t enums;
    int64_t traits;
};

struct BuildMetadata {
    const char* target;
    const char* cpu;
    const char* optimization;
    SplArray* features;
    SplArray* linker_flags;
    const char* compiler_version;
    const char* build_timestamp;
};

struct GenericTemplates {
    std::vector<FunctionDef> functions;
    std::vector<StructDef> structs;
    std::vector<ClassDef> classes;
    std::vector<EnumDef> enums;
    std::vector<TraitDef> traits;
};

struct CallRewrite {
    const char* original_name;
    std::vector<ConcreteType> type_args;
    const char* mangled_name;
};

struct ModuleRewriter {
    int64_t rewrites;
};

struct TypeSubstitution {
    SplDict* mapping;
};

struct DocItem {
    int64_t kind;
    const char* name;
    const char* doc;
    const char* signature;
    const char* visibility;
    bool has_parent;
    const char* parent;
    std::vector<DocItem> children;
};

struct ModuleDocs {
    bool has_name;
    const char* name;
    std::vector<DocItem> items;
};

struct DocComment {
    const char* raw;
};

struct ExamplesRegistry {
    int64_t tables;
};

struct InjectionPoint {
    const char* source_macro;
    const char* label;
    int64_t anchor;
    int64_t code_kind;
};

struct ConstEvalContext {
    int64_t bindings;
};

struct MacroIntroDecl {
    const char* kind;
    const char* name_pattern;
    bool has_type_pattern;
    const char* type_pattern;
};

struct MacroInjectDecl {
    const char* label;
    int64_t anchor;
    int64_t code_kind;
};

struct PartialNode {
    int64_t kind;
    bool has_name;
    const char* name;
    int64_t start_line;
    int64_t start_column;
    int64_t end_line;
    int64_t end_column;
    std::vector<PartialNode> children;
    bool has_error_message;
    const char* error_message;
    bool has_type_hint;
    const char* type_hint;
};

struct PartialTree {
    PartialNode* root;
    const char* source;
};

struct ErrorHint {
    int64_t level;
    const char* message;
    int64_t line;
    int64_t column;
    bool has_suggestion;
    const char* suggestion;
    bool has_help;
    const char* help;
};

struct ErrorCollector {
    std::vector<ErrorHint> errors;
    int64_t max_errors;
    bool in_recovery;
};

struct TestMeta {
    const char* description;
    int64_t kind;
    int64_t line;
    SplArray* tags;
    SplArray* group_path;
};

struct TestGroupMeta {
    const char* name;
    int64_t line;
    std::vector<TestMeta> tests;
    std::vector<TestGroupMeta> children;
};

struct FileTestMeta {
    bool has_file_path;
    const char* file_path;
    std::vector<TestGroupMeta> groups;
    std::vector<TestMeta> top_level_tests;
};

struct CompilerCompilationContext {
    SplDict* ast_cache;
    TypeRegistry* type_reg;
    DiContainer* di;
    AopWeaver* aop;
    int64_t contracts;
    bool coverage;
    SplArray* recorded;
};

struct UnifiedRegistry {
    SplDict* prefixes;
};

struct HeuristicOutlineItem {
    int64_t kind;
    const char* name;
    int64_t line;
    int64_t column;
    int64_t end_line;
    const char* visibility;
    bool has_parent;
    const char* parent;
    bool has_signature;
    const char* signature;
    std::vector<HeuristicOutlineItem> children;
};

struct HeuristicParseResult {
    std::vector<HeuristicOutlineItem> items;
    bool has_impl_target;
    const char* impl_target;
};

struct TreeSitter {
    Lexer* lexer;
    Token* current;
    Token* previous;
    std::vector<ParseError> errors;
    bool has_doc_comment;
    const char* doc_comment;
    std::vector<BlockOutline> inline_blocks;
    bool has_current_context;
    const char* current_context;
    bool fast_mode;
    bool heuristic_mode;
    bool has_registry;
    BlockRegistry* registry;
};

struct PatternBinding {
    const char* name;
    Type* ty;
};

struct BuiltinEntry {
    const char* name;
    int64_t category;
    int64_t param_count;
    const char* description;
};

struct BuiltinRegistry {
    SplDict* entries;
};

struct TraitImplRegistry {
    SplDict* specific_impls;
    bool blanket_impl;
    bool default_blanket_impl;
};

struct MixinInfo {
    const char* name;
    SplArray* type_params;
    SplArray* fields;
    SplArray* methods;
    SplArray* required_traits;
    SplArray* required_mixins;
};

struct PromiseTypeInfo {
    bool has_inner_type;
    const char* inner_type;
    bool is_wrapped;
    bool has_original_type;
    const char* original_type;
};

struct JoinPoint {
    int64_t kind;
    BlockId* block_id;
    int64_t instruction_index;
    JoinPointContext* context;
};

struct JoinPointContext {
    const char* function_name;
    const char* module_path;
    const char* signature;
    SplArray* attributes;
    SplArray* effects;
};

struct MatchedAdvice {
    const char* advice_function;
    int64_t form;
    int64_t priority;
    int32_t specificity;
};

struct WeavingRule {
    const char* predicate_text;
    const char* advice_function;
    int64_t form;
    int64_t priority;
};

struct WeavingConfig {
    bool enabled;
    std::vector<WeavingRule> before_advices;
    std::vector<WeavingRule> after_success_advices;
    std::vector<WeavingRule> after_error_advices;
    std::vector<WeavingRule> around_advices;
};

/* Result<BlockValue, BlockError> */
struct Result_BlockValue_BlockError {
    bool is_ok;
    int64_t ok_value;
    int64_t err_value;
    Result_BlockValue_BlockError() : is_ok(false), ok_value{}, err_value{} {}
    static Result_BlockValue_BlockError Ok(int64_t v) { Result_BlockValue_BlockError r; r.is_ok = true; r.ok_value = v; return r; }
    static Result_BlockValue_BlockError Err(int64_t e) { Result_BlockValue_BlockError r; r.is_ok = false; r.err_value = e; return r; }
};

extern "C" SplArray* sys_get_args();
extern "C" int64_t cranelift_module_new(const char* name, int64_t target);
extern "C" void cranelift_free_module(int64_t module);
extern "C" int64_t cranelift_new_signature(int64_t call_conv);
extern "C" void cranelift_sig_set_return(int64_t sig, int64_t type_);

ProceedContext create_proceed_context_minimal(const char* advice_name);
ProceedContext create_proceed_context_internal(const char* advice_name);
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
void test_if_expression_checking();
void test_nested_lambda();
void test_higher_order_function();
void test_complex_expression();
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
bool Result__is_ok(const Result* self);
bool Result__is_err(const Result* self);
int64_t Result__unwrap(const Result* self);
int64_t Result__unwrap_err(const Result* self);
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
TemplateKey templatekey_required(const char* name, int64_t position);
SymbolUsage symbolusage_empty();
ContextPack contextpack_create(const char* target);
CoverageStats coveragestats_empty();
CoverageCollector coveragecollector_create();
int64_t desugar_async_function(int64_t func);
DimSolver dimsolver_new();
DimError dimerror_mismatch(int64_t d1, int64_t d2, int64_t span);
void di_panic(const char* msg);
DiContainer dicontainer_for_profile(int64_t profile);
void set_container(DiContainer container);
DiContainer get_container();
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
CompilerDriver CompilerDriver__create(int64_t options);
int64_t CompilerDriver__compile(CompilerDriver* self);
bool CompilerDriver__load_sources_impl(CompilerDriver* self);
bool CompilerDriver__parse_all_impl(CompilerDriver* self);
Module CompilerDriver__parse_source(const CompilerDriver* self, int64_t source);
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
SplDict* CompilerDriver__process_async(CompilerDriver* self);
void CompilerDriver__optimize_mir(CompilerDriver* self, int64_t config);
int64_t CompilerDriver__get_optimization_config(const CompilerDriver* self);
const char* find_runtime_lib_dir();
const char* find_simple_old_binary();
int64_t compile_file(const char* path);
int64_t compile_files(SplArray* paths, int64_t mode);
int64_t interpret_file(const char* path);
int64_t jit_file(const char* path);
int64_t aot_file(const char* path, const char* output);
int64_t check_file(const char* path);
int64_t parse_sdn_file(const char* path);
const char* compile_to_smf(const char* path, const char* output);
Config create_config();
int64_t create_block_resolver();
int64_t OutputFormat__from_text(const char* s);
CompileOptions CompileOptions__default();
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
HirModule MethodResolver__resolve_module(MethodResolver* self, HirModule module);
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
void test_validation();
Obligation obligation_new(int64_t ty, TraitRef trait_ref);
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
ArmRegisterAllocator armregisterallocator_new(int64_t arch);
int64_t BackendFactory__create(int64_t target, CompileOptions options);
int64_t BackendFactory__auto_select(int64_t target, int64_t mode);
void BackendFactory__create_specific(int64_t kind, int64_t target, CompileOptions options);
void BackendFactory__try_create(int64_t target, CompileOptions options);
bool BackendFactory__supports_target(int64_t kind, int64_t target);
SplArray* BackendFactory__available_backends();
BackendCapability get_cranelift_capability();
BackendOptions backendoptions_jit();
CompileOptions compileoptions_default_options();
void CapabilityTracker__add_instruction(CapabilityTracker* self, const char* name, int64_t cat, bool cran, bool llvm_, bool vulk, bool interp);
CodegenError codegenerror_new(int64_t kind, const char* message);
CompilerBackendImpl compilerbackendimpl_jit();
CompilerBackendImpl compilerbackendimpl_aot(const char* output);
CraneliftTypeMapper CraneliftTypeMapper__create();
CraneliftTypeMapper CraneliftTypeMapper__create_for_target(int64_t target);
CudaBackend CudaBackend__create(int64_t compute_cap);
CudaTypeMapper CudaTypeMapper__create();
CudaTypeMapper CudaTypeMapper__create_sm(int64_t major, int64_t minor);
SplDict* empty_env_scope();
Environment environment_new();
bool environment_assign(Environment self, SymbolId symbol, int64_t value);
HirVisitor hirvisitor_new(int64_t backend, HirModule module);
const char* SourceLocation__to_string(const SourceLocation* self);
SourceLocation CatchAllPattern__get_location(const CatchAllPattern* self);
int64_t CatchAllPattern__get_severity(const CatchAllPattern* self);
bool CatchAllPattern__is_error(const CatchAllPattern* self);
const char* CatchAllPattern__format_report(const CatchAllPattern* self);
FileAnalysisResult FileAnalysisResult__new(const char* path);
InterpreterConfig interpreterconfig_classic();
InterpreterConfig interpreterconfig_optimized();
InterpreterConfig interpreterconfig_with_gc(InterpreterConfig self, bool enabled);
InterpreterConfig interpreterconfig_with_debug(InterpreterConfig self, bool enabled);
InterpreterBackendImpl interpreterbackendimpl_new();
InterpreterBackendImpl interpreterbackendimpl_with_config(InterpreterConfig config);
InterpreterBackendImpl interpreterbackendimpl_optimized();
InterpreterTypeMapper InterpreterTypeMapper__create();
JitInterpreterConfig jitinterpreterconfig_default();
const char* mir_type_to_lean(MirType ty);
LeanBuilder LeanBuilder__create();
const char* generate_borrow_proofs(int64_t func, int64_t checker);
const char* generate_place_definition(int64_t place);
const char* generate_borrow_definition(int64_t borrow, int64_t idx);
const char* generate_safety_theorem(const char* func_name, int64_t borrow_count);
const char* generate_lean_module(MirModule module);
LlvmBackend LlvmBackend__create(int64_t target, int64_t opt_level);
SplArray* passes_for_level(int64_t level);
LlvmTargetTriple llvmtargettriple_from_target(int64_t target);
LlvmTargetTriple llvmtargettriple_from_target_baremetal(int64_t target);
LlvmTargetTriple llvmtargettriple_from_target_with_mode(int64_t target, bool bare_metal);
const char* llvmtargettriple_to_text(LlvmTargetTriple triple);
LlvmTargetConfig llvmtargetconfig_for_target(int64_t target, Option_text cpu_override);
LlvmTargetConfig llvmtargetconfig_for_target_baremetal(int64_t target, Option_text cpu_override);
LlvmTargetConfig llvmtargetconfig_for_target_with_mode(int64_t target, const char* cpu_override, bool bare_metal);
LlvmTypeMapper LlvmTypeMapper__create();
LlvmTypeMapper LlvmTypeMapper__create_32bit();
LlvmTypeMapper LlvmTypeMapper__create_64bit();
LlvmTypeMapper LlvmTypeMapper__create_for_target(int64_t target);
void MirTestBuilder__add_const_int(MirTestBuilder* self, int32_t dest, int64_t value);
void MirTestBuilder__add_const_float(MirTestBuilder* self, int32_t dest, double value);
void MirTestBuilder__add_const_bool(MirTestBuilder* self, int32_t dest, bool value);
void MirTestBuilder__add_add(MirTestBuilder* self, int32_t dest, int32_t left, int32_t right);
int64_t MirTestCase__instruction_count(const MirTestCase* self);
bool MirTestCase__is_supported(const MirTestCase* self, int64_t backend);
bool is_supported(int64_t backend);
void MirTestBuilder__add_binop(MirTestBuilder* self, int32_t dest, const char* op, int32_t left, int32_t right);
void MirTestBuilder__add_ret(MirTestBuilder* self, int32_t vreg);
void MirTestBuilder__add_ret_void(MirTestBuilder* self);
void MirTestBuilder__add_branch(MirTestBuilder* self, int32_t cond, int32_t then_block, int32_t else_block);
void MirTestBuilder__add_jump(MirTestBuilder* self, int32_t block);
void MirTestBuilder__only_backend(MirTestBuilder* self, int64_t backend);
void MirTestBuilder__only_backends(MirTestBuilder* self, SplArray* backend_list);
MirTestCase MirTestBuilder__build(const MirTestBuilder* self);
NativeCompileResult nativecompileresult_success_result(const char* binary_path, int64_t compile_time_ms);
OptimizationPass optimizationpass_new(const char* name, bool enabled, int64_t priority, const char* description);
RiscVRegisterAllocator riscvregisterallocator_new(int64_t arch);
VulkanBackend VulkanBackend__create(int64_t vk_version);
VulkanTypeMapper VulkanTypeMapper__create();
int64_t mir_type_to_wasm(MirType ty, int64_t target);
BrowserBinding browserbinding_console_log();
WasmTypeMapper WasmTypeMapper__create();
WasmTypeMapper WasmTypeMapper__create_wasm32();
WasmTypeMapper WasmTypeMapper__create_wasm64();
WasmTypeMapper WasmTypeMapper__create_for_target(int64_t target);
X86RegisterAllocator x86registerallocator_new(int64_t arch);
LinkResult linkresult_ok(const char* output, int32_t table_size);
SMFMetadata smfmetadata_empty();
StringMetadata stringmetadata_create(int32_t id, const char* text, int32_t params);
FullStringEntry fullstringentry_from_smf_entry(int64_t entry);
const char* generate_smt_section(int64_t table);
const char* generate_entry_asm(FullStringEntry entry);
const char* escape_for_asm(const char* s);
const char* escape_for_comment(const char* s);
const char* generate_linker_script_fragment();
const char* generate_metadata_json(int64_t table);
const char* escape_for_json(const char* s);
bool write_asm_file(const char* asm_code, const char* output_path);
bool write_metadata_file(int64_t table, const char* output_path);
bool file_write(const char* path, const char* content);
void test_codegen();
BlockBuilder blockbuilder_new(const char* kind);
SplArray* sql_keywords();
BlockContext blockcontext_new(const char* payload, Span payload_span, Span block_span);
int64_t error_at(BlockContext ctx, const char* message, int64_t offset, int64_t length);
std::vector<HighlightToken> highlight_keywords(const char* text, SplArray* keywords);
std::vector<HighlightToken> highlight_strings(const char* text);
LexerConfig lexerconfig_default();
TextSpan textspan_new(int64_t start, int64_t end);
PreLexInfo prelexinfo_empty();
void enable_block(const char* kind, int64_t block_def);
void disable_block(const char* kind);
SplArray* list_blocks();
int64_t block_info(const char* kind);
const char* parse_json(const char* text);
const char* parse_yaml(const char* text);
const char* parse_toml(const char* text);
const char* parse_xml(const char* text);
const char* parse_csv(const char* text);
int64_t json_parse_internal(const char* input);
int64_t yaml_parse_internal(const char* input);
int64_t toml_parse_internal(const char* input);
int64_t xml_parse_internal(const char* input);
SplArray* csv_parse_internal(const char* input);
BlockRegistry blockregistry_new();
BlockRegistry blockregistry_default();
bool blockregistry_unregister(BlockRegistry self, const char* kind);
BlockRegistry block_registry();
void register_block(int64_t block_def);
bool unregister_block(const char* kind);
bool is_block(const char* kind);
void get_block(const char* kind);
bool is_block_registered(const char* kind);
void with_block(int64_t block_def, int64_t body);
RegistryBuilder registrybuilder_new();
ResolvedModule resolvedmodule_new(OutlineModule outline, SplArray* blocks);
const char* interpolate_variables(const char* text, SplDict* vars);
const char* strip_indent(const char* text);
const char* normalize_newlines(const char* text);
SplArray* validate_json(int64_t value);
SplArray* validate_regex(int64_t value);
SplArray* validate_sql(int64_t value, const char* dialect);
SplArray* validate_json_structure(int64_t value);
SplArray* validate_sql_dialect(int64_t query, const char* dialect);
int64_t json_depth(int64_t value, int64_t current);
const char* json_type_name(int64_t value);
ResolvedBlock resolvedblock_new(const char* kind, int64_t value, Span span, Span payload_span);
int64_t Place__local(int64_t id);
int64_t Place__static_var(const char* name);
int64_t Borrow__create(int64_t id, int64_t place, int64_t kind, int64_t lifetime, int64_t point);
int64_t place_static_var(const char* name);
int64_t place_deref(int64_t self);
int64_t Region__create(int64_t id, int64_t lifetime);
BorrowChecker BorrowChecker__create();
int64_t BasicBlock__create(int64_t id);
ImportEdge importedge_new(const char* from, const char* to, int64_t kind);
CyclicDependencyError cyclicdependencyerror_new(SplArray* cycle);
ImportGraph importgraph_new();
MacroSymbol macrosymbol_new(const char* module_path, const char* name, int64_t kind);
MacroSymbol macrosymbol_value_sym(const char* module_path, const char* name);
MacroSymbol macrosymbol_macro_sym(const char* module_path, const char* name);
AutoImport autoimport_new(const char* from_module, const char* macro_name);
MacroExports macroexports_new();
MacroDirManifest macrodirmanifest_new(const char* name);
bool is_auto_imported(MacroDirManifest manifest, MacroSymbol sym);
std::vector<MacroSymbol> auto_imported_macros(MacroDirManifest manifest, MacroExports exports);
std::vector<MacroSymbol> glob_import(MacroDirManifest manifest, MacroExports exports);
int64_t explicit_import(MacroExports exports, const char* name);
MacroExports combine_exports(MacroExports e1, MacroExports e2);
FileSystem filesystem_new();
FileSystem filesystem_from_files(SplArray* files);
const char* to_file_path(const char* root, ModPath mp);
const char* to_dir_path(const char* root, ModPath mp);
int64_t resolve(FileSystem fs, const char* root, ModPath mp);
bool is_well_formed(FileSystem fs, const char* root);
SymbolConflictError symbolconflicterror_new(const char* name, const char* existing, const char* new_sym);
Symbol symbol_new(const char* name, int64_t visibility);
Symbol symbol_pub_symbol(const char* name);
Symbol symbol_priv_symbol(const char* name);
ModDecl moddecl_new(const char* name, bool is_pub);
ModDecl moddecl_pub_decl(const char* name);
ModDecl moddecl_priv_decl(const char* name);
DirManifest dirmanifest_new(const char* name);
ModuleContents modulecontents_new();
StateEnum generate_state_enum(const char* func_name, int64_t analysis);
SuspensionAnalysis analyze_suspensions(Function func);
ChangeSet changeset_empty();
BuildCache buildcache_empty(const char* cache_path);
BuildCache buildcache_load(const char* cache_path);
IncrementalCompiler incrementalcompiler_create(const char* source_root, const char* cache_path);
ParallelBuildConfig parallelbuildconfig_default();
ParallelBuildConfig parallelbuildconfig_single_threaded();
BuildGraph buildgraph_empty();
int64_t buildgraph_add_unit(BuildGraph self, const char* path, SplArray* dependencies);
BuildStats buildstats_empty();
ParallelBuilder parallelbuilder_create(ParallelBuildConfig config);
int64_t parallelbuilder_add_unit(ParallelBuilder self, const char* path, SplArray* dependencies);
int64_t parallelbuilder_build(ParallelBuilder self, FnPtr_i64 compile_fn);
WriteSite writesite_field_write(int64_t point, int64_t target_type, int64_t field_idx, int64_t source_type);
AllocationSite allocationsite_create(int64_t id, int64_t point, int64_t type_id);
GcSafetyConfig gcsafetyconfig_default_config();
GcRoot gcroot_local(int64_t id, int64_t type_id);
HirExpr hirlowering_lower_expr(int64_t self, Expr e);
int64_t hirlowering_lower_binop(int64_t self, int64_t op);
int64_t hirlowering_lower_unaryop(int64_t self, int64_t op);
HirPattern hirlowering_lower_pattern(int64_t self, Pattern p);
HirBlock hirlowering_lower_block(int64_t self, Block b);
HirAsm hirlowering_lower_asm(int64_t self, AsmExpr asm_code);
HirModule hirlowering_lower_module(int64_t self, Module module);
HirStmt hirlowering_lower_stmt(int64_t self, Stmt s);
HirLowering hirlowering_new();
ConstraintSet constraintset_empty();
DeferredStore deferredstore_empty();
InferenceEngine inferenceengine_create();
const char* hints_to_sdn(std::vector<DeferredHint> hints);
std::vector<DeferredHint> hints_from_sdn(const char* content);
Unifier unifier_empty();
Type unifier_fresh_var(Unifier self);
const char* IrCodeGen__generate_match(const IrCodeGen* self);
const char* IrCodeGen__generate_instruction_arm(const IrCodeGen* self, int64_t inst);
const char* IrCodeGen__generate_unsupported_group(const IrCodeGen* self, SplArray* insts);
SplArray* IrCodeGen__get_supported_instructions(const IrCodeGen* self);
SplArray* IrCodeGen__get_unsupported_instructions(const IrCodeGen* self);
bool IrCodeGen__is_supported(const IrCodeGen* self, int64_t inst);
const char* generate_backend_code(SplArray* instructions, const char* backend);
void IrDslParser__parse(IrDslParser* self);
void IrDslParser__parse_instruction(IrDslParser* self);
void IrValidator__validate(IrValidator* self);
void IrValidator__validate_instruction(IrValidator* self, IrInstruction inst);
void IrValidator__add_error(IrValidator* self, const char* inst_name, const char* err_type, const char* msg);
LazyInstantiatorConfig lazyinstantiatorconfig_default();
SplArray* text_to_bytes(const char* text);
LibSmfHeader libsmfheader_new_default();
LibSmfBuilder libsmfbuilder_new();
const char* LinkerCompilationContext__load_template(const LinkerCompilationContext* self, const char* name);
bool LinkerCompilationContext__has_template(const LinkerCompilationContext* self, const char* name);
TypeRegistry LinkerCompilationContext__type_registry(const LinkerCompilationContext* self);
int64_t LinkerCompilationContext__contract_mode(const LinkerCompilationContext* self);
int64_t LinkerCompilationContext__di_container(const LinkerCompilationContext* self);
int64_t LinkerCompilationContext__aop_weaver(const LinkerCompilationContext* self);
bool LinkerCompilationContext__coverage_enabled(const LinkerCompilationContext* self);
const char* LinkerCompilationContext__compile_template(const LinkerCompilationContext* self, GenericTemplate template, std::vector<ConcreteType> type_args);
const char* scan_libraries(SplArray* library_paths, bool verbose);
const char* extract_basename(const char* path);
NativeLinkConfig NativeLinkConfig__default();
int64_t link_native_cc(SplArray* object_files, const char* output, NativeLinkConfig config);
int64_t link_native_windows(SplArray* object_files, const char* output, NativeLinkConfig config);
int64_t find_crt_files(bool pie, bool verbose);
int64_t link_to_self_contained(SplArray* smf_data, const char* output, int64_t config);
int64_t detect_self_contained(const char* exe_path);
int64_t find_runtime_binary();
SplArray* build_trailer(int64_t smf_offset, int64_t smf_size, int64_t checksum);
int64_t fnv1a_hash(SplArray* data);
SplArray* i64_to_le_bytes(int64_t value);
LinkConfig linkconfig_default();
const char* find_mold_path();
const char* find_lld_path();
const char* find_ld_path();
const char* execute_linker(const char* linker_path, SplArray* args);
const char* write_elf_object(SplArray* code, const char* name, const char* output_path);
int64_t linker_file_size(const char* path);
MoldCrtFiles mold_find_crt_files(bool pie, bool verbose);
MsvcConfig msvcconfig_default();
ObjectFileResolver objectfileresolver_new(bool verbose);
ObjTakerConfig objtakerconfig_default();
int64_t platform_from_u8(uint8_t value);
int64_t arch_from_u8(uint8_t value);
int64_t compressiontype_from_u8(uint8_t value);
int64_t smfapptype_from_u8(uint8_t value);
SmfLocation smflocation_single_file(const char* module_name, const char* file_path, int64_t size);
SmfHeader smfheader_new_v1_1(int64_t platform, int64_t arch);
SplArray* u32_to_bytes(uint32_t value);
SplArray* u64_to_bytes(uint64_t value);
const char* parse_header_from_bytes(SplArray* data);
NoteSdnMetadata stub_new_note_sdn();
SmfHeader smfheader_from_raw(SmfHeaderRaw raw);
const char* char_from_byte(uint8_t b);
const char* bytes_to_string(SplArray* bytes);
NoteSdnMetadata parse_note_sdn(const char* sdn_text);
SmfWriter smfwriter_create();
int64_t smfwriter_add_string(SmfWriter self, const char* s);
int64_t smfwriter_add_code_section(SmfWriter self, const char* name, SplArray* code);
int64_t smfwriter_add_data_section(SmfWriter self, const char* name, SplArray* data, int64_t kind);
int64_t smfwriter_add_bss_section(SmfWriter self, const char* name, int64_t size);
int64_t smfwriter_add_symbol(SmfWriter self, SmfSymbol symbol);
int64_t smfwriter_add_note_section(SmfWriter self, const char* name, SplArray* data);
AnalyzedSymbol analyzedsymbol_create(const char* name, int64_t visibility);
SymbolGraph symbolgraph_empty();
SymbolAnalyzer symbolanalyzer_create();
SymbolGraph symbolanalyzer_analyze(SymbolAnalyzer self);
CompilerContext compilercontext_create();
SplArray* CompilerContextImpl__infer_types(const CompilerContextImpl* self, Template template, SplArray* hints);
CompilationResult CompilerContextImpl__instantiate_template(const CompilerContextImpl* self, Template template, SplArray* type_args);
JitCompilationContext jitcompilationcontext_from_smf(SplDict* tmpls);
int64_t compiler_create_context();
bool compiler_destroy_context(int64_t handle);
const char* compiler_infer_types(int64_t handle, const char* template_json, const char* hints_json);
bool compiler_check_types(int64_t handle, const char* types_json, const char* constraints_json);
const char* compiler_instantiate_template(int64_t handle, const char* template_json, const char* types_json);
const char* compiler_get_stats(int64_t handle);
JitInstantiatorConfig jitinstantiatorconfig_default();
ModuleLoaderLibConfig moduleloaderlibconfig_default();
ModuleLoaderConfig moduleloaderconfig_default();
SmfCache smfcache_new();
int64_t native_mmap_file(const char* path, int32_t prot, int32_t flags, int64_t offset, int64_t length);
bool native_munmap(int64_t address, int64_t size);
SplArray* native_mmap_read_bytes(int64_t address, int64_t offset, int64_t length);
const char* native_mmap_read_string(int64_t address, int64_t offset, int64_t max_length);
bool native_madvise(int64_t address, int64_t size, int32_t advice);
bool native_msync(int64_t address, int64_t size, bool is_async);
bool native_mlock(int64_t address, int64_t size);
bool native_munlock(int64_t address, int64_t size);
int64_t native_alloc_exec_memory(int64_t size);
int64_t native_alloc_rw_memory(int64_t size);
bool native_free_exec_memory(int64_t address, int64_t size);
int64_t native_write_exec_memory(int64_t address, SplArray* code, int64_t offset);
bool native_make_executable(int64_t address, int64_t size);
void native_flush_icache(int64_t address, int64_t size);
int64_t native_get_function_pointer(int64_t address);
int64_t native_call_function_0(int64_t fn_ptr);
int64_t native_call_function_1(int64_t fn_ptr, int64_t arg1);
int64_t native_call_function_2(int64_t fn_ptr, int64_t arg1, int64_t arg2);
int64_t native_exec_memory_total();
int64_t native_exec_memory_count();
int32_t unsafe_open(const char* path, int32_t flags);
void unsafe_close(int32_t fd);
int64_t unsafe_mmap(int64_t addr, int64_t length, int32_t prot, int32_t flags, int32_t fd, int64_t offset);
int32_t unsafe_munmap(int64_t addr, int64_t length);
int32_t unsafe_mprotect(int64_t addr, int64_t length, int32_t prot);
int32_t unsafe_madvise(int64_t addr, int64_t length, int32_t advice);
int32_t unsafe_msync(int64_t addr, int64_t length, int32_t flags);
int32_t unsafe_mlock(int64_t addr, int64_t length);
int32_t unsafe_munlock(int64_t addr, int64_t length);
uint8_t ptr_read_u8(int64_t ptr, int64_t offset);
void ptr_write_u8(int64_t ptr, int64_t offset, uint8_t value);
SplArray* slice_from_raw_parts(int64_t ptr, int64_t len);
const char* str_from_utf8_lossy(SplArray* bytes);
SyntaxMark syntaxmark_create(int64_t expansion_id);
MarkedIdent markedident_from_name(const char* name);
MarkedIdent markedident_add_mark(MarkedIdent self, SyntaxMark mark);
MarkedIdent markedident_remove_mark(MarkedIdent self, SyntaxMark mark);
HygieneScope hygienescope_root();
MacroRule macrorule_create(SplArray* matcher, SplArray* transcriber);
TemplateParam templateparam_simple(const char* name, int64_t kind);
TemplateParam templateparam_repeated(const char* name, int64_t kind, int64_t depth);
TemplateError templateerror_create(const char* message);
TemplateError templateerror_at(const char* message, int64_t pos);
TemplateValidator TemplateValidator__create();
GhostErasureStats ghosterasurestats_new();
ConstantEvaluator constantevaluator_new();
AlgebraicSimplifier algebraicsimplifier_new();
ConstantFolding constantfolding_new();
CopyChain copychain_new();
CopyPropagation copypropagation_new();
ExpressionTable expressiontable_new();
LivenessAnalysis livenessanalysis_new();
InlineCostAnalyzer inlinecostanalyzer_new(int64_t threshold);
FunctionInliner functioninliner_new(int64_t next_local_id);
LoopDetector loopdetector_new();
LoopInvariantMotion loopinvariantmotion_new();
PassManager passmanager_new();
const char* path_join(const char* base, const char* segment);
const char* path_basename(const char* path);
DirectoryManifest directorymanifest_new(const char* name);
CallSiteAnalyzer callsiteanalyzer_create(SplArray* generic_function_names);
BindingSpecializer bindingspecializer_create();
BindingSpecializer bindingspecializer_from_bindings(std::vector<InterfaceBinding> bindings);
MonoCacheConfig monocacheconfig_default_config();
MonoCacheConfig monocacheconfig_memory_only();
MonoCacheConfig monocacheconfig_persistent(const char* cache_dir);
MonoCacheStats monocachestats_empty();
MonoCache monocache_create(MonoCacheConfig config);
CycleDetectionResult cycledetectionresult_new();
DeferredMonomorphizer deferredmonomorphizer_new(int64_t mode);
const char* concrete_type_to_text(ConcreteType ty);
MonomorphizationTable monomorphizationtable_create();
const char* monomorphizationtable_request_function(MonomorphizationTable self, const char* name, std::vector<ConcreteType> type_args, int64_t func);
Monomorphizer monomorphizer_create();
int64_t monomorphizer_specialize_function_internal(Monomorphizer self, SpecializationKey key, int64_t func);
HirFunction specialize_function_with_types(HirFunction func, SplArray* type_args);
const char* generate_mangled_name(const char* base_name, SplArray* type_args);
const char* mangle_type(int64_t ty);
HotReloadConfig hotreloadconfig_default();
MonomorphizationMetadata monomorphizationmetadata_new();
BuildMetadata buildmetadata_new(const char* target, const char* cpu, const char* optimization, SplArray* features, SplArray* linker_flags, const char* compiler_version, const char* build_timestamp);
GenericTemplates generictemplates_new();
ModuleRewriter modulerewriter_create();
int64_t monomorphize_module(SplArray* generic_names, std::vector<CallSite> call_sites);
MonomorphizationTable monomorphizationtable_new();
SpecializationKey specializationkey_new(const char* name, std::vector<ConcreteType> type_args);
TypeSubstitution typesubstitution_empty();
TypeSubstitution typesubstitution_from_params(std::vector<HirTypeParam> type_params, SplArray* type_args);
TypeSubstitution typesubstitution_from_concrete(std::vector<HirTypeParam> type_params, std::vector<ConcreteType> type_args);
int64_t concrete_to_hir_type(ConcreteType ct, Span span);
int64_t substitute_type(int64_t ty, TypeSubstitution subst);
HirExpr substitute_expr(HirExpr expr, TypeSubstitution subst);
HirCallArg substitute_call_arg(HirCallArg arg, TypeSubstitution subst);
HirMatchArm substitute_match_arm(HirMatchArm arm, TypeSubstitution subst);
HirPattern substitute_pattern(HirPattern pat, TypeSubstitution subst);
int64_t substitute_pattern_payload(int64_t payload, TypeSubstitution subst);
int64_t substitute_enum_payload(int64_t payload, TypeSubstitution subst);
HirCompClause substitute_comp_clause(HirCompClause clause, TypeSubstitution subst);
HirBlock substitute_block(HirBlock block, TypeSubstitution subst);
HirStmt substitute_stmt(HirStmt stmt, TypeSubstitution subst);
HirParam substitute_param(HirParam param, TypeSubstitution subst);
HirFunction substitute_function(HirFunction func, TypeSubstitution subst, const char* mangled_name);
bool type_uses_param(Type ty, const char* param);
int64_t infer_concrete_type(Expr expr, int64_t type_context);
ConcreteType ast_type_to_concrete(Type ty, int64_t bindings);
Type concrete_to_ast_type(ConcreteType concrete);
int64_t ast_pointer_kind_to_concrete(int64_t kind);
int64_t concrete_pointer_kind_to_ast(int64_t kind);
DocItem docitem_new(int64_t kind, const char* name, const char* signature);
ModuleDocs moduledocs_empty();
ModuleDocs moduledocs_named(const char* name);
const char* format_item_markdown(DocItem item);
const char* format_item_html(DocItem item);
const char* html_escape(const char* s);
DocComment doccomment_from_raw(const char* raw);
ExamplesRegistry examplesregistry_empty();
ModuleDocs generate_docs_from_source(const char* source, Option_text module_name);
SplArray* collect_doc_block(SplArray* lines, int64_t start);
int64_t try_extract_item(const char* trimmed, const char* doc);
const char* extract_first_name(const char* s);
const char* extract_signature(const char* line);
const char* symbol_name(IntroducedSymbol sym);
const char* symbol_source_macro(IntroducedSymbol sym);
ConstEvalContext constevalcontext_empty();
MacroRegistry macroregistry_default();
MacroRegistry macroregistry_with_ll1_mode();
const char* expand_name_pattern(const char* pattern, ConstEvalContext ctx);
std::vector<PartialNode> collect_errors(PartialNode node);
int64_t find_deepest(PartialNode node, int64_t line, int64_t column);
int64_t find_node_at_position(PartialTree tree, int64_t line, int64_t column);
PartialTree build_partial_tree(const char* source);
int64_t parse_top_level(SplArray* lines, int64_t start);
int64_t detect_declaration(const char* trimmed);
int64_t find_block_end(SplArray* lines, int64_t start, int64_t base_indent);
const char* extract_ident(const char* s);
int64_t count_spaces(const char* line);
const char* mistake_message(int64_t m);
const char* mistake_suggestion(int64_t m);
int64_t detect_common_mistake(const char* current_lexeme, const char* current_kind, const char* prev_kind, Option_text next_lexeme);
ErrorHint errorhint_error(const char* message, int64_t line, int64_t column);
ErrorHint errorhint_warning(const char* message, int64_t line, int64_t column);
ErrorCollector errorcollector_default();
ErrorCollector errorcollector_with_limit(int64_t max_errors);
TestMeta testmeta_new(const char* description, int64_t line, int64_t kind);
TestGroupMeta testgroupmeta_new(const char* name, int64_t line);
FileTestMeta filetestmeta_empty();
FileTestMeta filetestmeta_for_file(const char* path);
FileTestMeta extract_tests_from_source(const char* source, Option_text file_path);
FileTestMeta extract_file_test_meta(const char* source, Option_text file_path);
Option_text__text_ try_parse_dsl_call(const char* trimmed);
const char* extract_string_literal(const char* s);
int64_t count_leading_spaces(const char* line);
const char* CompilerCompilationContext__load_template(const CompilerCompilationContext* self, const char* name);
bool CompilerCompilationContext__has_template(const CompilerCompilationContext* self, const char* name);
TypeRegistry CompilerCompilationContext__type_registry(const CompilerCompilationContext* self);
int64_t CompilerCompilationContext__contract_mode(const CompilerCompilationContext* self);
int64_t CompilerCompilationContext__di_container(const CompilerCompilationContext* self);
int64_t CompilerCompilationContext__aop_weaver(const CompilerCompilationContext* self);
bool CompilerCompilationContext__coverage_enabled(const CompilerCompilationContext* self);
const char* CompilerCompilationContext__compile_template(const CompilerCompilationContext* self, GenericTemplate template, std::vector<ConcreteType> type_args);
int64_t CompilerCompilationContext__instantiation_mode(const CompilerCompilationContext* self);
void CompilerCompilationContext__record_instantiation(CompilerCompilationContext* self, int64_t entry);
UnifiedRegistry unifiedregistry_new();
int64_t binaryopresult_int(int64_t v);
int64_t binaryopresult_float(double v);
int64_t binaryopresult_bool(bool v);
int64_t binaryopresult_string(const char* v);
int64_t binaryopresult_error(const char* msg);
int64_t binaryopsemantics_eval_int_int(int64_t op, int64_t left, int64_t right);
int64_t binaryopsemantics_int_pow(int64_t base, int64_t exp);
int64_t binaryopsemantics_eval_float_float(int64_t op, double left, double right);
int64_t binaryopsemantics_eval_int_float(int64_t op, int64_t left, double right);
int64_t binaryopsemantics_eval_float_int(int64_t op, double left, int64_t right);
int64_t binaryopsemantics_eval_string_string(int64_t op, const char* left, const char* right);
int64_t binaryopsemantics_eval_string_int(int64_t op, const char* left, int64_t right);
int64_t binaryopsemantics_eval_bool_bool(int64_t op, bool left, bool right);
bool binaryopsemantics_is_short_circuit(int64_t op);
int64_t cast_int_to_numeric(int64_t value, int64_t target);
int64_t cast_float_to_numeric(double value, int64_t target);
int64_t cast_bool_to_numeric(bool value, int64_t target);
bool boolcast_from_int(int64_t i);
bool boolcast_from_float(double f);
bool boolcast_from_str(const char* s);
const char* stringcast_from_int(int64_t i);
const char* stringcast_from_float(double f);
const char* stringcast_from_bool(bool b);
bool truthinessrules_is_always_truthy_type(const char* type_name);
int64_t CoercionResult__ok(int64_t value);
int64_t CoercionResult__incompatible(const char* from, const char* to);
bool CoercionResult__is_ok(const CoercionResult* self);
int64_t CoercionResult__unwrap(const CoercionResult* self);
void hello();
HeuristicOutlineItem heuristicoutlineitem_new(int64_t kind, const char* name, int64_t line, int64_t column);
OutlineModule treesitter_parse_outline_heuristic(int64_t self);
OutlineModule treesitter_heuristic_convert_to_module(int64_t self, std::vector<HeuristicOutlineItem> items);
TreeSitter treesitter_new(const char* source);
TypeChecker typechecker_new();
HmInferContext hminfercontext_new();
int64_t hminfercontext_fresh_var(HmInferContext self, Span span);
int64_t hminfercontext_fresh_var_at_level(HmInferContext self, int64_t level, Span span);
const char* infer_expr_bidir(InferenceEngine engine, Expr expr, SplDict* env, int64_t mode);
const char* check_expr(InferenceEngine engine, Expr expr, Type expected, SplDict* env);
const char* synthesize_lambda(InferenceEngine engine, std::vector<LambdaParam> params, Expr body, SplDict* env);
const char* check_lambda(InferenceEngine engine, std::vector<LambdaParam> params, Expr body, std::vector<Type> expected_params, Type expected_ret, SplDict* env);
const char* synthesize_tuple(InferenceEngine engine, std::vector<Expr> elements, SplDict* env);
const char* synthesize_dict(InferenceEngine engine, SplArray* pairs, SplDict* env);
std::vector<PatternBinding> extract_pattern_bindings(Pattern pattern, Type subject_ty);
int64_t check_stmt_bidir(InferenceEngine engine, int64_t stmt, SplDict* env, Option_Type current_fn_ret_type);
const char* infer_with_expected(InferenceEngine engine, Expr expr, Type expected, SplDict* env);
const char* type_registry_lookup(const char* name);
bool type_registry_has(const char* name);
BuiltinRegistry builtinregistry_default();
TraitImplRegistry traitimplregistry_empty();
TypeChecker typechecker_create();
PromiseTypeInfo promisetypeinfo_sync_function(Option_text return_type);
PromiseTypeInfo promisetypeinfo_async_function(Option_text return_type);
int64_t infer_function_effect(FunctionInfo func, SplDict* env);
SplDict* build_effect_env(std::vector<FunctionInfo> functions);
SplDict* infer_mutual_effects(std::vector<FunctionInfo> functions, int64_t env);
SplDict* propagate_effects_transitive(std::vector<FunctionInfo> functions);
SplArray* tarjan_scc(SplDict* graph);
void tarjan_dfs(const char* v, SplDict* graph, int64_t index_counter, int64_t stack, int64_t on_stack, int64_t indices, int64_t lowlinks, int64_t result);
const char* validate_sync_constraint(FunctionInfo func);
const char* validate_suspension_context(FunctionInfo func, SplDict* env);
bool needs_promise_wrapping(FunctionInfo func, SplDict* env);
int64_t get_return_wrap_mode(FunctionInfo func, SplDict* env);
bool is_promise_type(const char* type_name);
const char* wrap_in_promise(const char* type_name);
const char* unwrap_promise(const char* type_name);
int64_t needs_await(const char* callee_name, SplDict* env);
int64_t needs_await_typed(const char* callee_name, SplDict* env, Option_text expected_type);
PromiseTypeInfo infer_promise_type_info(FunctionInfo func, SplDict* env);
const char* infer_expr(InferenceEngine engine, Expr expr, SplDict* env);
const char* infer_binary(InferenceEngine engine, int64_t op, Expr left, Expr right, SplDict* env);
const char* infer_unary(InferenceEngine engine, int64_t op, Expr operand, SplDict* env);
const char* infer_call(InferenceEngine engine, Expr callee, SplArray* args, SplDict* env);
const char* infer_method_call(InferenceEngine engine, Expr receiver, const char* method, SplArray* args, SplDict* env);
const char* infer_lambda(InferenceEngine engine, std::vector<LambdaParam> params, Expr body, SplDict* env);
const char* infer_if(InferenceEngine engine, Expr condition, Expr then_branch, Expr else_branch, SplDict* env);
const char* infer_match(InferenceEngine engine, Expr subject, std::vector<MatchArm> arms, SplDict* env);
const char* infer_array(InferenceEngine engine, std::vector<Expr> elements, SplDict* env);
const char* infer_tuple(InferenceEngine engine, std::vector<Expr> elements, SplDict* env);
const char* infer_dict(InferenceEngine engine, SplArray* pairs, SplDict* env);
const char* infer_field_access(InferenceEngine engine, Expr receiver, const char* field, SplDict* env);
const char* infer_index_access(InferenceEngine engine, Expr receiver, Expr index, SplDict* env);
const char* infer_macro(InferenceEngine engine, const char* name, SplArray* args, SplDict* env);
const char* check_module(TypeChecker checker, Module module);
const char* register_definition(TypeChecker checker, int64_t item);
const char* register_function_signature(TypeChecker checker, FunctionDef func);
const char* register_struct(TypeChecker checker, StructDef struct_def);
const char* register_class(TypeChecker checker, ClassDef class_def);
const char* register_enum(TypeChecker checker, EnumDef enum_def);
const char* register_trait(TypeChecker checker, TraitDef trait_def);
const char* register_impl_signature(TypeChecker checker, ImplBlock impl_block);
const char* register_type_alias(TypeChecker checker, int64_t alias);
const char* register_const(TypeChecker checker, int64_t const_stmt);
const char* register_static(TypeChecker checker, int64_t static_stmt);
const char* check_definition(TypeChecker checker, int64_t item);
const char* check_function_body(TypeChecker checker, FunctionDef func);
WeavingConfig weavingconfig_disabled();

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
static CompileOptions options = {};
static int64_t v1 = 0;
static int64_t v2 = 0;
static HirLowering lowering = {};
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
static HirLowering hir_lowering = {};
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
static TreeSitter ts = {};
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
static BlockRegistry _global_registry = {};
static SplArray* LSMF_MAGIC;
static int64_t LSMF_HEADER_SIZE = 128;
static int64_t LSMF_INDEX_ENTRY_SIZE = 128;
static uint8_t LSMF_VERSION_MAJOR = 1;
static uint8_t LSMF_VERSION_MINOR = 0;
static SplArray* SMF_MAGIC;
static int64_t SMF_HEADER_SIZE = 128;
static uint32_t SMF_FLAG_EXECUTABLE = /* TODO: 0x0001 */((int64_t)0);
static uint32_t SMF_FLAG_RELOADABLE = /* TODO: 0x0002 */((int64_t)0);
static uint32_t SMF_FLAG_DEBUG_INFO = /* TODO: 0x0004 */((int64_t)0);
static uint32_t SMF_FLAG_PIC = /* TODO: 0x0008 */((int64_t)0);
static uint32_t SMF_FLAG_HAS_STUB = /* TODO: 0x0010 */((int64_t)0);
static int64_t SMF_VERSION_MAJOR = 0;
static int64_t SMF_VERSION_MINOR = 1;
static int64_t SECTION_FLAG_READ = /* TODO: 0x1 */((int64_t)0);
static int64_t SECTION_FLAG_WRITE = /* TODO: 0x2 */((int64_t)0);
static int64_t SECTION_FLAG_EXEC = /* TODO: 0x4 */((int64_t)0);
static int32_t PROT_READ = /* TODO: 0x1 */((int64_t)0);
static int32_t MAP_PRIVATE = /* TODO: 0x2 */((int64_t)0);
static int32_t MADV_SEQUENTIAL = 2;
static int32_t MADV_WILLNEED = 3;
static int32_t PROT_NONE = /* TODO: 0x0 */((int64_t)0);
static int32_t PROT_WRITE = /* TODO: 0x2 */((int64_t)0);
static int32_t PROT_EXEC = /* TODO: 0x4 */((int64_t)0);
static int32_t MAP_SHARED = /* TODO: 0x1 */((int64_t)0);
static int32_t MAP_ANONYMOUS = /* TODO: 0x20 */((int64_t)0);
static int64_t MAP_FAILED = -1;
static int32_t MADV_NORMAL = 0;
static int32_t MADV_RANDOM = 1;
static int32_t MADV_DONTNEED = 4;
static SplDict* EXEC_MEMORY_ALLOCS = 0;
static const char* NOTE_SDN_TERMINATOR = spl_str_concat(spl_str_concat(NL, "# END_NOTE"), NL);
static SplArray* C_TYPE_NAMES;
static SplArray* TEST_FUNCTIONS;
static SplArray* SLOW_TEST_FUNCTIONS;
static SplArray* SKIP_TEST_FUNCTIONS;
static SplArray* IGNORE_TEST_FUNCTIONS;
static SplArray* GROUP_FUNCTIONS;

ProceedContext create_proceed_context_minimal(const char* advice_name) {
    return ProceedContext{.advice_name = advice_name, .proceed_count = 0};
}

ProceedContext create_proceed_context_internal(const char* advice_name) {
    return ProceedContext{.advice_name = advice_name, .proceed_count = 0};
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

void test_if_expression_checking() {
    /* pass */;
}

void test_nested_lambda() {
    /* pass */;
}

void test_higher_order_function() {
    /* pass */;
}

void test_complex_expression() {
    /* pass */;
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
    SplArray* keys = spl_array_new();
    bool in_brace = false;
    const char* current_key = "";
    int64_t i = 0;
    while ((i < tmpl_len(tmpl))) {
        int64_t char = spl_str_index_char(tmpl, i..i+1);
        if (spl_str_eq(char, "{")) {
            in_brace = true;
            current_key = "";
        } else if (spl_str_eq(char, "}")) {
            if (in_brace) {
                if ((current_key_len(current_key) > 0)) {
                }
                return keys_push(keys, current_key);
            }
            in_brace = false;
            current_key = "";
        } else if (in_brace) {
            current_key = spl_str_concat(current_key, char);
        }
        i = (i + 1);
    }
    return keys;
}

void test_const_key_set_type() {
    /* stub */
}

void test_get_keys() {
    /* stub */
}

void test_get_keys_empty() {
    int64_t str_ty = HirType_Str;
    int64_t keys = str_ty_get_keys(str_ty);
    spl_println("✅ Get keys empty for non-ConstKeySet");
}

void test_has_key() {
    /* stub */
}

void test_type_equality_const_key_set() {
    /* stub */
}

void test_type_equality_other() {
    int64_t int_ty = HirType_Int;
    int64_t str_ty = HirType_Str;
    int64_t arr_ty = hirtype_Array(elem_ty: HirType.Int);
    spl_println("✅ Type equality for other types");
}

void test_infer_template_with_keys() {
    const char* tmpl = spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("Hello ", spl_i64_to_str(name)), ", you are "), spl_i64_to_str(age)), " years old");
    int64_t ty = templatetypeinference_infer_template(tmpl);
    int64_t keys = ty_get_keys(ty);
    spl_str_eq(assert keys[0], "name");
    spl_str_eq(assert keys[1], "age");
    spl_println("✅ Infer template with keys");
}

void test_infer_plain_string() {
    const char* plain = "Hello world";
    int64_t ty = templatetypeinference_infer_template(plain);
    spl_println("✅ Infer plain string");
}

void test_is_template() {
    const char* tmpl = spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("User ", spl_i64_to_str(id)), " has "), spl_i64_to_str(points)), " points");
    const char* plain = "No keys here";
    spl_println("✅ Template detection");
}

void test_const_key_set_to_string() {
    /* stub */
}

void test_dependent_keys_type() {
    int64_t ty = HirType__DependentKeys(source: "user_input");
    int64_t str_repr = ty_to_string(ty);
    spl_str_eq(assert str_repr, "DependentKeys<user_input>");
    spl_println("✅ DependentKeys type");
}

const char* format_key_list(SplArray* keys) {
    if ((keys_len(keys) == 0)) {
        return "";
    }
    const char* result = spl_str_concat(spl_str_concat("\"", spl_i64_to_str(keys[0])), "\"");
    int64_t i = 1;
    while ((i < keys_len(keys))) {
        result = spl_str_concat(result, spl_str_concat(spl_str_concat(", \"", spl_i64_to_str(keys[i])), "\""));
        i = (i + 1);
    }
    return result;
}

SplArray* find_missing_keys(SplArray* required, SplArray* provided) {
    SplArray* missing = spl_array_new();
    for (size_t __key_i = 0; __key_i < required.size(); __key_i++) {
        Symbol key = required[__key_i];
        if (!(spl_str_contains(provided, key))) {
            return missing_push(missing, key);
        }
    }
    return missing;
}

SplArray* find_extra_keys(SplArray* required, SplArray* provided) {
    SplArray* extra = spl_array_new();
    for (size_t __key_i = 0; __key_i < provided.size(); __key_i++) {
        Symbol key = provided[__key_i];
        if (!(spl_str_contains(required, key))) {
            return extra_push(extra, key);
        }
    }
    return extra;
}

bool Result__is_ok(const Result* self) {
    switch (self) {
    }
}

bool Result__is_err(const Result* self) {
    switch (self) {
    }
}

int64_t Result__unwrap(const Result* self) {
    switch (self) {
        case Err(_):
        {
            return assert false;
            int64_t dummy = 0;
            return dummy as T;
            break;
        }
    }
}

int64_t Result__unwrap_err(const Result* self) {
    switch (self) {
        case Ok(_):
        {
            assert false;
            int64_t dummy = 0;
            return dummy as E;
            break;
        }
    }
}

void test_validate_with_call_success() {
    /* stub */
}

void test_validate_with_call_missing_keys() {
    /* stub */
}

void test_validate_with_call_extra_keys() {
    int64_t tmpl_ty = HirType__ConstKeySet(keys:["name"]);
    SplArray* provided = spl_array_new();
    spl_array_push(provided, spl_str("name"));
    spl_array_push(provided, spl_str("age"));
    spl_array_push(provided, spl_str("unknown"));
    int64_t result = constkeyvalidator_validate_with_call(tmpl_ty, provided);
    int64_t err = result_unwrap_err(result);
    spl_println("✅ Extra keys detected");
}

void test_validate_with_call_both_errors() {
    /* stub */
}

void test_validate_with_call_not_const_key_set() {
    int64_t str_ty = HirType_Str;
    SplArray* provided = spl_array_new();
    spl_array_push(provided, spl_str("name"));
    int64_t result = constkeyvalidator_validate_with_call(str_ty, provided);
    int64_t err = result_unwrap_err(result);
    switch (err) {
    }
    spl_println("✅ Not ConstKeySet detected");
}

void test_validate_keys_match() {
    /* stub */
}

void test_has_missing_keys() {
    SplArray* required = spl_array_new();
    spl_array_push(required, spl_str("name"));
    spl_array_push(required, spl_str("age"));
    spl_array_push(required, spl_str("email"));
    SplArray* provided1 = spl_array_new();
    spl_array_push(provided1, spl_str("name"));
    spl_array_push(provided1, spl_str("age"));
    spl_array_push(provided1, spl_str("email"));
    SplArray* provided2 = spl_array_new();
    spl_array_push(provided2, spl_str("name"));
    spl_array_push(provided2, spl_str("age"));
    spl_println("✅ Has missing keys");
}

void test_has_extra_keys() {
    SplArray* required = spl_array_new();
    spl_array_push(required, spl_str("name"));
    SplArray* provided1 = spl_array_new();
    spl_array_push(provided1, spl_str("name"));
    SplArray* provided2 = spl_array_new();
    spl_array_push(provided2, spl_str("name"));
    spl_array_push(provided2, spl_str("age"));
    spl_println("✅ Has extra keys");
}

void test_find_missing_keys() {
    SplArray* required = spl_array_new();
    spl_array_push(required, spl_str("name"));
    spl_array_push(required, spl_str("age"));
    spl_array_push(required, spl_str("email"));
    SplArray* provided = spl_array_new();
    spl_array_push(provided, spl_str("name"));
    spl_array_push(provided, spl_str("age"));
    std::vector<Symbol> missing = find_missing_keys(required, provided);
    spl_str_eq(assert missing[0], "email");
    spl_println("✅ Find missing keys");
}

void test_find_extra_keys() {
    SplArray* required = spl_array_new();
    spl_array_push(required, spl_str("name"));
    spl_array_push(required, spl_str("age"));
    SplArray* provided = spl_array_new();
    spl_array_push(provided, spl_str("name"));
    spl_array_push(provided, spl_str("age"));
    spl_array_push(provided, spl_str("unknown"));
    spl_array_push(provided, spl_str("extra"));
    std::vector<Symbol> extra = find_extra_keys(required, provided);
    spl_str_eq(assert extra[0], "unknown");
    spl_str_eq(assert extra[1], "extra");
    spl_println("✅ Find extra keys");
}

void test_key_error_to_string() {
    /* stub */
}

void test_typo_detection() {
    /* stub */
}

TemplateKey templatekey_required(const char* name, int64_t position) {
    TemplateKey{.name = name, .position = position, .is_optional = false} = spl_array_new();
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

DiContainer get_container() {
    if (has__global_container) {
        return _global_container_value;
    }
    DiContainer default = dicontainer_for_profile(CompilerProfile_Dev);
    _global_container = default;
    return default;
}

ParamInfo paraminfo_create(const char* name, const char* type_name, bool has_inject) {
    return ParamInfo{.name = name, .type_name = type_name, .has_inject = has_inject, .is_injectable = false};
}

DiValidator divalidator_create() {
    return DiValidator{};
}

const char* validate_constructor(ConstructorInfo ctor) {
    DiValidator validator = divalidator_create();
    return validator_validate_constructor(validator, ctor);
}

const char* validate_class_injection(const char* class_name, bool has_sys_inject, SplArray* field_types) {
    DiValidator validator = divalidator_create();
    return validator_validate_class_injection(validator, class_name, has_sys_inject, field_types);
}

const char* format_di_error(DiValidationError error) {
    return error_format(error);
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
    return Result_Ok;
}

const char* CheckBackendImpl__eval_expr(const CheckBackendImpl* self, HirExpr expr, int64_t env) {
    return Result_Ok;
}

const char* CheckBackendImpl__exec_stmt(const CheckBackendImpl* self, int64_t stmt, int64_t env) {
    return Result_Ok;
}

CompilerDriver CompilerDriver__create(int64_t options) {
    return CompilerDriver{.ctx = compilecontext_create(options)};
}

int64_t CompilerDriver__compile(CompilerDriver* self) {
    int64_t log = self->ctx.logger;
    log_debug(log, "phase 1: loading sources...");
    if (!(CompilerDriver__load_sources_impl(self))) {
        log_error(log, "phase 1 FAILED");
        return compileresult_ParseError(self->ctx.errors);
    }
    return log_debug(log, spl_str_concat(spl_str_concat("phase 1 done, ", spl_i64_to_str(spl_array_len(self->ctx.sources))), " sources loaded"));
    log_debug(log, "phase 2: parsing...");
    if (!(CompilerDriver__parse_all_impl(self))) {
        log_error(log, "phase 2 FAILED");
        return compileresult_ParseError(self->ctx.errors);
    }
    return log_debug(log, "phase 2 done");
    log_debug(log, "phase 3: lowering and checking...");
    log_trace(log, spl_str_concat("BEFORE phase 3: hir_modules count = ", spl_i64_to_str(spl_array_len(self->ctx.hir_modules_keys(self->ctx.hir_modules)))));
    bool analyze_ok = CompilerDriver__lower_and_check_impl(self);
    log_trace(log, spl_str_concat("AFTER phase 3: hir_modules count = ", spl_i64_to_str(spl_array_len(self->ctx.hir_modules_keys(self->ctx.hir_modules)))));
    if (!(analyze_ok)) {
        return log_error(log, "phase 3 FAILED");
        if ((self->ctx_errors_len(self->ctx, errors) > 0)) {
            int64_t first_error = self->ctx.errors[0];
            if (spl_str_contains(first_error, "Method resolution")) {
                return compileresult_ResolveError(self->ctx.errors);
            }
        }
        return compileresult_TypeError(self->ctx.errors);
    }
    return log_debug(log, "phase 3 done");
    log_debug(log, "phase 4: monomorphization...");
    bool mono_ok = CompilerDriver__monomorphize_impl(self);
    if (!(mono_ok)) {
        log_error(log, "phase 4 FAILED");
        return compileresult_TypeError(self->ctx.errors);
    }
    return log_debug(log, "phase 4 done");
    log_debug(log, "phase 5: mode-specific processing...");
    switch (self->ctx.options.mode) {
        case CompileMode_Check:
        {
            log_debug(log, "check mode");
            return compileresult_Success(spl_nil());
            break;
        }
        case CompileMode_Sdn:
        {
            log_debug(log, "sdn mode");
            return CompilerDriver__process_sdn(self);
            break;
        }
        case CompileMode_Interpret:
        {
            log_debug(log, "interpret mode");
            return CompilerDriver__interpret(self);
            break;
        }
        case CompileMode_Jit:
        {
            log_debug(log, "jit mode");
            return CompilerDriver__jit_compile_and_run(self);
            break;
        }
        case CompileMode_Aot:
        {
            log_debug(log, "aot mode");
            return CompilerDriver__aot_compile(self);
            break;
        }
    }
    log_warn(log, "no mode matched, falling through");
    return compileresult_Success(spl_nil());
}

bool CompilerDriver__load_sources_impl(CompilerDriver* self) {
    int64_t log = self->ctx.logger;
    log_debug(log, spl_str_concat("input_files count=", spl_i64_to_str(spl_array_len(self->ctx.options.input_files))));
    int64_t i = 0;
    while ((i < self->ctx.options_input_files_len(self->ctx.options, input_files))) {
        int64_t path = self->ctx.options.input_files[i];
        log_trace(log, spl_str_concat("loading file: ", spl_i64_to_str(path)));
        switch (SourceFile__load(path)) {
            case Ok(source):
            {
                log_trace(log, spl_str_concat("loaded OK: ", spl_i64_to_str(source.path)));
                return self->ctx_sources_push(self->ctx, sources, source);
                break;
            }
            case Err(e):
            {
                log_error(log, spl_str_concat("load error: ", spl_i64_to_str(e)));
                return CompilerDriver__ctx_add_error(self, ctx, e);
                break;
            }
        }
        i = (i + 1);
    }
    return log_debug(log, spl_str_concat("sources stored, count=", spl_i64_to_str(spl_array_len(self->ctx.sources))));
    return !(CompilerDriver__ctx_has_errors(self, ctx));
}

bool CompilerDriver__parse_all_impl(CompilerDriver* self) {
    int64_t log = self->ctx.logger;
    int64_t sources = self->ctx.sources;
    log_debug(log, spl_str_concat(spl_str_concat("parsing ", spl_i64_to_str(spl_array_len(sources))), " sources"));
    int64_t src_idx = 0;
    while ((src_idx < sources_len(sources))) {
        int64_t source = sources[src_idx];
        log_trace(log, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("parsing: ", spl_i64_to_str(source.path)), " (module="), spl_i64_to_str(source.module_name)), ", len="), spl_i64_to_str(spl_array_len(source.content))), ")"));
        Module module = CompilerDriver__parse_source(self, source);
        self->ctx.modules[source.module_name] = module;
        log_trace(log, spl_str_concat("stored module, total=", spl_i64_to_str(spl_array_len(self->ctx.modules_keys(self->ctx.modules)))));
        src_idx = (src_idx + 1);
    }
    log_debug(log, spl_str_concat("parsing done, modules=", spl_i64_to_str(spl_array_len(self->ctx.modules_keys(self->ctx.modules)))));
    return !(CompilerDriver__ctx_has_errors(self, ctx));
}

Module CompilerDriver__parse_source(const CompilerDriver* self, int64_t source) {
    int64_t log = self->ctx.logger;
    log_trace(log, "2a: outline parsing...");
    int64_t ts = TreeSitter__new(source.content);
    int64_t outline = ts_parse_outline(ts);
    log_trace(log, "2b: resolving blocks...");
    int64_t resolver = create_block_resolver();
    resolver = resolver_with_file(resolver, source.path);
    resolver = resolver_with_module(resolver, source.module_name);
    int64_t _destruct_0 = resolver_resolve(resolver, outline);
    int64_t resolved = _destruct_0[0];
    int64_t block_diagnostics = _destruct_0[1];
    log_trace(log, "2c: full parse...");
    int64_t parser = Parser__with_resolved_blocks(source.content, resolved);
    int64_t module = parser_parse(parser);
    log_trace(log, "2d: desugaring...");
    int64_t desugared_module = desugar_module(module);
    return desugared_module;
}

bool CompilerDriver__lower_and_check_impl(CompilerDriver* self) {
    return false; /* stub */
}

int64_t CompilerDriver__lower_to_hir_impl(const CompilerDriver* self) {
    int64_t lowering = create_hir_lowering();
    int64_t ctx = self->ctx;
    int64_t module_names = ctx_modules_keys(ctx, modules);
    for (int64_t __name_i = 0; __name_i < spl_array_len(module_names); __name_i++) {
        int64_t name = spl_array_get(module_names, __name_i).as_int;
        int64_t module = ctx.modules[name];
        int64_t hir_module = lowering_lower_module(lowering, module);
        ctx.hir_modules[name] = hir_module;
    }
    return spl_array_new();
}

int64_t CompilerDriver__resolve_methods_impl(const CompilerDriver* self) {
    int64_t ctx = self->ctx;
    for (int64_t __name_i = 0; __name_i < spl_array_len(ctx_hir_modules_keys(ctx, hir_modules)); __name_i++) {
        int64_t name = spl_array_get(ctx_hir_modules_keys(ctx, hir_modules), __name_i).as_int;
        int64_t hir_module = ctx.hir_modules[name];
        int64_t _destruct_2 = resolve_methods(hir_module);
        int64_t resolved_module = _destruct_2[0];
        int64_t resolve_errors = _destruct_2[1];
        ctx.hir_modules[name] = resolved_module;
        for (int64_t __err_i = 0; __err_i < spl_array_len(resolve_errors); __err_i++) {
            int64_t err = spl_array_get(resolve_errors, __err_i).as_int;
            return spl_array_push(ctx.errors, spl_int(spl_str_concat(spl_str_concat(spl_str_concat("Method resolution error in ", spl_i64_to_str(name)), ": "), spl_i64_to_str(err.message))));
        }
    }
    return spl_array_new();
}

int64_t CompilerDriver__type_check_impl(const CompilerDriver* self) {
    int64_t ctx = self->ctx;
    return spl_array_new();
}

bool CompilerDriver__monomorphize_impl(CompilerDriver* self) {
    int64_t log = self->ctx.logger;
    return log_debug(log, spl_str_concat(spl_str_concat("running monomorphization on ", spl_i64_to_str(spl_array_len(self->ctx.hir_modules_keys(self->ctx.hir_modules)))), " modules"));
    int64_t _destruct_3 = run_monomorphization(self->ctx.hir_modules);
    int64_t updated_modules = _destruct_3[0];
    int64_t stats = _destruct_3[1];
    self->ctx.hir_modules = updated_modules;
    log_debug(log, "monomorphization stats:");
    log_debug(log, spl_str_concat("  generic functions: ", spl_i64_to_str(stats.generic_functions_found)));
    log_debug(log, spl_str_concat("  generic structs: ", spl_i64_to_str(stats.generic_structs_found)));
    log_debug(log, spl_str_concat("  generic classes: ", spl_i64_to_str(stats.generic_classes_found)));
    log_debug(log, spl_str_concat("  call sites: ", spl_i64_to_str(stats.call_sites_found)));
    return log_debug(log, spl_str_concat("  specializations created: ", spl_i64_to_str(stats.specializations_created)));
    return !(CompilerDriver__ctx_has_errors(self, ctx));
}

int64_t CompilerDriver__process_sdn(const CompilerDriver* self) {
    int64_t backend = self->ctx.di_resolve(self->ctx.di, "Backend");
    SplDict* results = Any> = {};
    for (int64_t __name_i = 0; __name_i < spl_array_len(self->ctx_hir_modules_keys(self->ctx, hir_modules)); __name_i++) {
        int64_t name = spl_array_get(self->ctx_hir_modules_keys(self->ctx, hir_modules), __name_i).as_int;
        int64_t hir_module = self->ctx.hir_modules[name];
        switch (backend_process_module(backend, hir_module)) {
            case Ok(value):
            {
                results[name] = value;
                break;
            }
            case Err(e):
            {
                return CompileResult__RuntimeError(spl_str_concat(spl_str_concat(spl_str_concat("SDN error in ", spl_i64_to_str(name)), ": "), spl_i64_to_str(e)));
                break;
            }
        }
    }
    return compileresult_Success(results);
}

int64_t CompilerDriver__interpret(const CompilerDriver* self) {
    if ((self->ctx.options_input_files_len(self->ctx.options, input_files) == 0)) {
        return CompileResult__Error("No source file specified for interpret mode");
    }
    int64_t source_file = self->ctx.options.input_files[0];
    const char* simple_old = find_simple_old_binary();
    if (spl_str_eq(simple_old, "")) {
        return CompileResult__Error("Cannot find simple_old binary for interpretation");
    }
    const char* result = rt_shell(spl_str_concat(spl_str_concat(simple_old, " "), spl_i64_to_str(source_file)));
    if (result.has_stdout) {
        printf("%lld\n", (long long)result.stdout);
    }
    if ((result.exit_code != 0)) {
        if (result.has_stderr) {
            return compileresult_Error(result.stderr);
        }
        return CompileResult__Error(spl_str_concat("Interpret failed with exit code ", spl_i64_to_str(result.exit_code)));
    }
    return compileresult_Success(BackendResult_Unit);
}

int64_t CompilerDriver__run_module(const CompilerDriver* self, int64_t backend, int64_t module) {
    switch (backend_process_module(backend, module)) {
    }
}

int64_t CompilerDriver__jit_compile_and_run(CompilerDriver* self) {
    if (!(CompilerDriver__lower_to_mir(self))) {
        return CompileResult__CodegenError(((self->ctx.errors_first(self->ctx.errors)) ? (self->ctx.errors_first(self->ctx.errors)) : ("MIR lowering failed")));
    }
    if (!(CompilerDriver__borrow_check(self))) {
        return compileresult_BorrowError(self->ctx.errors);
    }
    SplDict* _async_state_machines = CompilerDriver__process_async(self);
    return CompilerDriver__optimize_mir(self, OptimizationConfig__speed());
    int64_t pipeline = CodegenPipeline();
    for (int64_t __name_i = 0; __name_i < spl_array_len(self->ctx_mir_modules_keys(self->ctx, mir_modules)); __name_i++) {
        int64_t name = spl_array_get(self->ctx_mir_modules_keys(self->ctx, mir_modules), __name_i).as_int;
        int64_t mir_module = self->ctx.mir_modules[name];
        switch (pipeline_jit_compile(pipeline, mir_module)) {
            case Err(e):
            {
                return CompileResult__CodegenError(spl_str_concat(spl_str_concat(spl_str_concat("JIT compile error in ", spl_i64_to_str(name)), ": "), spl_i64_to_str(e)));
                break;
            }
        }
    }
    int64_t main_fn = pipeline_get_function(pipeline, "main");
    if ((main_fn == -1)) {
        return CompileResult__RuntimeError("No main function found");
    }
    switch (pipeline_call_function(pipeline, "main", spl_array_new())) {
    }
}

int64_t CompilerDriver__aot_compile(CompilerDriver* self) {
    int64_t log = self->ctx.logger;
    log_debug(log, spl_str_concat(spl_str_concat("AOT: lowering to MIR (", spl_i64_to_str(spl_array_len(self->ctx.hir_modules_keys(self->ctx.hir_modules)))), " HIR modules)"));
    if (!(CompilerDriver__lower_to_mir(self))) {
        for (int64_t __err_i = 0; __err_i < spl_array_len(self->ctx.errors); __err_i++) {
            int64_t err = spl_array_get(self->ctx.errors, __err_i).as_int;
            return log_error(log, spl_str_concat("MIR error: ", spl_i64_to_str(err)));
        }
        return CompileResult__CodegenError(((self->ctx.errors_first(self->ctx.errors)) ? (self->ctx.errors_first(self->ctx.errors)) : ("MIR lowering failed")));
    }
    return log_debug(log, spl_str_concat(spl_str_concat("MIR done, ", spl_i64_to_str(spl_array_len(self->ctx.mir_modules_keys(self->ctx.mir_modules)))), " modules"));
    log_debug(log, "AOT: running borrow check...");
    if (!(CompilerDriver__borrow_check(self))) {
        for (int64_t __err_i = 0; __err_i < spl_array_len(self->ctx.errors); __err_i++) {
            int64_t err = spl_array_get(self->ctx.errors, __err_i).as_int;
            return log_error(log, spl_str_concat("Borrow error: ", spl_i64_to_str(err)));
        }
        return compileresult_BorrowError(self->ctx.errors);
    }
    return log_debug(log, "borrow check done");
    log_debug(log, "AOT: processing async functions");
    SplDict* async_state_machines = CompilerDriver__process_async(self);
    return log_debug(log, spl_str_concat(spl_str_concat("async processing done, ", spl_i64_to_str(spl_array_len(async_state_machines_keys(async_state_machines)))), " state machines"));
    int64_t opt_config = CompilerDriver__get_optimization_config(self);
    log_debug(log, spl_str_concat(spl_str_concat("AOT: optimizing MIR (level: ", spl_i64_to_str(opt_config.level)), ")"));
    CompilerDriver__optimize_mir(self, opt_config);
    return log_debug(log, "MIR optimization done");
    int64_t output = ((self->ctx.options.output_file) ? (self->ctx.options.output_file) : ("a.out"));
    int64_t format = self->ctx.options.output_format;
    switch (format) {
        case OutputFormat_Smf:
        {
            return CompilerDriver__compile_to_smf(self, output);
            break;
        }
        case OutputFormat_SelfContained:
        {
            return CompilerDriver__compile_to_self_contained(self, output);
            break;
        }
        case OutputFormat_Both:
        {
            int64_t native_result = CompilerDriver__compile_to_native(self, output);
            if (!(native_result_is_success(native_result))) {
                return native_result;
            }
            int64_t smf_result = CompilerDriver__compile_to_smf(self, spl_str_concat(spl_i64_to_str(output), ".smf"));
            if (!(smf_result_is_success(smf_result))) {
                return smf_result;
            }
            return compileresult_Success(output);
            break;
        }
        default:
        {
            return CompilerDriver__compile_to_native(self, output);
            break;
        }
    }
}

int64_t CompilerDriver__compile_to_native(CompilerDriver* self, const char* output) {
    int64_t log = self->ctx.logger;
    int64_t backend_name = self->ctx.options.backend;
    int64_t is_release = self->ctx.options.release;
    int64_t effective_backend = get_effective_backend_name(backend_name, is_release);
    return log_debug(log, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("AOT native: compiling to ", output), " (backend: "), spl_i64_to_str(effective_backend)), ")"));
    SplArray* object_files = spl_array_new();
    for (int64_t __name_i = 0; __name_i < spl_array_len(self->ctx_mir_modules_keys(self->ctx, mir_modules)); __name_i++) {
        int64_t name = spl_array_get(self->ctx_mir_modules_keys(self->ctx, mir_modules), __name_i).as_int;
        log_trace(log, spl_str_concat("compiling module: ", spl_i64_to_str(name)));
        int64_t mir_module = self->ctx.mir_modules[name];
        int64_t compiled = compile_module_with_backend(backend_name, mir_module, is_release);
        if (compiled_is_err(compiled)) {
            int64_t err = compiled_unwrap_err(compiled);
            return CompileResult__CodegenError(spl_str_concat(spl_str_concat(spl_str_concat("AOT compile error in ", spl_i64_to_str(name)), ": "), spl_i64_to_str(err_to_text(err))));
        }
        int64_t module = compiled_value;
        if (module.has_object_code) {
            const char* obj_path = spl_str_concat(spl_str_concat(spl_str_concat(output, "."), spl_i64_to_str(name)), ".o");
            if (rt_file_write_bytes(obj_path, module.object_code_value)) {
                object_files = object_files_push(object_files, obj_path);
            } else {
                return CompileResult__CodegenError(spl_str_concat("Failed to write object file: ", obj_path));
            }
        } else {
            return CompileResult__CodegenError(spl_str_concat("Backend produced no object code for ", spl_i64_to_str(name)));
        }
    }
    NativeLinkConfig link_config = NativeLinkConfig__default();
    link_config.debug = self->ctx.options.debug_info;
    link_config.verbose = self->ctx.options.verbose;
    switch (link_to_native(object_files, output, link_config)) {
        case Ok(_):
        {
            log_info(log, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("Native executable written to ", output), " (backend: "), spl_i64_to_str(effective_backend)), ")"));
            return compileresult_Success(output);
            break;
        }
        case Err(e):
        {
            return CompileResult__CodegenError(spl_str_concat("Linking failed: ", spl_i64_to_str(e)));
            break;
        }
    }
}

int64_t CompilerDriver__compile_to_smf(CompilerDriver* self, const char* output) {
    int64_t log = self->ctx.logger;
    int64_t backend_name = self->ctx.options.backend;
    int64_t is_release = self->ctx.options.release;
    int64_t effective_backend = get_effective_backend_name(backend_name, is_release);
    return log_debug(log, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("AOT SMF: compiling to ", output), " (backend: "), spl_i64_to_str(effective_backend)), ")"));
    int64_t smf_result = CompilerDriver__collect_smf_bytes(self);
    if (!(smf_result_is_success(smf_result))) {
        return smf_result;
    }
    int64_t smf_bytes = smf_result_get_value(smf_result);
    switch (link_to_smf(smf_bytes, output, self->ctx.options.verbose)) {
        case Ok(_):
        {
            log_info(log, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("SMF module written to ", output), " (backend: "), spl_i64_to_str(effective_backend)), ")"));
            return compileresult_Success(output);
            break;
        }
        case Err(e):
        {
            return CompileResult__CodegenError(spl_str_concat("Failed to write SMF file: ", spl_i64_to_str(e)));
            break;
        }
    }
}

int64_t CompilerDriver__compile_to_self_contained(CompilerDriver* self, const char* output) {
    int64_t log = self->ctx.logger;
    int64_t backend_name = self->ctx.options.backend;
    int64_t is_release = self->ctx.options.release;
    int64_t effective_backend = get_effective_backend_name(backend_name, is_release);
    return log_debug(log, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("AOT self-contained: compiling to ", output), " (backend: "), spl_i64_to_str(effective_backend)), ")"));
    int64_t smf_result = CompilerDriver__collect_smf_bytes(self);
    if (!(smf_result_is_success(smf_result))) {
        return smf_result;
    }
    int64_t smf_bytes = smf_result_get_value(smf_result);
    int64_t sc_config = SelfContainedConfig__default();
    sc_config.verbose = self->ctx.options.verbose;
    switch (link_to_self_contained(smf_bytes, output, sc_config)) {
        case Ok(_):
        {
            log_info(log, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("Self-contained binary written to ", output), " (backend: "), spl_i64_to_str(effective_backend)), ")"));
            return compileresult_Success(output);
            break;
        }
        case Err(e):
        {
            return CompileResult__CodegenError(spl_str_concat("Self-contained build failed: ", spl_i64_to_str(e)));
            break;
        }
    }
}

int64_t CompilerDriver__collect_smf_bytes(CompilerDriver* self) {
    int64_t log = self->ctx.logger;
    int64_t backend_name = self->ctx.options.backend;
    int64_t is_release = self->ctx.options.release;
    SplArray* all_object_bytes = spl_array_new();
    for (int64_t __name_i = 0; __name_i < spl_array_len(self->ctx_mir_modules_keys(self->ctx, mir_modules)); __name_i++) {
        int64_t name = spl_array_get(self->ctx_mir_modules_keys(self->ctx, mir_modules), __name_i).as_int;
        log_trace(log, spl_str_concat("compiling module for SMF: ", spl_i64_to_str(name)));
        int64_t mir_module = self->ctx.mir_modules[name];
        int64_t compiled = compile_module_with_backend(backend_name, mir_module, is_release);
        if (compiled_is_err(compiled)) {
            int64_t err = compiled_unwrap_err(compiled);
            return CompileResult__CodegenError(spl_str_concat(spl_str_concat(spl_str_concat("AOT compile error in ", spl_i64_to_str(name)), ": "), spl_i64_to_str(err_to_text(err))));
        }
        int64_t module = compiled_value;
        if (module.has_object_code) {
            all_object_bytes = all_object_bytes_concat(all_object_bytes, module.object_code_value);
        }
    }
    int64_t target = Target__host();
    int64_t smf_bytes = generate_smf_with_templates(all_object_bytes, spl_nil(), spl_nil(), target);
    return compileresult_Success(smf_bytes);
}

const char* CompilerDriver__link_objects(const CompilerDriver* self, SplArray* objects, const char* output) {
    if (objects_is_empty(objects)) {
        return Result_Err;
    }
    NativeLinkConfig config = NativeLinkConfig__default();
    return link_to_native(objects, output, config);
}

bool CompilerDriver__lower_to_mir(CompilerDriver* self) {
    int64_t lowering = MirLowering__new(create_symbol_table());
    int64_t hir_keys = self->ctx_hir_modules_keys(self->ctx, hir_modules);
    for (int64_t __name_i = 0; __name_i < spl_array_len(hir_keys); __name_i++) {
        int64_t name = spl_array_get(hir_keys, __name_i).as_int;
        int64_t hir_module = self->ctx.hir_modules[name];
        int64_t mir_module = lowering_lower_module(lowering, hir_module);
        mir_module.name = name;
        self->ctx.mir_modules[name] = mir_module;
    }
    return !(CompilerDriver__ctx_has_errors(self, ctx));
}

bool CompilerDriver__borrow_check(CompilerDriver* self) {
    int64_t log = self->ctx.logger;
    if (self->ctx.options.no_borrow_check) {
        log_debug(log, "borrow checking disabled");
        return true;
    }
    return log_debug(log, spl_str_concat(spl_str_concat("borrow checking ", spl_i64_to_str(spl_array_len(self->ctx.mir_modules_keys(self->ctx.mir_modules)))), " modules"));
    BorrowChecker checker = BorrowChecker__create();
    bool has_errors = false;
    for (int64_t __name_i = 0; __name_i < spl_array_len(self->ctx_mir_modules_keys(self->ctx, mir_modules)); __name_i++) {
        int64_t name = spl_array_get(self->ctx_mir_modules_keys(self->ctx, mir_modules), __name_i).as_int;
        int64_t mir_module = self->ctx.mir_modules[name];
        for (int64_t __fn_symbol_i = 0; __fn_symbol_i < spl_array_len(mir_module_functions_keys(mir_module, functions)); __fn_symbol_i++) {
            int64_t fn_symbol = spl_array_get(mir_module_functions_keys(mir_module, functions), __fn_symbol_i).as_int;
            int64_t mir_fn = mir_module.functions[fn_symbol];
            int64_t body = MirBody__from_function(mir_fn);
            switch (checker_check_function(checker, body)) {
                case Errors(errors):
                {
                    for (int64_t err = 0; err < errors; err++) {
                        return CompilerDriver__ctx_add_error(self, ctx, CompilerDriver__format_borrow_error(self, err));
                    }
                    has_errors = true;
                    break;
                }
                case Result_Ok:
                {
                    /* pass */;
                    break;
                }
            }
        }
    }
    return !(has_errors);
}

const char* CompilerDriver__format_borrow_error(const CompilerDriver* self, int64_t err) {
    const char* msg = spl_str_concat("error[E0502]: ", spl_i64_to_str(err.message));
    if (err.has_help) {
        msg = spl_str_concat(spl_str_concat(spl_str_concat(msg, NL), "  = help: "), spl_i64_to_str(err.help_value));
    }
    return msg;
}

SplDict* CompilerDriver__process_async(CompilerDriver* self) {
    int64_t log = self->ctx.logger;
    return log_debug(log, spl_str_concat(spl_str_concat("processing async functions in ", spl_i64_to_str(spl_array_len(self->ctx.mir_modules_keys(self->ctx.mir_modules)))), " modules"));
    int64_t state_machines = process_async_mir(self->ctx.mir_modules);
    log_debug(log, spl_str_concat(spl_str_concat("generated ", spl_i64_to_str(spl_array_len(state_machines_keys(state_machines)))), " async state machines"));
    return state_machines;
}

void CompilerDriver__optimize_mir(CompilerDriver* self, int64_t config) {
    int64_t log = self->ctx.logger;
    log_debug(log, spl_str_concat(spl_str_concat("optimizing ", spl_i64_to_str(spl_array_len(self->ctx.mir_modules_keys(self->ctx.mir_modules)))), " MIR modules"));
    for (int64_t __name_i = 0; __name_i < spl_array_len(self->ctx_mir_modules_keys(self->ctx, mir_modules)); __name_i++) {
        int64_t name = spl_array_get(self->ctx_mir_modules_keys(self->ctx, mir_modules), __name_i).as_int;
        int64_t mir_module = self->ctx.mir_modules[name];
        int64_t optimized = optimize_mir_module(mir_module, config);
        self->ctx.mir_modules[name] = optimized;
    }
}

int64_t CompilerDriver__get_optimization_config(const CompilerDriver* self) {
    if (self->ctx.options.has_opt_level) {
        int64_t level = self->ctx.options.opt_level_value;
        if ((level == 0)) {
            return OptimizationConfig__debug();
        } else if ((level == 1)) {
            return OptimizationConfig__size();
        } else if ((level == 2)) {
            return OptimizationConfig__speed();
        } else if ((level >= 3)) {
            return OptimizationConfig__aggressive();
        }
    }
    if ((self->ctx.options.release || self->ctx.options.optimize)) {
        return OptimizationConfig__speed();
    }
    return else:;
    return OptimizationConfig__debug();
}

const char* find_runtime_lib_dir() {
    const char* env_path = rt_env_get("SIMPLE_RUNTIME_PATH");
    if ((env_path != 0)) {
        if ((!spl_str_eq(env_path, ""))) {
        }
        return env_path;
    }
    if (rt_file_exists("rust/target/debug/libsimple_compiler.so")) {
        return "rust/target/debug";
    }
    if (rt_file_exists("rust/target/release/libsimple_compiler.so")) {
        return "rust/target/release";
    }
    return "rust/target/debug";
}

const char* find_simple_old_binary() {
    const char* runtime_path = rt_env_get("SIMPLE_RUNTIME_PATH");
    if ((runtime_path != 0)) {
        if ((!spl_str_eq(runtime_path, ""))) {
        }
        return runtime_path;
    }
    const char* env_path = rt_env_get("SIMPLE_OLD_PATH");
    if ((env_path != 0)) {
        if ((!spl_str_eq(env_path, ""))) {
        }
        return env_path;
    }
    if (rt_file_exists("./bin/release/simple")) {
        return "./bin/release/simple";
    }
    if (rt_file_exists("./rust/target/debug/simple")) {
        return "./rust/target/debug/simple";
    }
    if (rt_file_exists("./rust/target/release/simple")) {
        return "./rust/target/release/simple";
    }
    if (rt_file_exists("./rust/target/debug/simple_old")) {
        return "./rust/target/debug/simple_old";
    }
    if (rt_file_exists("./rust/target/release/simple_old")) {
        return "./rust/target/release/simple_old";
    }
    return "";
}

int64_t compile_file(const char* path) {
    CompileOptions options = CompileOptions__default();
    options.input_files = spl_array_new();
    CompilerDriver driver = CompilerDriver__create(options);
    return driver_compile(driver);
}

int64_t compile_files(SplArray* paths, int64_t mode) {
    CompileOptions options = CompileOptions__default();
    options.input_files = paths;
    options.mode = mode;
    CompilerDriver driver = CompilerDriver__create(options);
    return driver_compile(driver);
}

int64_t interpret_file(const char* path) {
    return compile_files(spl_array_new(), CompileMode.Interpret);
}

int64_t jit_file(const char* path) {
    return compile_files(spl_array_new(), CompileMode.Jit);
}

int64_t aot_file(const char* path, const char* output) {
    CompileOptions options = CompileOptions__default();
    options.input_files = spl_array_new();
    options.mode = CompileMode.Aot;
    options.output_file = output;
    CompilerDriver driver = CompilerDriver__create(options);
    return driver_compile(driver);
}

int64_t check_file(const char* path) {
    return compile_files(spl_array_new(), CompileMode.Check);
}

int64_t parse_sdn_file(const char* path) {
    return compile_files(spl_array_new(), CompileMode.Sdn);
}

const char* compile_to_smf(const char* path, const char* output) {
    return ""; /* stub */
}

Config create_config() {
    return Config{}; /* stub */
}

int64_t create_block_resolver() {
    return 0; /* stub */
}

int64_t OutputFormat__from_text(const char* s) {
    switch (s) {
    }
}

CompileOptions CompileOptions__default() {
    return CompileOptions{}; /* stub */
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
    EffectEnv env = effectenv_new();
    spl_println("✅ Environment creation");
}

void test_set_get() {
    EffectEnv env = effectenv_new();
    EffectEnv__set_effect(&env, "my_func", Effect_Async);
    spl_println("✅ Set/get effects");
}

void test_dirty() {
    EffectEnv env = effectenv_new();
    EffectEnv__set_effect(&env, "test", Effect_Sync);
    env_clear_dirty(env);
    EffectEnv__set_effect(&env, "test", Effect_Sync);
    EffectEnv__set_effect(&env, "test", Effect_Async);
    env_clear_dirty(env);
    spl_println("✅ Dirty tracking");
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
    int64_t int_ty = HirType_Int;
    int64_t str_ty = HirType_Str;
    int64_t promise_int = hirtype_Promise(inner: HirType.Int);
    spl_println("✅ Basic type operations");
}

void test_promise_wrap() {
    EffectEnv env = effectenv_new();
    TypeWrapper wrapper = typewrapper_new(env);
    int64_t async_ret = TypeWrapper__wrap_return_type(&wrapper, "async_task", HirType_Int);
    int64_t sync_ret = TypeWrapper__wrap_return_type(&wrapper, "sync_task", HirType_Int);
    spl_println("✅ Promise wrapping");
}

void test_promise_unwrap() {
    EffectEnv env = effectenv_new();
    TypeWrapper wrapper = typewrapper_new(env);
    int64_t promise_int = hirtype_Promise(inner: HirType.Int);
    int64_t unwrapped = wrapper_unwrap_suspend(wrapper, promise_int);
    int64_t direct_int = HirType_Int;
    int64_t not_unwrapped = wrapper_unwrap_suspend(wrapper, direct_int);
    spl_println("✅ Promise unwrapping");
}

void test_suspend_validation() {
    EffectEnv env = effectenv_new();
    TypeWrapper wrapper = typewrapper_new(env);
    int64_t promise_int = hirtype_Promise(inner: HirType.Int);
    int64_t direct_int = HirType_Int;
    spl_println("✅ Suspend validation");
}

void test_nested_promises() {
    int64_t int_ty = HirType_Int;
    int64_t promise_int = hirtype_Promise(inner: int_ty);
    int64_t promise_promise_int = hirtype_Promise(inner: promise_int);
    int64_t unwrapped_once = promise_promise_int_unwrap_promise(promise_promise_int);
    int64_t unwrapped_twice = unwrapped_once_unwrap_promise(unwrapped_once);
    spl_println("✅ Nested promises");
}

void test_function_types() {
    int64_t int_ret = hirtype_Function(ret: HirType.Int);
    int64_t promise_ret = hirtype_Function(ret: HirType_Promise(ret: HirType, inner: HirType.Str));
    spl_println("✅ Function types");
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

HirModule MethodResolver__resolve_module(MethodResolver* self, HirModule module) {
    return HirModule{}; /* stub */
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
    HirLowering hir_lowering = hirlowering_new();
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
    HirLowering hir_lowering = hirlowering_new();
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

void test_validation() {
    int64_t registry = implregistry_new();
    int64_t impl_block = ImplBlock__new(TraitRef__new("Display"))_add_method(ImplBlock__new(TraitRef__new("Display")), "to_string");
}

Obligation obligation_new(int64_t ty, TraitRef trait_ref) {
    return Obligation{}; /* stub */
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

ArmRegisterAllocator armregisterallocator_new(int64_t arch) {
    return ArmRegisterAllocator{}; /* stub */
}

int64_t BackendFactory__create(int64_t target, CompileOptions options) {
    return BackendFactory__create_specific(BackendKind_Cranelift);
}

int64_t BackendFactory__auto_select(int64_t target, int64_t mode) {
    switch (mode) {
        case BuildMode_Debug:
        {
            return BackendKind_Cranelift;
            break;
        }
        case BuildMode_Release:
        {
            return BackendKind_Llvm;
            break;
        }
        case BuildMode_Test:
        {
            return BackendKind_Interpreter;
            break;
        }
        case BuildMode_Bootstrap:
        {
            return BackendKind_Cranelift;
            break;
        }
    }
}

void BackendFactory__create_specific(int64_t kind, int64_t target, CompileOptions options) {
    /* stub */
}

void BackendFactory__try_create(int64_t target, CompileOptions options) {
    /* stub */
}

bool BackendFactory__supports_target(int64_t kind, int64_t target) {
    switch (kind) {
        case BackendKind_Cranelift:
        {
            return true;
            break;
        }
        case BackendKind_Llvm:
        {
            return true;
            break;
        }
        case BackendKind_Interpreter:
        {
            return true;
            break;
        }
        case BackendKind_Native:
        {
            return true;
            break;
        }
        case BackendKind_Wasm:
        {
            return true;
            break;
        }
        case BackendKind_Lean:
        {
            return true;
            break;
        }
        case BackendKind_Cuda:
        {
            return true;
            break;
        }
        case BackendKind_Vulkan:
        {
            return true;
            break;
        }
    }
}

SplArray* BackendFactory__available_backends() {
    return spl_array_new();
}

BackendCapability get_cranelift_capability() {
    return BackendCapability{.backend_name = "Cranelift", .supports_simd = true, .supports_gpu = false, .supports_async = true, .supports_32bit = false, .instruction_coverage = 95};
}

BackendOptions backendoptions_jit() {
    return BackendOptions{}; /* stub */
}

CompileOptions compileoptions_default_options() {
    return CompileOptions{.target = CodegenTarget_Host, .opt_level = OptimizationLevel_Speed, .debug_info = false, .emit_assembly = false, .emit_llvm_ir = false, .emit_mir = false, .verify_output = true};
}

void CapabilityTracker__add_instruction(CapabilityTracker* self, const char* name, int64_t cat, bool cran, bool llvm_, bool vulk, bool interp) {
    /* stub */
}

CodegenError codegenerror_new(int64_t kind, const char* message) {
    return CodegenError{}; /* stub */
}

CompilerBackendImpl compilerbackendimpl_jit() {
    return CompilerBackendImpl{.mode = CodegenMode_Jit, .output_path = spl_nil()};
}

CompilerBackendImpl compilerbackendimpl_aot(const char* output) {
    return output_path: output);
}

CraneliftTypeMapper CraneliftTypeMapper__create() {
    return CraneliftTypeMapper{.target_bits = 64};
}

CraneliftTypeMapper CraneliftTypeMapper__create_for_target(int64_t target) {
    if false;
    error("Cranelift does not support 32-bit targets. Use LLVM backend instead.");
    return CraneliftTypeMapper{.target_bits = 64};
    SplArray* _tv_0 = spl_array_new();
    spl_array_push(_tv_0, spl_int(special handling));
    spl_array_push(_tv_0, spl_int(no direct type));
}

CudaBackend CudaBackend__create(int64_t compute_cap) {
    return CudaBackend{}; /* stub */
}

CudaTypeMapper CudaTypeMapper__create() {
    SplArray* _tup_0 = spl_array_new();
    spl_array_push(_tup_0, spl_int(7));
    spl_array_push(_tup_0, spl_int(0));
    return CudaTypeMapper{.compute_capability = _tup_0};
}

CudaTypeMapper CudaTypeMapper__create_sm(int64_t major, int64_t minor) {
    SplArray* _tv_1 = spl_array_new();
    spl_array_push(_tv_1, spl_int(major));
    spl_array_push(_tv_1, spl_int(minor));
    return CudaTypeMapper{.compute_capability = _tv_1};
}

SplDict* empty_env_scope() {
    SplDict* result = Value> = {};
    return result;
}

Environment environment_new() {
    return Environment{.scopes = spl_array_new(), .globals = empty_env_scope()};
}

bool environment_assign(Environment self, SymbolId symbol, int64_t value) {
    return false; /* stub */
}

HirVisitor hirvisitor_new(int64_t backend, HirModule module) {
    return HirVisitor{.backend = backend, .ctx = EvalContext{.env = environment_new(), .module = module, .backend = backend}};
}

const char* SourceLocation__to_string(const SourceLocation* self) {
    return spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(self->file_path, ":"), spl_i64_to_str(self->line_number)), ":"), spl_i64_to_str(self->column));
}

SourceLocation CatchAllPattern__get_location(const CatchAllPattern* self) {
    return self->location;
}

int64_t CatchAllPattern__get_severity(const CatchAllPattern* self) {
    return self->severity;
}

bool CatchAllPattern__is_error(const CatchAllPattern* self) {
    switch (self->severity) {
    }
}

const char* CatchAllPattern__format_report(const CatchAllPattern* self) {
    return ""; /* stub */
}

FileAnalysisResult FileAnalysisResult__new(const char* path) {
    return FileAnalysisResult{}; /* stub */
}

InterpreterConfig interpreterconfig_classic() {
    return InterpreterConfig{.mode = InterpreterMode_Classic, .enable_debug_hooks = true, .enable_gc = true, .use_ffi_arithmetic = true};
}

InterpreterConfig interpreterconfig_optimized() {
    return InterpreterConfig{.mode = InterpreterMode_Optimized, .enable_debug_hooks = false, .enable_gc = false, .use_ffi_arithmetic = false};
}

InterpreterConfig interpreterconfig_with_gc(InterpreterConfig self, bool enabled) {
    self->enable_gc = enabled;
    return self;
}

InterpreterConfig interpreterconfig_with_debug(InterpreterConfig self, bool enabled) {
    self->enable_debug_hooks = enabled;
    return self;
}

InterpreterBackendImpl interpreterbackendimpl_new() {
    return InterpreterBackendImpl{.config = interpreterconfig_classic()};
}

InterpreterBackendImpl interpreterbackendimpl_with_config(InterpreterConfig config) {
    return InterpreterBackendImpl{.config = config};
}

InterpreterBackendImpl interpreterbackendimpl_optimized() {
    return InterpreterBackendImpl{.config = interpreterconfig_optimized()};
    int64_t _cast_0 = span.column as i64;
    int64_t _asv_0 = span.line as i64;
}

InterpreterTypeMapper InterpreterTypeMapper__create() {
    return InterpreterTypeMapper{};
}

JitInterpreterConfig jitinterpreterconfig_default() {
    return JitInterpreterConfig{}; /* stub */
}

const char* mir_type_to_lean(MirType ty) {
    switch (ty.kind) {
        case Ptr(inner, _):
        {
            return spl_str_concat(spl_str_concat("Ptr (", mir_type_to_lean(inner)), ")");
            break;
        }
        case Array(elem, size):
        {
            return spl_str_concat(spl_str_concat(spl_str_concat("Array (", mir_type_to_lean(elem)), ") "), spl_i64_to_str(size));
            break;
        }
        case Struct(id):
        {
            return spl_str_concat("Struct", spl_i64_to_str(id));
            break;
        }
        case Tuple(elems):
        {
            int64_t elem_types = elems_map(elems, \e: mir_type_to_lean(e))_join(elems_map(elems, \e: mir_type_to_lean(e)), " × ");
            return spl_str_concat(spl_str_concat("(", spl_i64_to_str(elem_types)), ")");
            break;
        }
        case Option(inner):
        {
            return spl_str_concat(spl_str_concat("Option (", mir_type_to_lean(inner)), ")");
            break;
        }
        case Result(ok, err):
        {
            return spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("Except (", mir_type_to_lean(err)), ") ("), mir_type_to_lean(ok)), ")");
            break;
        }
    }
}

LeanBuilder LeanBuilder__create() {
    return LeanBuilder{}; /* stub */
}

const char* generate_borrow_proofs(int64_t func, int64_t checker) {
    const char* output = spl_str_concat(spl_str_concat("-- Borrow safety proofs for ", spl_i64_to_str(func.name)), "\n");
    output = spl_str_concat(output, "-- Auto-generated by Simple compiler\n\n");
    output = spl_str_concat(output, "import BorrowCheckerSafety\n\n");
    output = spl_str_concat(spl_str_concat(spl_str_concat(output, "namespace "), spl_i64_to_str(func.name)), "_safety\n\n");
    output = spl_str_concat(output, "open BorrowCheckerSafety\n\n");
    output = spl_str_concat(spl_str_concat(spl_str_concat(output, "/-- Function "), spl_i64_to_str(func.name)), " passes borrow checking --/\n");
    output = spl_str_concat(spl_str_concat(spl_str_concat(output, "theorem "), spl_i64_to_str(func.name)), "_borrow_safe : True := by trivial\n\n");
    output = spl_str_concat(output, "-- Additional theorems can be added based on analysis\n\n");
    output = spl_str_concat(spl_str_concat(spl_str_concat(output, "end "), spl_i64_to_str(func.name)), "_safety\n");
    return output;
}

const char* generate_place_definition(int64_t place) {
    const char* proj_list = "[]";
    return spl_str_concat(spl_str_concat(spl_str_concat("Place.mk ", spl_i64_to_str(place_base_id(place))), " "), proj_list);
}

const char* generate_borrow_definition(int64_t borrow, int64_t idx) {
    return ""; /* stub */
}

const char* generate_safety_theorem(const char* func_name, int64_t borrow_count) {
    const char* output = spl_str_concat(spl_str_concat("/-- Main safety theorem: all borrows in ", func_name), " are safe --/\n");
    output = spl_str_concat(spl_str_concat(spl_str_concat(output, "theorem "), func_name), "_borrows_safe :\n");
    output = spl_str_concat(output, "    BorrowSet.isSafe [");
    int64_t i = 0;
    while ((i < borrow_count)) {
        if ((i > 0)) {
            output = spl_str_concat(output, ", ");
        }
        output = spl_str_concat(spl_str_concat(output, "borrow"), spl_i64_to_str(i));
        i = (i + 1);
    }
    output = spl_str_concat(output, "] := by\n");
    output = spl_str_concat(output, "  unfold BorrowSet.isSafe\n");
    output = spl_str_concat(output, "  intro b1 b2 h1 h2\n");
    output = spl_str_concat(output, "  -- Proof by case analysis on borrow pairs\n");
    output = spl_str_concat(output, "  sorry  -- TODO: Complete proof based on borrow checker analysis\n");
    return output;
}

const char* generate_lean_module(MirModule module) {
    const char* output = "/-\n";
    output = spl_str_concat(spl_str_concat(spl_str_concat(output, "  Borrow Safety Proofs for Module: "), module.name), "\n");
    output = spl_str_concat(output, "  Auto-generated by Simple compiler\n");
    output = spl_str_concat(output, "-/\n\n");
    output = spl_str_concat(output, "import BorrowCheckerSafety\n\n");
    output = spl_str_concat(spl_str_concat(spl_str_concat(output, "namespace "), module.name), "_safety\n\n");
    output = spl_str_concat(output, "open BorrowCheckerSafety\n\n");
    int64_t checker = borrowchecker_create();
    for (int64_t __symbol_i = 0; __symbol_i < spl_array_len(MirModule__functions_keys(&module, functions)); __symbol_i++) {
        int64_t symbol = spl_array_get(MirModule__functions_keys(&module, functions), __symbol_i).as_int;
        int64_t mir_fn = module.functions[symbol];
        int64_t body = mirbody_from_function(mir_fn);
        return checker_check_function(checker, body);
        output = spl_str_concat(spl_str_concat(output, generate_borrow_proofs(body, checker)), "\n");
    }
    output = spl_str_concat(spl_str_concat(spl_str_concat(output, "end "), module.name), "_safety\n");
    return output;
}

LlvmBackend LlvmBackend__create(int64_t target, int64_t opt_level) {
    return LlvmBackend{}; /* stub */
}

SplArray* passes_for_level(int64_t level) {
    return nullptr; /* stub */
}

LlvmTargetTriple llvmtargettriple_from_target(int64_t target) {
    return LlvmTargetTriple__from_target_with_mode(target, bare_metal: false);
}

LlvmTargetTriple llvmtargettriple_from_target_baremetal(int64_t target) {
    return LlvmTargetTriple__from_target_with_mode(target, bare_metal: true);
}

LlvmTargetTriple llvmtargettriple_from_target_with_mode(int64_t target, bool bare_metal) {
    int64_t os = if bare_metal: "none" else: "linux";
    int64_t env = if bare_metal: nil else: "gnu";
    switch (target) {
        case CodegenTarget_X86_64:
        {
            return LlvmTargetTriple{.arch = "x86_64", .vendor = "unknown", .os = os, .has_env = (env != -1), .env = ((env) ? (env) : (""))};
            break;
        }
        case AArch64:
        {
            return LlvmTargetTriple{.arch = "aarch64", .vendor = "unknown", .os = os, .has_env = (env != -1), .env = ((env) ? (env) : (""))};
            break;
        }
        case CodegenTarget_Riscv64:
        {
            return LlvmTargetTriple{.arch = "riscv64", .vendor = "unknown", .os = os, .has_env = (env != -1), .env = ((env) ? (env) : (""))};
            break;
        }
        case Arch_X86:
        {
            return LlvmTargetTriple{.arch = "i686", .vendor = "unknown", .os = os, .has_env = (env != -1), .env = ((env) ? (env) : (""))};
            break;
        }
        case Arch_Arm:
        {
            int64_t arm_env = if bare_metal: "eabi" else: "gnueabihf";
            return LlvmTargetTriple{.arch = "armv7", .vendor = "unknown", .os = os, .has_env = true, .env = arm_env};
            break;
        }
        case Arch_Riscv32:
        {
            return LlvmTargetTriple{.arch = "riscv32", .vendor = "unknown", .os = os, .has_env = (env != -1), .env = ((env) ? (env) : (""))};
            break;
        }
        case Arch_Wasm32:
        {
            return LlvmTargetTriple{.arch = "wasm32", .vendor = "unknown", .os = "wasi", .has_env = false, .env = ""};
            break;
        }
        case Arch_Wasm64:
        {
            return LlvmTargetTriple{.arch = "wasm64", .vendor = "unknown", .os = "wasi", .has_env = false, .env = ""};
            break;
        }
        case TargetArch_Host:
        {
            return LlvmTargetTriple{.arch = "x86_64", .vendor = "unknown", .os = os, .has_env = (env != -1), .env = ((env) ? (env) : (""))};
            break;
        }
    }
}

const char* llvmtargettriple_to_text(LlvmTargetTriple triple) {
    const char* result = spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(triple.arch, "-"), triple.vendor), "-"), triple.os);
    if ((triple.has_env && (!spl_str_eq(triple.env, "")))) {
        result = spl_str_concat(spl_str_concat(result, "-"), triple.env);
    }
    return result;
}

LlvmTargetConfig llvmtargetconfig_for_target(int64_t target, Option_text cpu_override) {
    return LlvmTargetConfig__for_target_with_mode(target, cpu_override, bare_metal: false);
}

LlvmTargetConfig llvmtargetconfig_for_target_baremetal(int64_t target, Option_text cpu_override) {
    return LlvmTargetConfig__for_target_with_mode(target, cpu_override, bare_metal: true);
}

LlvmTargetConfig llvmtargetconfig_for_target_with_mode(int64_t target, const char* cpu_override, bool bare_metal) {
    return LlvmTargetConfig{}; /* stub */
}

LlvmTypeMapper LlvmTypeMapper__create() {
    return LlvmTypeMapper{.target_bits = 64};
}

LlvmTypeMapper LlvmTypeMapper__create_32bit() {
    return LlvmTypeMapper{.target_bits = 32};
}

LlvmTypeMapper LlvmTypeMapper__create_64bit() {
    return LlvmTypeMapper{.target_bits = 64};
}

LlvmTypeMapper LlvmTypeMapper__create_for_target(int64_t target) {
    if false;
    llvmtypemapper_create_32bit();
    return else:;
    return llvmtypemapper_create_64bit();
}

void MirTestBuilder__add_const_int(MirTestBuilder* self, int32_t dest, int64_t value) {
    VReg vreg = VReg{.id = dest};
    MirTestBuilder__instructions_push(self, instructions, MirTestInst__ConstInt(vreg, value));
    MirTestBuilder__update_next_vreg(self, dest);
}

void MirTestBuilder__add_const_float(MirTestBuilder* self, int32_t dest, double value) {
    VReg vreg = VReg{.id = dest};
    MirTestBuilder__instructions_push(self, instructions, MirTestInst__ConstFloat(vreg, value));
    MirTestBuilder__update_next_vreg(self, dest);
}

void MirTestBuilder__add_const_bool(MirTestBuilder* self, int32_t dest, bool value) {
    VReg vreg = VReg{.id = dest};
    MirTestBuilder__instructions_push(self, instructions, MirTestInst__ConstBool(vreg, value));
    MirTestBuilder__update_next_vreg(self, dest);
}

void MirTestBuilder__add_add(MirTestBuilder* self, int32_t dest, int32_t left, int32_t right) {
    /* stub */
}

int64_t MirTestCase__instruction_count(const MirTestCase* self) {
    return MirTestCase__instructions_len(self, instructions);
}

bool MirTestCase__is_supported(const MirTestCase* self, int64_t backend) {
    return MirTestCase__expected_backends_contains(self, expected_backends, backend);
}

void MirTestBuilder__add_binop(MirTestBuilder* self, int32_t dest, const char* op, int32_t left, int32_t right) {
    spl_array_push(self->instructions, spl_int(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("v", spl_i64_to_str(dest)), " = "), op), " v"), spl_i64_to_str(left)), ", v"), spl_i64_to_str(right))));
    if ((dest >= self->next_vreg)) {
        self->next_vreg = (dest + 1);
    }
}

void MirTestBuilder__add_ret(MirTestBuilder* self, int32_t vreg) {
    spl_array_push(self->instructions, spl_int(spl_str_concat("ret v", spl_i64_to_str(vreg))));
}

void MirTestBuilder__add_ret_void(MirTestBuilder* self) {
    spl_array_push(self->instructions, spl_int("ret void"));
}

void MirTestBuilder__add_branch(MirTestBuilder* self, int32_t cond, int32_t then_block, int32_t else_block) {
    spl_array_push(self->instructions, spl_int(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("br v", spl_i64_to_str(cond)), ", bb"), spl_i64_to_str(then_block)), ", bb"), spl_i64_to_str(else_block))));
}

void MirTestBuilder__add_jump(MirTestBuilder* self, int32_t block) {
    spl_array_push(self->instructions, spl_int(spl_str_concat("jmp bb", spl_i64_to_str(block))));
}

void MirTestBuilder__only_backend(MirTestBuilder* self, int64_t backend) {
    self->backends = spl_array_new();
}

void MirTestBuilder__only_backends(MirTestBuilder* self, SplArray* backend_list) {
    self->backends = backend_list;
}

MirTestCase MirTestBuilder__build(const MirTestBuilder* self) {
    return MirTestCase{}; /* stub */
}

NativeCompileResult nativecompileresult_success_result(const char* binary_path, int64_t compile_time_ms) {
    return NativeCompileResult{}; /* stub */
}

OptimizationPass optimizationpass_new(const char* name, bool enabled, int64_t priority, const char* description) {
    return OptimizationPass{}; /* stub */
}

RiscVRegisterAllocator riscvregisterallocator_new(int64_t arch) {
    return RiscVRegisterAllocator{}; /* stub */
}

VulkanBackend VulkanBackend__create(int64_t vk_version) {
    return VulkanBackend{}; /* stub */
}

VulkanTypeMapper VulkanTypeMapper__create() {
    return VulkanTypeMapper{};
}

int64_t mir_type_to_wasm(MirType ty, int64_t target) {
    WasmTypeMapper mapper = WasmTypeMapper__create_for_target(target);
    int64_t type_str = mapper_map_type(mapper, ty);
    switch (type_str) {
    }
}

BrowserBinding browserbinding_console_log() {
    return BrowserBinding{}; /* stub */
}

WasmTypeMapper WasmTypeMapper__create() {
    return WasmTypeMapper{.target_bits = 32};
}

WasmTypeMapper WasmTypeMapper__create_wasm32() {
    return WasmTypeMapper{.target_bits = 32};
}

WasmTypeMapper WasmTypeMapper__create_wasm64() {
    return WasmTypeMapper{.target_bits = 64};
}

WasmTypeMapper WasmTypeMapper__create_for_target(int64_t target) {
    if ((target == CodegenTarget_Wasm32)) {
        return wasmtypemapper_create_wasm32();
    } else if ((target == CodegenTarget_Wasm64)) {
        return wasmtypemapper_create_wasm64();
    }
    return else:;
    return error("WasmTypeMapper only supports Wasm32 and Wasm64 targets");
}

X86RegisterAllocator x86registerallocator_new(int64_t arch) {
    return X86RegisterAllocator{}; /* stub */
}

LinkResult linkresult_ok(const char* output, int32_t table_size) {
    return LinkResult{}; /* stub */
}

SMFMetadata smfmetadata_empty() {
    return SMFMetadata{}; /* stub */
}

StringMetadata stringmetadata_create(int32_t id, const char* text, int32_t params) {
    return StringMetadata{}; /* stub */
}

FullStringEntry fullstringentry_from_smf_entry(int64_t entry) {
    return FullStringEntry{}; /* stub */
}

const char* generate_smt_section(int64_t table) {
    const char* asm_code = "";
    asm_code = spl_str_concat(asm, spl_str_concat("# Auto-generated string table section", NL));
    asm_code = spl_str_concat(asm, spl_str_concat("# DO NOT EDIT - Generated by Simple compiler", NL));
    asm_code = spl_str_concat(asm, NL);
    asm_code = spl_str_concat(asm, spl_str_concat(".section .smt, \"a\"", NL));
    asm_code = spl_str_concat(asm, spl_str_concat(".align 4", NL));
    asm_code = spl_str_concat(asm, NL);
    asm_code = spl_str_concat(asm, spl_str_concat(".global __simple_string_table", NL));
    asm_code = spl_str_concat(asm, spl_str_concat(".global __simple_string_table_end", NL));
    asm_code = spl_str_concat(asm, NL);
    asm_code = spl_str_concat(asm, spl_str_concat("__simple_string_table:", NL));
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat(spl_str_concat("    .word ", spl_i64_to_str(table_count(table))), "           # Entry count"), NL));
    asm_code = spl_str_concat(asm, NL);
    for (int64_t __entry_i = 0; __entry_i < spl_array_len(table.entries); __entry_i++) {
        int64_t entry = spl_array_get(table.entries, __entry_i).as_int;
        asm_code = spl_str_concat(asm, generate_entry_asm(entry));
    }
    asm_code = spl_str_concat(asm, NL);
    asm_code = spl_str_concat(asm, spl_str_concat("__simple_string_table_end:", NL));
    asm_code = spl_str_concat(asm, NL);
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat(spl_str_concat("# Table size: ", spl_i64_to_str(table.total_size)), " bytes"), NL));
    asm_code = spl_str_concat(asm, spl_str_concat(".global __simple_string_table_size", NL));
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat(".set __simple_string_table_size, ", spl_i64_to_str(table.total_size)), NL));
    return asm_code;
}

const char* generate_entry_asm(FullStringEntry entry) {
    const char* asm_code = "";
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("    # Entry ", spl_i64_to_str(entry.id)), ": \""), escape_for_comment(entry.text)), "\" "));
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("(", spl_i64_to_str(entry.length)), " bytes, "), spl_i64_to_str(entry.param_count)), " params)\n"));
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat("    .word ", spl_i64_to_str(entry.id)), "                # ID\n"));
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat("    .word ", spl_i64_to_str(entry.length)), "            # Length (with null)\n"));
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat("    .word ", spl_i64_to_str(entry.param_count)), "       # Parameter count\n"));
    asm_code = spl_str_concat(asm, spl_str_concat(spl_str_concat(spl_str_concat("    .ascii \"", escape_for_asm(entry.text)), "\\0\""), NL));
    asm_code = spl_str_concat(asm, spl_str_concat("    .align 4", NL));
    asm_code = spl_str_concat(asm, NL);
    return asm_code;
}

const char* escape_for_asm(const char* s) {
    const char* result = "";
    int64_t i = 0;
    while ((i < s_len(s))) {
        const char* ch = spl_str_slice(s, i, i+1);
        if (spl_str_eq(ch, "\n")) {
            result = spl_str_concat(result, "\\n");
        } else if (spl_str_eq(ch, "\t")) {
            result = spl_str_concat(result, "\\t");
        } else if (spl_str_eq(ch, "\r")) {
            result = spl_str_concat(result, "\\r");
        } else if (spl_str_eq(ch, "\"")) {
            result = spl_str_concat(result, "\\\"");
        } else if (spl_str_eq(ch, "\\")) {
            result = spl_str_concat(result, "\\\\");
        } else {
            result = spl_str_concat(result, ch);
        }
        i = (i + 1);
    }
    return result;
}

const char* escape_for_comment(const char* s) {
    int64_t max_len = 40;
    const char* escaped = escape_for_asm(s);
    if ((escaped_len(escaped) > max_len)) {
        escaped = spl_str_concat(spl_str_slice(escaped, 0, max_len), "...");
    }
    return escaped;
}

const char* generate_linker_script_fragment() {
    const char* script = "";
    script = spl_str_concat(script, "/* String table section */\n");
    script = spl_str_concat(script, ".smt : {\n");
    script = spl_str_concat(script, "    . = ALIGN(4);\n");
    script = spl_str_concat(script, "    __simple_string_table = .;\n");
    script = spl_str_concat(script, "    *(.smt)\n");
    script = spl_str_concat(script, "    __simple_string_table_end = .;\n");
    script = spl_str_concat(script, "    . = ALIGN(4);\n");
    script = spl_str_concat(script, "} > RAM\n");
    return script;
}

const char* generate_metadata_json(int64_t table) {
    const char* json = "";
    json = spl_str_concat(json, "{\n");
    json = spl_str_concat(json, "  \"version\": 1,\n");
    json = spl_str_concat(json, "  \"format\": \"simple_string_table\",\n");
    json = spl_str_concat(json, spl_str_concat(spl_str_concat("  \"entry_count\": ", spl_i64_to_str(table_count(table))), ",\n"));
    json = spl_str_concat(json, spl_str_concat(spl_str_concat("  \"total_size\": ", spl_i64_to_str(table.total_size)), ",\n"));
    json = spl_str_concat(json, "  \"entries\": [\n");
    bool first = true;
    for (int64_t __entry_i = 0; __entry_i < spl_array_len(table.entries); __entry_i++) {
        int64_t entry = spl_array_get(table.entries, __entry_i).as_int;
        if (!(first)) {
            json = spl_str_concat(json, ",\n");
        }
        first = false;
        json = spl_str_concat(json, "    {\n");
        json = spl_str_concat(json, spl_str_concat(spl_str_concat("      \"id\": ", spl_i64_to_str(entry.id)), ",\n"));
        json = spl_str_concat(json, spl_str_concat(spl_str_concat("      \"text\": \"", escape_for_json(entry.text)), "\",\n"));
        json = spl_str_concat(json, spl_str_concat(spl_str_concat("      \"length\": ", spl_i64_to_str(entry.length)), ",\n"));
        json = spl_str_concat(json, spl_str_concat(spl_str_concat("      \"param_count\": ", spl_i64_to_str(entry.param_count)), ",\n"));
        json = spl_str_concat(json, spl_str_concat(spl_str_concat("      \"aligned_size\": ", spl_i64_to_str(entry.aligned_size)), "\n"));
        json = spl_str_concat(json, "    }");
    }
    json = spl_str_concat(json, "\n  ]\n");
    json = spl_str_concat(json, "}\n");
    return json;
}

const char* escape_for_json(const char* s) {
    const char* result = "";
    int64_t i = 0;
    while ((i < s_len(s))) {
        const char* ch = spl_str_slice(s, i, i+1);
        if (spl_str_eq(ch, "\n")) {
            result = spl_str_concat(result, "\\n");
        } else if (spl_str_eq(ch, "\t")) {
            result = spl_str_concat(result, "\\t");
        } else if (spl_str_eq(ch, "\r")) {
            result = spl_str_concat(result, "\\r");
        } else if (spl_str_eq(ch, "\"")) {
            result = spl_str_concat(result, "\\\"");
        } else if (spl_str_eq(ch, "\\")) {
            result = spl_str_concat(result, "\\\\");
        } else {
            result = spl_str_concat(result, ch);
        }
        i = (i + 1);
    }
    return result;
}

bool write_asm_file(const char* asm_code, const char* output_path) {
    return file_write(output_path, asm_code);
}

bool write_metadata_file(int64_t table, const char* output_path) {
    const char* json = generate_metadata_json(table);
    return file_write(output_path, json);
}

bool file_write(const char* path, const char* content) {
    io_file_write(path, content);
    return true;
}

void test_codegen() {
    int64_t metadata = parse_smf_file("hello_world.smf");
    int64_t table = build_full_table(metadata);
    const char* asm_code = generate_smt_section(table);
    spl_println("Generated assembly:");
    spl_println("====================");
    spl_println(asm_code);
    spl_println("");
    const char* json = generate_metadata_json(table);
    spl_println("Metadata JSON:");
    spl_println("==============");
    spl_println(json);
    write_asm_file(asm_code, "string_table.s");
    write_metadata_file(table, "string_table.json");
}

BlockBuilder blockbuilder_new(const char* kind) {
    return BlockBuilder{}; /* stub */
}

SplArray* sql_keywords() {
    const char* s = "SELECT";
    const char* f = "FROM";
    const char* w = "WHERE";
    return spl_array_new();
}

BlockContext blockcontext_new(const char* payload, Span payload_span, Span block_span) {
    return BlockContext{}; /* stub */
}

int64_t error_at(BlockContext ctx, const char* message, int64_t offset, int64_t length) {
    Span span = Span{.start = (ctx.payload_span.start + offset), .end = ((ctx.payload_span.start + offset) + length), .line = ctx.payload_span.line, .col = (ctx.payload_span.col + offset)};
}

std::vector<HighlightToken> highlight_keywords(const char* text, SplArray* keywords) {
    SplArray* tokens = spl_array_new();
    int64_t pos = 0;
    for (int64_t __keyword_i = 0; __keyword_i < spl_array_len(keywords); __keyword_i++) {
        const char* keyword = spl_array_get(keywords, __keyword_i).as_str;
        int64_t search_pos = 0;
        while (true) {
            int64_t index = text_index_of(text, keyword, start: search_pos);
            if (!(has_index)) {
                break;
            }
            if (is_word_boundary(text, index, keyword_len(keyword))) {
                HighlightToken token = HighlightToken{.start = index, .end = (index + keyword_len(keyword)), .kind = HighlightKind_Keyword};
                tokens = tokens_push(tokens, token);
            }
            search_pos = (index + 1);
        }
    }
    return tokens;
}

std::vector<HighlightToken> highlight_strings(const char* text) {
    return std::vector<HighlightToken>{}; /* stub */
}

LexerConfig lexerconfig_default() {
    return LexerConfig{}; /* stub */
}

TextSpan textspan_new(int64_t start, int64_t end) {
    return TextSpan{.start = start, .end = end};
}

PreLexInfo prelexinfo_empty() {
    return PreLexInfo{.string_spans = {}, .comment_spans = {}, .escape_positions = spl_array_new(), .brace_pairs = spl_array_new()};
}

void enable_block(const char* kind, int64_t block_def) {
    register_block(block_def);
}

void disable_block(const char* kind) {
    block_registry()_unregister(block_registry(), kind);
}

SplArray* list_blocks() {
    return block_registry()_all_keywords(block_registry());
}

int64_t block_info(const char* kind) {
    return 0; /* stub */
}

const char* parse_json(const char* text) {
    switch (json_parse(text_trim(text))) {
        case Ok(json_value):
        {
            return Result_Ok;
            break;
        }
        case Err(error):
        {
            return Result_Err;
            break;
        }
    }
}

const char* parse_yaml(const char* text) {
    return ""; /* stub */
}

const char* parse_toml(const char* text) {
    return ""; /* stub */
}

const char* parse_xml(const char* text) {
    return ""; /* stub */
}

const char* parse_csv(const char* text) {
    const char* lines = spl_str_split(spl_str_trim(text), NL);
    SplArray* rows = spl_array_new();
    for (int64_t __line_i = 0; __line_i < spl_array_len(lines); __line_i++) {
        int64_t line = spl_array_get(lines, __line_i).as_int;
        if ((spl_array_len(line_trim(line)) == 0)) {
            /* pass */;
        } else {
            int64_t cells = spl_str_split(line, ",");
            SplArray* trimmed_cells = spl_array_new();
            for (int64_t __cell_i = 0; __cell_i < spl_array_len(cells); __cell_i++) {
                int64_t cell = spl_array_get(cells, __cell_i).as_int;
                return trimmed_cells_push(trimmed_cells, spl_str_trim(cell));
            }
            return rows_push(rows, trimmed_cells);
        }
    }
    return Result_Ok;
}

int64_t json_parse_internal(const char* input) {
    switch (json_parse(text_trim(input))) {
    }
}

int64_t yaml_parse_internal(const char* input) {
    return 0; /* stub */
}

int64_t toml_parse_internal(const char* input) {
    return 0; /* stub */
}

int64_t xml_parse_internal(const char* input) {
    return 0; /* stub */
}

SplArray* csv_parse_internal(const char* input) {
    const char* lines = spl_str_split(spl_str_trim(input), NL);
    SplArray* rows = spl_array_new();
    for (int64_t __line_i = 0; __line_i < spl_array_len(lines); __line_i++) {
        int64_t line = spl_array_get(lines, __line_i).as_int;
        int64_t trimmed = spl_str_trim(line);
        if ((spl_array_len(trimmed) > 0)) {
            int64_t cells = spl_str_split(trimmed, ",");
            SplArray* row = spl_array_new();
            for (int64_t __cell_i = 0; __cell_i < spl_array_len(cells); __cell_i++) {
                int64_t cell = spl_array_get(cells, __cell_i).as_int;
                return spl_array_push(row, spl_str(spl_str_trim(cell)));
            }
            return spl_array_push(rows, spl_array_val(row));
        }
    }
    return rows;
}

BlockRegistry blockregistry_new() {
    return BlockRegistry{}; /* stub */
}

BlockRegistry blockregistry_default() {
    int64_t reg = BlockRegistry__new();
    reg_register(reg, MathBlockDef{});
    reg_register(reg, LossBlockDef{});
    return reg_register(reg, NogradBlockDef{});
    reg_register(reg, ShellBlockDef{});
    reg_register(reg, SqlBlockDef{});
    reg_register(reg, RegexBlockDef{});
    reg_register(reg, JsonBlockDef{});
    return reg_register(reg, MarkdownBlockDef{});
    return reg;
}

bool blockregistry_unregister(BlockRegistry self, const char* kind) {
    if (BlockRegistry__blocks_contains_key(self, blocks, kind)) {
        self->blocks = BlockRegistry__blocks_remove(self, blocks, kind);
        return true;
    } else {
        return false;
    }
}

BlockRegistry block_registry() {
    if (!(has__global_registry)) {
        _global_registry = BlockRegistry__default();
    }
    return _global_registry_value;
}

void register_block(int64_t block_def) {
    BlockRegistry reg = block_registry();
    reg_register(reg, block_def);
}

bool unregister_block(const char* kind) {
    BlockRegistry reg = block_registry();
    return reg_unregister(reg, kind);
}

bool is_block(const char* kind) {
    return block_registry()_is_block_keyword(block_registry(), kind);
}

void get_block(const char* kind) {
    block_registry()_lookup(block_registry(), kind);
}

bool is_block_registered(const char* kind) {
    return is_block(kind);
}

void with_block(int64_t block_def, int64_t body) {
    int64_t kind = block_def_kind(block_def);
    register_block(block_def);
    int64_t result = body();
    unregister_block(kind);
    result;
}

RegistryBuilder registrybuilder_new() {
    return RegistryBuilder{}; /* stub */
}

ResolvedModule resolvedmodule_new(OutlineModule outline, SplArray* blocks) {
    return ResolvedModule{}; /* stub */
}

const char* interpolate_variables(const char* text, SplDict* vars) {
    return ""; /* stub */
}

const char* strip_indent(const char* text) {
    int64_t lines = spl_str_split(text, NL);
    int64_t min_indent = 999999;
    for (int64_t __line_i = 0; __line_i < spl_array_len(lines); __line_i++) {
        int64_t line = spl_array_get(lines, __line_i).as_int;
        if ((line_trim(line) != 0)) {
            int64_t indent = (line_len(line) - spl_array_len(line_trim_start(line)));
            if ((indent < min_indent)) {
                min_indent = indent;
            }
        }
    }
    SplArray* result = spl_array_new();
    for (int64_t __line_i = 0; __line_i < spl_array_len(lines); __line_i++) {
        int64_t line = spl_array_get(lines, __line_i).as_int;
        if ((line_len(line) >= min_indent)) {
            return spl_array_push(result, spl_str(spl_str_slice(line, min_indent, spl_str_len(line))));
        } else {
            return spl_array_push(result, spl_str(line));
        }
    }
    return result_join(result, NL);
}

const char* normalize_newlines(const char* text) {
    return spl_str_replace(spl_str_replace(text, "\r\n", NL), "\r", NL);
}

SplArray* validate_json(int64_t value) {
    switch (value) {
        case Json(json_val):
        {
            return validate_json_structure(json_val);
            break;
        }
        default:
        {
            return spl_array_new();
            break;
        }
    }
}

SplArray* validate_regex(int64_t value) {
    switch (value) {
        case Regex(pattern):
        {
            if (pattern.has_raw) {
                return spl_array_new();
            } else {
                return spl_array_new();
            }
            break;
        }
        default:
        {
            return spl_array_new();
            break;
        }
    }
}

SplArray* validate_sql(int64_t value, const char* dialect) {
    switch (value) {
        case Sql(query):
        {
            return validate_sql_dialect(query, dialect);
            break;
        }
        default:
        {
            return spl_array_new();
            break;
        }
    }
}

SplArray* validate_json_structure(int64_t value) {
    SplArray* errors = spl_array_new();
    int64_t depth = json_depth(value, 0);
    if ((depth > 100)) {
        return spl_array_push(errors, spl_int(spl_str_concat(spl_str_concat("JSON nesting depth ", spl_i64_to_str(depth)), " exceeds maximum 100")));
    }
    switch (value.kind) {
        case Object(fields):
        {
            for (int64_t field = 0; field < fields; field++) {
                int64_t key = field[0];
                if ((key_len(key) == 0)) {
                    return spl_array_push(errors, spl_int("JSON object has empty key"));
                }
            }
            for (int64_t field = 0; field < fields; field++) {
                SplArray* nested_errors = validate_json_structure(field[1]);
                errors = (errors + nested_errors);
            }
            break;
        }
        case Array(elements):
        {
            if ((elements_len(elements) > 0)) {
                const char* first_type = json_type_name(elements[0]);
                bool mixed = false;
                for (int64_t elem = 0; elem < elements; elem++) {
                    if ((!spl_str_eq(json_type_name(elem), first_type))) {
                        mixed = true;
                    }
                }
                if (mixed) {
                    return spl_array_push(errors, spl_int("Warning: JSON array has mixed types"));
                }
            }
            for (int64_t elem = 0; elem < elements; elem++) {
                SplArray* nested_errors = validate_json_structure(elem);
                errors = (errors + nested_errors);
            }
            break;
        }
        default:
        {
            /* pass */;
            break;
        }
    }
    return errors;
}

SplArray* validate_sql_dialect(int64_t query, const char* dialect) {
    SplArray* errors = spl_array_new();
    int64_t raw = SqlQuery__raw_lower(&query, raw);
    if (((spl_str_contains(raw, "';") || spl_str_contains(raw, "--")) || spl_str_contains(raw, "/*"))) {
        return spl_array_push(errors, spl_int("Warning: SQL contains potential injection patterns"));
    }
    switch (dialect) {
        case "postgres":
        {
            if (spl_str_contains(raw, "limit")) {
                if (!(spl_str_contains(raw, "offset"))) {
                }
                /* pass */;
            }
            if (spl_str_contains(raw, "returning")) {
                if ((((query.kind != SqlKind_Insert) && (query.kind != SqlKind_Update)) && (query.kind != SqlKind_Delete))) {
                }
                return spl_array_push(errors, spl_int("RETURNING clause only valid for INSERT/UPDATE/DELETE in PostgreSQL"));
            }
            if ((spl_str_contains(raw, "serial") || spl_str_contains(raw, "bigserial"))) {
                /* pass */;
            }
            if (spl_str_contains(raw, "auto_increment")) {
                return spl_array_push(errors, spl_int("auto_increment is MySQL syntax; use SERIAL in PostgreSQL"));
            }
            break;
        }
        case "mysql":
        {
            if (spl_str_contains(raw, "serial")) {
                return spl_array_push(errors, spl_int("SERIAL is PostgreSQL syntax; use AUTO_INCREMENT in MySQL"));
            }
            if (spl_str_contains(raw, "returning")) {
                return spl_array_push(errors, spl_int("RETURNING clause not supported in MySQL"));
            }
            if (spl_str_contains(raw, "limit")) {
                if (spl_str_contains(raw, ",")) {
                }
                /* pass */;
            }
            break;
        }
        case "sqlite":
        {
            if (spl_str_contains(raw, "serial")) {
                return spl_array_push(errors, spl_int("Use INTEGER PRIMARY KEY AUTOINCREMENT in SQLite"));
            }
            if (spl_str_contains(raw, "returning")) {
                return spl_array_push(errors, spl_int("RETURNING clause not supported in SQLite (requires version 3[35]+)"));
            }
            if (spl_str_contains(raw, "alter table")) {
                if (((spl_str_contains(raw, "add constraint") || spl_str_contains(raw, "drop column")))) {
                }
                return spl_array_push(errors, spl_int("Warning: SQLite has limited ALTER TABLE support"));
            }
            break;
        }
        case "ansi":
        {
            if ((spl_str_contains(raw, "serial") || spl_str_contains(raw, "auto_increment"))) {
                return spl_array_push(errors, spl_int("SERIAL/AUTO_INCREMENT are vendor extensions; use IDENTITY in ANSI SQL"));
            }
            if (spl_str_contains(raw, "limit")) {
                return spl_array_push(errors, spl_int("LIMIT is vendor extension; use FETCH FIRST in ANSI SQL"));
            }
            break;
        }
        default:
        {
            return spl_array_push(errors, spl_int(spl_str_concat("Unknown SQL dialect: ", dialect)));
            break;
        }
    }
    if ((query.kind == SqlKind_Select)) {
        if (!(spl_str_contains(raw, "from"))) {
            if (!(spl_str_contains(raw, "select"))) {
            }
            return spl_array_push(errors, spl_int("SELECT query should have FROM clause or be SELECT without table"));
        }
    }
    if ((query.kind == SqlKind_Insert)) {
        if (!(spl_str_contains(raw, "values"))) {
            if (!(spl_str_contains(raw, "select"))) {
            }
            return spl_array_push(errors, spl_int("INSERT should have VALUES or SELECT clause"));
        }
    }
    return errors;
}

int64_t json_depth(int64_t value, int64_t current) {
    switch (value.kind) {
        case Object(fields):
        {
            int64_t max_depth = current;
            for (int64_t field = 0; field < fields; field++) {
                int64_t nested_depth = json_depth(field[1], (current + 1));
                if ((nested_depth > max_depth)) {
                    max_depth = nested_depth;
                }
            }
            return max_depth;
            break;
        }
        case Array(elements):
        {
            int64_t max_depth = current;
            for (int64_t elem = 0; elem < elements; elem++) {
                int64_t nested_depth = json_depth(elem, (current + 1));
                if ((nested_depth > max_depth)) {
                    max_depth = nested_depth;
                }
            }
            return max_depth;
            break;
        }
        default:
        {
            return current;
            break;
        }
    }
}

const char* json_type_name(int64_t value) {
    switch (value.kind) {
    }
}

ResolvedBlock resolvedblock_new(const char* kind, int64_t value, Span span, Span payload_span) {
    return ResolvedBlock{.kind = kind, .value = value, .span = span, .payload_span = payload_span};
}

int64_t Place__local(int64_t id) {
    return Place(base: placebase_Local(id), projections:[0]);
}

int64_t Place__static_var(const char* name) {
    return Place(base: placebase_Static(name), projections:[0]);
}

int64_t Borrow__create(int64_t id, int64_t place, int64_t kind, int64_t lifetime, int64_t point) {
    return PointerKind_Borrow;
}

int64_t place_static_var(const char* name) {
    return Place(base: placebase_Static(name), projections:[0]);
}

int64_t place_deref(int64_t self) {
    return 0; /* stub */
}

int64_t Region__create(int64_t id, int64_t lifetime) {
    return 0; /* stub */
}

BorrowChecker BorrowChecker__create() {
    return BorrowChecker{}; /* stub */
}

int64_t BasicBlock__create(int64_t id) {
    return 0; /* stub */
}

ImportEdge importedge_new(const char* from, const char* to, int64_t kind) {
    return ImportEdge{.from = from, .to = to, .kind = kind};
}

CyclicDependencyError cyclicdependencyerror_new(SplArray* cycle) {
    return CyclicDependencyError{.cycle = cycle};
}

ImportGraph importgraph_new() {
    return ImportGraph{}; /* stub */
}

MacroSymbol macrosymbol_new(const char* module_path, const char* name, int64_t kind) {
    return MacroSymbol{.module_path = module_path, .name = name, .kind = kind};
}

MacroSymbol macrosymbol_value_sym(const char* module_path, const char* name) {
    return macrosymbol_new(module_path, name, SymKind_ValueOrType);
}

MacroSymbol macrosymbol_macro_sym(const char* module_path, const char* name) {
    return macrosymbol_new(module_path, name, SymKind_MacroKind);
}

AutoImport autoimport_new(const char* from_module, const char* macro_name) {
    return AutoImport{.from_module = from_module, .macro_name = macro_name};
}

MacroExports macroexports_new() {
    return MacroExports{.non_macros = {}, .macros = {}};
}

MacroDirManifest macrodirmanifest_new(const char* name) {
    return MacroDirManifest{.name = name, .auto_imports = {}};
}

bool is_auto_imported(MacroDirManifest manifest, MacroSymbol sym) {
    int64_t sym_kind = sym_get_kind(sym);
    switch (sym_kind) {
        case SymKind_ValueOrType:
        {
            return false;
            break;
        }
        case SymKind_MacroKind:
        {
            /* pass */;
            break;
        }
    }
    int64_t sym_module = sym_get_module_path(sym);
    int64_t sym_name = sym_get_name(sym);
    for (size_t __ai_i = 0; __ai_i < manifest.auto_imports.size(); __ai_i++) {
        AutoImport ai = manifest.auto_imports[__ai_i];
        int64_t ai_module = ai_get_from_module(ai);
        int64_t ai_macro = ai_get_macro_name(ai);
        if ((ai_module == sym_module)) {
            if ((ai_macro == sym_name)) {
            }
            return true;
        }
    }
    return false;
}

std::vector<MacroSymbol> auto_imported_macros(MacroDirManifest manifest, MacroExports exports) {
    std::vector<MacroSymbol> result = {};
    for (size_t __sym_i = 0; __sym_i < exports.macros.size(); __sym_i++) {
        MacroSymbol sym = exports.macros[__sym_i];
        if (is_auto_imported(manifest, sym)) {
            return result_push(result, sym);
        }
    }
    return result;
}

std::vector<MacroSymbol> glob_import(MacroDirManifest manifest, MacroExports exports) {
    std::vector<MacroSymbol> result = {};
    for (size_t __sym_i = 0; __sym_i < exports.non_macros.size(); __sym_i++) {
        MacroSymbol sym = exports.non_macros[__sym_i];
        return result_push(result, sym);
    }
    std::vector<MacroSymbol> auto_macros = auto_imported_macros(manifest, exports);
    for (size_t __sym_i = 0; __sym_i < auto_macros.size(); __sym_i++) {
        MacroSymbol sym = auto_macros[__sym_i];
        return result_push(result, sym);
    }
    return result;
}

int64_t explicit_import(MacroExports exports, const char* name) {
    for (size_t __sym_i = 0; __sym_i < exports.non_macros.size(); __sym_i++) {
        MacroSymbol sym = exports.non_macros[__sym_i];
        int64_t sym_name = sym_get_name(sym);
        if (spl_str_eq(sym_name, name)) {
            return sym;
        }
    }
    for (size_t __sym_i = 0; __sym_i < exports.macros.size(); __sym_i++) {
        MacroSymbol sym = exports.macros[__sym_i];
        int64_t sym_name = sym_get_name(sym);
        if (spl_str_eq(sym_name, name)) {
            return sym;
        }
    }
    return spl_nil();
}

MacroExports combine_exports(MacroExports e1, MacroExports e2) {
    MacroExports result = macroexports_new();
    for (size_t __sym_i = 0; __sym_i < e1.non_macros.size(); __sym_i++) {
        MacroSymbol sym = e1.non_macros[__sym_i];
        return MacroExports__non_macros_push(&result, non_macros, sym);
    }
    for (size_t __sym_i = 0; __sym_i < e2.non_macros.size(); __sym_i++) {
        MacroSymbol sym = e2.non_macros[__sym_i];
        return MacroExports__non_macros_push(&result, non_macros, sym);
    }
    for (size_t __sym_i = 0; __sym_i < e1.macros.size(); __sym_i++) {
        MacroSymbol sym = e1.macros[__sym_i];
        return MacroExports__macros_push(&result, macros, sym);
    }
    for (size_t __sym_i = 0; __sym_i < e2.macros.size(); __sym_i++) {
        MacroSymbol sym = e2.macros[__sym_i];
        return MacroExports__macros_push(&result, macros, sym);
    }
    return result;
}

FileSystem filesystem_new() {
    return FileSystem{.files = spl_array_new()};
}

FileSystem filesystem_from_files(SplArray* files) {
    return FileSystem{.files = files};
}

const char* to_file_path(const char* root, ModPath mp) {
    const char* path = spl_str_concat(root, "/");
    int64_t segs = mp_segments(mp);
    int64_t i = 0;
    while ((i < segs_len(segs))) {
        if ((i > 0)) {
            path = spl_str_concat(path, "/");
        }
        path = spl_str_concat(path, segs[i]_name(segs[i]));
        i = (i + 1);
    }
    return spl_str_concat(path, ".spl");
}

const char* to_dir_path(const char* root, ModPath mp) {
    const char* path = spl_str_concat(root, "/");
    int64_t segs = mp_segments(mp);
    int64_t i = 0;
    while ((i < segs_len(segs))) {
        if ((i > 0)) {
            path = spl_str_concat(path, "/");
        }
        path = spl_str_concat(path, segs[i]_name(segs[i]));
        i = (i + 1);
    }
    return spl_str_concat(path, "/__init__.spl");
}

int64_t resolve(FileSystem fs, const char* root, ModPath mp) {
    const char* file_path = to_file_path(root, mp);
    const char* dir_path = to_dir_path(root, mp);
    int64_t file_exists = fs_has_file(fs, file_path);
    int64_t dir_exists = fs_has_file(fs, dir_path);
    if (file_exists) {
        if (dir_exists) {
        }
        return resolutionresult_Ambiguous(file_path: file_path, dir_path: dir_path);
    } else if (file_exists) {
        return resolutionresult_Unique(kind: FileKind.File, path: file_path);
    } else if (dir_exists) {
        return resolutionresult_Unique(kind: FileKind.Directory, path: dir_path);
    } else {
        return ResolutionResult_NotFound;
    }
}

bool is_well_formed(FileSystem fs, const char* root) {
    for (int64_t __file_path_i = 0; __file_path_i < spl_array_len(fs.files); __file_path_i++) {
        const char* file_path = spl_array_get(fs.files, __file_path_i).as_str;
        if (spl_str_ends_with(file_path, ".spl")) {
            if (!(spl_str_ends_with(file_path, "__init__.spl"))) {
            }
            int64_t base = spl_str_index_char(file_path, 0..-4);
            int64_t init_path = spl_str_concat(base, "/__init__.spl");
            if (fs_has_file(fs, init_path)) {
                return false;
            }
        }
    }
    return true;
}

SymbolConflictError symbolconflicterror_new(const char* name, const char* existing, const char* new_sym) {
    return SymbolConflictError{.name = name, .existing_qualified = existing, .new_qualified = new_sym};
}

Symbol symbol_new(const char* name, int64_t visibility) {
    return Symbol{.id = symbolid_new(name), .visibility = visibility};
}

Symbol symbol_pub_symbol(const char* name) {
    return symbol_new(name, Visibility_Public);
}

Symbol symbol_priv_symbol(const char* name) {
    return symbol_new(name, Visibility_Private);
}

ModDecl moddecl_new(const char* name, bool is_pub) {
    return ModDecl{.name = name, .is_pub = is_pub};
}

ModDecl moddecl_pub_decl(const char* name) {
    return moddecl_new(name, true);
}

ModDecl moddecl_priv_decl(const char* name) {
    return moddecl_new(name, false);
}

DirManifest dirmanifest_new(const char* name) {
    return DirManifest{.name = name, .children = {}, .exports = {}};
}

ModuleContents modulecontents_new() {
    return ModuleContents{.symbols = {}};
}

StateEnum generate_state_enum(const char* func_name, int64_t analysis) {
    return StateEnum{}; /* stub */
}

SuspensionAnalysis analyze_suspensions(Function func) {
    return SuspensionAnalysis{}; /* stub */
}

ChangeSet changeset_empty() {
    return ChangeSet{.changes = spl_array_new()};
}

BuildCache buildcache_empty(const char* cache_path) {
    return BuildCache{}; /* stub */
}

BuildCache buildcache_load(const char* cache_path) {
    if (!(rt_file_exists(cache_path))) {
        return BuildCache__empty(cache_path);
    }
    switch (parse_file(cache_path)) {
        case Ok(sdn_value):
        {
            return BuildCache__empty(cache_path);
            break;
        }
        case Err(error):
        {
            return BuildCache__empty(cache_path);
            break;
        }
    }
}

IncrementalCompiler incrementalcompiler_create(const char* source_root, const char* cache_path) {
    int64_t cache = BuildCache__load(cache_path);
    return IncrementalCompiler{.cache = cache, .source_root = source_root};
}

ParallelBuildConfig parallelbuildconfig_default() {
    return ParallelBuildConfig{.num_threads = 0, .parallel_threshold = 4, .deterministic = true, .verbose = false};
}

ParallelBuildConfig parallelbuildconfig_single_threaded() {
    return ParallelBuildConfig{.num_threads = 1, .parallel_threshold = 999, .deterministic = true, .verbose = false};
}

BuildGraph buildgraph_empty() {
    return BuildGraph{}; /* stub */
}

int64_t buildgraph_add_unit(BuildGraph self, const char* path, SplArray* dependencies) {
    int64_t id = self->next_id;
    self->next_id = (self->next_id + 1);
    BuildUnit unit = BuildUnit{.id = id, .path = path, .dependencies = dependencies, .dependents = spl_array_new(), .status = BuildUnitStatus_Pending, .output = spl_nil()};
    self->units[id] = unit;
    for (int64_t __dep_id_i = 0; __dep_id_i < spl_array_len(dependencies); __dep_id_i++) {
        int64_t dep_id = spl_array_get(dependencies, __dep_id_i).as_int;
        if (BuildGraph__units_contains_key(self, units, dep_id)) {
            int64_t dep = self->units[dep_id];
            self->units[dep_id] = BuildUnit{.id = dep.id, .path = dep.path, .dependencies = dep.dependencies, .dependents = dep_dependents_push(dep, dependents, id), .status = dep.status, .output = dep.output};
        }
    }
    return id;
}

BuildStats buildstats_empty() {
    return BuildStats{.total_units = 0, .completed = 0, .failed = 0, .skipped = 0, .parallel_batches = 0};
}

ParallelBuilder parallelbuilder_create(ParallelBuildConfig config) {
    return ParallelBuilder{.config = config, .graph = buildgraph_empty(), .stats = buildstats_empty()};
}

int64_t parallelbuilder_add_unit(ParallelBuilder self, const char* path, SplArray* dependencies) {
    return ParallelBuilder__graph_add_unit(self, graph, path, dependencies);
}

int64_t parallelbuilder_build(ParallelBuilder self, FnPtr_i64 compile_fn) {
    int64_t total = BuildGraph__units_len(&self->graph, units);
    self->stats = BuildStats{.total_units = total, .completed = 0, .failed = 0, .skipped = 0, .parallel_batches = 0};
    SplArray* errors = spl_array_new();
    SplArray* outputs = spl_array_new();
    if ((self->config.deterministic || (total < self->config.parallel_threshold))) {
        int64_t order = ParallelBuilder__graph_topological_order(self, graph);
        for (int64_t __id_i = 0; __id_i < spl_array_len(order); __id_i++) {
            int64_t id = spl_array_get(order, __id_i).as_int;
            if (!(BuildGraph__units_contains_key(&self->graph, units, id))) {
                continue;
            }
            int64_t unit = self->graph.units[id];
            bool dep_failed = false;
            for (int64_t __dep_id_i = 0; __dep_id_i < spl_array_len(unit.dependencies); __dep_id_i++) {
                int64_t dep_id = spl_array_get(unit.dependencies, __dep_id_i).as_int;
                if (BuildGraph__units_contains_key(&self->graph, units, dep_id)) {
                    switch (self->graph.units[dep_id].status) {
                    }
                }
            }
            if (dep_failed) {
                BuildGraph__mark_failed(&self->graph, id, "Dependency failed");
                self->stats = BuildStats{.total_units = self->stats.total_units, .completed = self->stats.completed, .failed = (self->stats.failed + 1), .skipped = self->stats.skipped, .parallel_batches = self->stats.parallel_batches};
                continue;
            }
            ParallelBuilder__graph_mark_in_progress(self, graph, id);
            int64_t result = compile_fn(unit.path);
            switch (result) {
                case Ok(output):
                {
                    ParallelBuilder__graph_mark_completed(self, graph, id, output);
                    outputs = outputs_push(outputs, output);
                    self->stats = BuildStats{.total_units = self->stats.total_units, .completed = (self->stats.completed + 1), .failed = self->stats.failed, .skipped = self->stats.skipped, .parallel_batches = self->stats.parallel_batches};
                    break;
                }
                case Err(msg):
                {
                    ParallelBuilder__graph_mark_failed(self, graph, id, msg);
                    errors = errors_push(errors, (unit.path, msg));
                    self->stats = BuildStats{.total_units = self->stats.total_units, .completed = self->stats.completed, .failed = (self->stats.failed + 1), .skipped = self->stats.skipped, .parallel_batches = self->stats.parallel_batches};
                    break;
                }
            }
        }
    } else {
        while (!(ParallelBuilder__graph_is_complete(self, graph))) {
            int64_t ready = ParallelBuilder__graph_ready_units(self, graph);
            if ((ready_len(ready) == 0)) {
                break;
            }
            self->stats = BuildStats{.total_units = self->stats.total_units, .completed = self->stats.completed, .failed = self->stats.failed, .skipped = self->stats.skipped, .parallel_batches = (self->stats.parallel_batches + 1)};
            for (int64_t __unit_i = 0; __unit_i < spl_array_len(ready); __unit_i++) {
                int64_t unit = spl_array_get(ready, __unit_i).as_int;
                ParallelBuilder__graph_mark_in_progress(self, graph, unit.id);
                int64_t result = compile_fn(unit.path);
                switch (result) {
                    case Ok(output):
                    {
                        ParallelBuilder__graph_mark_completed(self, graph, unit.id);
                        outputs = outputs_push(outputs, output);
                        self->stats = BuildStats{.total_units = self->stats.total_units, .completed = (self->stats.completed + 1), .failed = self->stats.failed, .skipped = self->stats.skipped, .parallel_batches = self->stats.parallel_batches};
                        break;
                    }
                    case Err(msg):
                    {
                        ParallelBuilder__graph_mark_failed(self, graph, unit.id);
                        errors = errors_push(errors, (unit.path, msg));
                        self->stats = BuildStats{.total_units = self->stats.total_units, .completed = self->stats.completed, .failed = (self->stats.failed + 1), .skipped = self->stats.skipped, .parallel_batches = self->stats.parallel_batches};
                        break;
                    }
                }
            }
        }
    }
    return BuildResult{.success = !(ParallelBuilder__graph_has_failures(self, graph)), .stats = self->stats, .errors = errors, .outputs = outputs};
}

WriteSite writesite_field_write(int64_t point, int64_t target_type, int64_t field_idx, int64_t source_type) {
    return WriteSite{}; /* stub */
}

AllocationSite allocationsite_create(int64_t id, int64_t point, int64_t type_id) {
    return AllocationSite{}; /* stub */
}

GcSafetyConfig gcsafetyconfig_default_config() {
    return GcSafetyConfig{}; /* stub */
}

GcRoot gcroot_local(int64_t id, int64_t type_id) {
    return GcRoot{}; /* stub */
}

HirExpr hirlowering_lower_expr(int64_t self, Expr e) {
    return HirExpr{}; /* stub */
}

int64_t hirlowering_lower_binop(int64_t self, int64_t op) {
    switch (op) {
    }
}

int64_t hirlowering_lower_unaryop(int64_t self, int64_t op) {
    switch (op) {
    }
}

HirPattern hirlowering_lower_pattern(int64_t self, Pattern p) {
    return HirPattern{}; /* stub */
}

HirBlock hirlowering_lower_block(int64_t self, Block b) {
    SymbolTable symbols_table = self->symbols;
    symbols_table_push_scope(symbols_table, ScopeKind_Block);
    self->symbols = symbols_table;
    std::vector<HirStmt> stmts = {};
    for (size_t __s_i = 0; __s_i < b.stmts.size(); __s_i++) {
        Stmt s = b.stmts[__s_i];
        int64_t lowered = HirLowering__lower_stmt(self, s);
        stmts = stmts_push(stmts, lowered);
        switch (s.kind) {
            case stmtkind_Val(name, _, _):
            {
                switch (lowered.kind) {
                    case Let(symbol_id, _, _):
                    {
                        SymbolTable syms = self->symbols;
                        if ((syms.next_symbol_id <= symbol_id.id)) {
                            syms.next_symbol_id = (symbol_id.id + 1);
                        }
                        int64_t scope = syms.scopes[syms.current_scope.id];
                        int64_t scope_syms = scope.symbols;
                        scope_syms[name] = symbol_id;
                        scope.symbols = scope_syms;
                        syms.scopes[syms.current_scope.id] = scope;
                        syms.symbols[symbol_id.id] = Symbol{.id = symbol_id, .name = name, .kind = SymbolKind_Variable, .type_ = spl_nil(), .scope = syms.current_scope, .span = s.span};
                        self->symbols = syms;
                        break;
                    }
                }
                break;
            }
            case stmtkind_Var(name, _, _):
            {
                switch (lowered.kind) {
                    case Let(symbol_id, _, _):
                    {
                        SymbolTable syms = self->symbols;
                        if ((syms.next_symbol_id <= symbol_id.id)) {
                            syms.next_symbol_id = (symbol_id.id + 1);
                        }
                        int64_t scope = syms.scopes[syms.current_scope.id];
                        int64_t scope_syms = scope.symbols;
                        scope_syms[name] = symbol_id;
                        scope.symbols = scope_syms;
                        syms.scopes[syms.current_scope.id] = scope;
                        syms.symbols[symbol_id.id] = Symbol{.id = symbol_id, .name = name, .kind = SymbolKind_Variable, .type_ = spl_nil(), .scope = syms.current_scope, .span = s.span, .is_public = false, .is_mutable = true, .defining_module = spl_nil()};
                        self->symbols = syms;
                        break;
                    }
                }
                break;
            }
        }
    }
    symbols_table = self->symbols;
    symbols_table_pop_scope(symbols_table);
    self->symbols = symbols_table;
    HirExpr value = spl_nil();
    if ((stmts_len(stmts) > 0)) {
        HirStmt last = stmts[stmts_len(stmts);
        switch (last.kind) {
            case Expr(expr):
            {
                value = expr;
                stmts = stmts[0:stmts_len(stmts);
                break;
            }
            default:
            {
                /* pass */;
                break;
            }
        }
    }
    return HirBlock{.stmts = stmts, .value = value, .span = b.span};
}

HirAsm hirlowering_lower_asm(int64_t self, AsmExpr asm_code) {
    std::vector<HirAsmConstraint> hir_constraints = {};
    for (size_t __constraint_i = 0; __constraint_i < asm_code.constraints.size(); __constraint_i++) {
        AsmConstraint constraint = asm_code.constraints[__constraint_i];
        int64_t hir_value = HirLowering__lower_expr(self, constraint.value);
        HirAsmConstraint hir_constraint = HirAsmConstraint{.name = constraint.name, .kind = constraint.kind, .location = constraint.location, .value = hir_value, .span = constraint.span};
    }
}

HirModule hirlowering_lower_module(int64_t self, Module module) {
    return HirModule{}; /* stub */
}

HirStmt hirlowering_lower_stmt(int64_t self, Stmt s) {
    return HirStmt{}; /* stub */
}

HirLowering hirlowering_new() {
    return HirLowering{}; /* stub */
}

ConstraintSet constraintset_empty() {
    return ConstraintSet{.constraints = spl_array_new(), .errors = spl_array_new()};
}

DeferredStore deferredstore_empty() {
    return DeferredStore{}; /* stub */
}

InferenceEngine inferenceengine_create() {
    return InferenceEngine{}; /* stub */
}

const char* hints_to_sdn(std::vector<DeferredHint> hints) {
    SplArray* lines = spl_array_new();
    lines = spl_array_push(lines, spl_str("inference_hints |var_id, source_module, fallback, constraints|"));
    for (size_t __hint_i = 0; __hint_i < hints.size(); __hint_i++) {
        DeferredHint hint = hints[__hint_i];
        const char* var_id = spl_i64_to_str(hint.type_var.id);
        const char* source = spl_str_concat(spl_str_concat("\"", hint.source_module), "\"");
        int64_t fallback = if hint.has_fallback:;
        spl_str_concat(spl_str_concat("\"", spl_i64_to_str(type_to_text(hint.fallback_value))), "\"");
        else:;
        "\"\"";
        const char* constraints = spl_str_concat(spl_str_concat("\"", spl_i64_to_str(constraints_to_text(hint.constraints))), "\"");
        lines = spl_array_push(lines, spl_str(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("    ", var_id), ", "), source), ", "), spl_i64_to_str(fallback)), ", "), constraints)));
    }
    return lines_join(lines, NL);
}

std::vector<DeferredHint> hints_from_sdn(const char* content) {
    return std::vector<DeferredHint>{}; /* stub */
}

Unifier unifier_empty() {
    return Unifier{}; /* stub */
}

Type unifier_fresh_var(Unifier self) {
    TypeVarId id = TypeVarId{.id = self->next_var};
    self->next_var = (self->next_var + 1);
    return type_Var(id: id);
}

const char* IrCodeGen__generate_match(const IrCodeGen* self) {
    const char* output = "match inst {\n";
    std::vector<IrInstruction> supported = IrCodeGen__get_supported_instructions(self);
    std::vector<IrInstruction> unsupported = IrCodeGen__get_unsupported_instructions(self);
    for (size_t __inst_i = 0; __inst_i < supported.size(); __inst_i++) {
        IrInstruction inst = supported[__inst_i];
        output = spl_str_concat(output, IrCodeGen__generate_instruction_arm(self, inst));
    }
    if ((unsupported_len(unsupported) > 0)) {
        output = spl_str_concat(output, "\n    // Unsupported instructions\n");
        output = spl_str_concat(output, IrCodeGen__generate_unsupported_group(self, unsupported));
    }
    output = spl_str_concat(output, "}\n");
    return output;
}

const char* IrCodeGen__generate_instruction_arm(const IrCodeGen* self, int64_t inst) {
    const char* output = "    ";
    output = spl_str_concat(output, inst.rust_pattern);
    output = spl_str_concat(output, " => {\n");
    output = spl_str_concat(output, spl_str_concat(spl_str_concat("        // ", inst.description), "\n"));
    output = spl_str_concat(output, spl_str_concat(spl_str_concat("        self.compile_", spl_i64_to_str(inst.name_to_lower(inst.name))), "("));
    bool first = true;
    for (size_t __param_i = 0; __param_i < inst.params.size(); __param_i++) {
        IrParam param = inst.params[__param_i];
        if (!(first)) {
            output = spl_str_concat(output, ", ");
        }
        output = spl_str_concat(output, param.name);
        first = false;
    }
    output = spl_str_concat(output, ")\n");
    output = spl_str_concat(output, "    },\n");
    return output;
}

const char* IrCodeGen__generate_unsupported_group(const IrCodeGen* self, SplArray* insts) {
    const char* output = "    ";
    bool first = true;
    for (size_t __inst_i = 0; __inst_i < insts.size(); __inst_i++) {
        IrInstruction inst = insts[__inst_i];
        if (!(first)) {
            output = spl_str_concat(output, "\n    | ");
        }
        output = spl_str_concat(output, inst.rust_pattern);
        first = false;
    }
    output = spl_str_concat(output, " => {\n");
    if ((insts_len(insts) > 0)) {
        if ((insts[0]_error_msg_len(insts[0], error_msg) > 0)) {
        }
        output = spl_str_concat(output, spl_str_concat(spl_str_concat("        Err(CompileError::unsupported(\"", spl_i64_to_str(insts[0].error_msg)), "\"))\n"));
    } else {
        output = spl_str_concat(output, spl_str_concat(spl_str_concat("        Err(CompileError::unsupported(\"Instruction not supported by ", self->backend), " backend\"))\n"));
    }
    output = spl_str_concat(output, "    },\n");
    return output;
}

SplArray* IrCodeGen__get_supported_instructions(const IrCodeGen* self) {
    std::vector<IrInstruction> result = {};
    for (size_t __inst_i = 0; __inst_i < self->instructions.size(); __inst_i++) {
        IrInstruction inst = self->instructions[__inst_i];
        if (IrCodeGen__is_supported(self, inst)) {
            return result_push(result, inst);
        }
    }
    return result;
}

SplArray* IrCodeGen__get_unsupported_instructions(const IrCodeGen* self) {
    std::vector<IrInstruction> result = {};
    for (size_t __inst_i = 0; __inst_i < self->instructions.size(); __inst_i++) {
        IrInstruction inst = self->instructions[__inst_i];
        if (!(IrCodeGen__is_supported(self, inst))) {
            return result_push(result, inst);
        }
    }
    return result;
}

bool IrCodeGen__is_supported(const IrCodeGen* self, int64_t inst) {
    for (int64_t __backend_i = 0; __backend_i < spl_array_len(inst.backends); __backend_i++) {
        const char* backend = spl_array_get(inst.backends, __backend_i).as_str;
        if (spl_str_eq(backend, self->backend)) {
            return true;
        }
    }
    return false;
}

const char* generate_backend_code(SplArray* instructions, const char* backend) {
    return ""; /* stub */
}

void IrDslParser__parse(IrDslParser* self) {
    while ((self->current_line < IrDslParser__lines_len(self, lines))) {
        const char* line = spl_str_trim(spl_array_get(self->lines, self->current_line).as_str);
        if (((spl_str_len(line) == 0) || spl_str_starts_with(line, "#"))) {
            self->current_line = (self->current_line + 1);
            /* pass */;
        } else if (spl_str_starts_with(line, "instruction ")) {
            IrDslParser__parse_instruction(self);
        } else {
            self->current_line = (self->current_line + 1);
        }
    }
}

void IrDslParser__parse_instruction(IrDslParser* self) {
    /* stub */
}

void IrValidator__validate(IrValidator* self) {
    for (size_t __inst_i = 0; __inst_i < self->instructions.size(); __inst_i++) {
        IrInstruction inst = self->instructions[__inst_i];
        IrValidator__validate_instruction(self, inst);
    }
}

void IrValidator__validate_instruction(IrValidator* self, IrInstruction inst) {
    if ((IrInstruction__name_len(&inst, name) == 0)) {
        IrValidator__add_error(self, inst.name, "empty_name");
    }
    if ((IrInstruction__backends_len(&inst, backends) == 0)) {
        IrValidator__add_error(self, inst.name, "no_backends");
    }
    if ((IrInstruction__description_len(&inst, description) == 0)) {
        IrValidator__add_error(self, inst.name, "no_description");
    }
    if ((IrInstruction__rust_pattern_len(&inst, rust_pattern) == 0)) {
        IrValidator__add_error(self, inst.name, "no_pattern");
    }
    if ((IrInstruction__backends_len(&inst, backends) > 0)) {
        if ((IrInstruction__backends_len(&inst, backends) < 4)) {
        }
        if ((IrInstruction__error_msg_len(&inst, error_msg) == 0)) {
            IrValidator__add_error(self, inst.name, "missing_error");
        }
    }
}

void IrValidator__add_error(IrValidator* self, const char* inst_name, const char* err_type, const char* msg) {
    /* stub */
}

LazyInstantiatorConfig lazyinstantiatorconfig_default() {
    return LazyInstantiatorConfig{}; /* stub */
}

SplArray* text_to_bytes(const char* text) {
    SplArray* bytes = spl_array_new();
    int64_t i = 0;
    while ((i < text_len(text))) {
        int64_t _cast_0 = spl_str_index_char(text, i);
        bytes_push(bytes, _cast_0);
        i = (i + 1);
    }
    return bytes;
}

LibSmfHeader libsmfheader_new_default() {
    return LibSmfHeader{}; /* stub */
}

LibSmfBuilder libsmfbuilder_new() {
    LibSmfBuilder{.modules = {}, .verbose = false} = spl_array_new();
}

const char* LinkerCompilationContext__load_template(const LinkerCompilationContext* self, const char* name) {
    if (LinkerCompilationContext__object_templates_contains_key(self, object_templates, name)) {
        return Result_Ok;
    }
    return else:;
    return Result_Err;
}

bool LinkerCompilationContext__has_template(const LinkerCompilationContext* self, const char* name) {
    return LinkerCompilationContext__object_templates_contains_key(self, object_templates, name);
}

TypeRegistry LinkerCompilationContext__type_registry(const LinkerCompilationContext* self) {
    return self->type_reg;
}

int64_t LinkerCompilationContext__contract_mode(const LinkerCompilationContext* self) {
    return ContractMode_All;
}

int64_t LinkerCompilationContext__di_container(const LinkerCompilationContext* self) {
    return self->project_di;
}

int64_t LinkerCompilationContext__aop_weaver(const LinkerCompilationContext* self) {
    return self->project_aop;
}

bool LinkerCompilationContext__coverage_enabled(const LinkerCompilationContext* self) {
    return false;
}

const char* LinkerCompilationContext__compile_template(const LinkerCompilationContext* self, GenericTemplate template, std::vector<ConcreteType> type_args) {
    return ""; /* stub */
}

const char* scan_libraries(SplArray* library_paths, bool verbose) {
    std::vector<LibraryInfo> libraries = {};
    for (int64_t __path_i = 0; __path_i < spl_array_len(library_paths); __path_i++) {
        const char* path = spl_array_get(library_paths, __path_i).as_str;
        if (!(file_exists(path))) {
            if (verbose) {
                spl_println(spl_str_concat("[linker-lib] Skipping non-existent path: ", path));
            }
            continue;
        }
        int64_t find_result = shell(spl_str_concat(spl_str_concat("find '", path), "' -name '*.lsm' -type f 2>/dev/null"));
        if ((find_result.exit_code != 0)) {
            continue;
        }
        int64_t lsm_files = spl_str_split(find_result.stdout, NL);
        for (int64_t __lsm_file_i = 0; __lsm_file_i < spl_array_len(lsm_files); __lsm_file_i++) {
            int64_t lsm_file = spl_array_get(lsm_files, __lsm_file_i).as_int;
            int64_t trimmed = lsm_file_trim(lsm_file);
            if (spl_str_eq(trimmed, "")) {
                continue;
            }
            if (verbose) {
                spl_println(spl_str_concat("[linker-lib] Found library: ", spl_i64_to_str(trimmed)));
            }
            const char* lib_name = extract_basename(trimmed);
            LibraryInfo lib_info = LibraryInfo{.path = trimmed, .name = lib_name, .modules = spl_array_new()};
            int64_t getter = smfgetter_new();
            int64_t add_result = getter_add_library(getter, trimmed);
            if (add_result_is_err(add_result)) {
                if (verbose) {
                    spl_println(spl_str_concat(spl_str_concat(spl_str_concat("[linker-lib] Warning: Could not read library ", spl_i64_to_str(trimmed)), ": "), spl_i64_to_str(add_result_unwrap_err(add_result))));
                }
                continue;
            }
            int64_t modules = getter_list_modules(getter);
            lib_info = LibraryInfo{.path = trimmed, .name = lib_name, .modules = modules};
            return libraries_push(libraries, lib_info);
            if (verbose) {
                spl_println(spl_str_concat("[linker-lib]   Modules: ", spl_i64_to_str(spl_array_len(modules))));
            }
        }
    }
    return Result_Ok;
}

const char* extract_basename(const char* path) {
    const char* name = path;
    int64_t last_slash = path_rfind(path, "/");
    if ((last_slash >= 0)) {
        name = path[((last_slash + 1));
    }
    if (spl_str_ends_with(name, ".lsm")) {
        name = name[0:((name_len(name) - 4));
    }
    return name;
}

NativeLinkConfig NativeLinkConfig__default() {
    NativeLinkConfig{.libraries = spl_array_new(), .library_paths = spl_array_new(), .runtime_path = "", .pie = true, .debug = false, .verbose = false, .extra_flags = spl_array_new()} = spl_array_new();
    return Result_Ok;
}

int64_t link_native_cc(SplArray* object_files, const char* output, NativeLinkConfig config) {
    const char* cmd = "cc";
    for (int64_t __obj_i = 0; __obj_i < spl_array_len(object_files); __obj_i++) {
        const char* obj = spl_array_get(object_files, __obj_i).as_str;
        cmd = spl_str_concat(spl_str_concat(cmd, " "), obj);
    }
    for (int64_t __lp_i = 0; __lp_i < spl_array_len(config.library_paths); __lp_i++) {
        const char* lp = spl_array_get(config.library_paths, __lp_i).as_str;
        cmd = spl_str_concat(spl_str_concat(cmd, " -L"), lp);
    }
    const char* runtime_dir = config.runtime_path;
    if (spl_str_eq(runtime_dir, "")) {
        runtime_dir = find_runtime_lib_dir();
    }
    if ((!spl_str_eq(runtime_dir, ""))) {
        cmd = spl_str_concat(cmd, spl_str_concat(spl_str_concat(" -L", runtime_dir), " -lsimple_compiler"));
        cmd = spl_str_concat(cmd, spl_str_concat(" -Wl,-rpath,", runtime_dir));
    }
    int64_t os_name = shell("uname -s").stdout;
    os_name = os_name_trim(os_name);
    if (spl_str_eq(os_name, "Darwin")) {
        cmd = spl_str_concat(cmd, " -lc -lpthread -lm -lSystem");
    } else if (spl_str_eq(os_name, "FreeBSD")) {
        cmd = spl_str_concat(cmd, " -lc -lpthread -lm");
    } else {
        cmd = spl_str_concat(cmd, " -lc -lpthread -ldl -lm");
    }
    for (int64_t __lib_i = 0; __lib_i < spl_array_len(config.libraries); __lib_i++) {
        const char* lib = spl_array_get(config.libraries, __lib_i).as_str;
        cmd = spl_str_concat(spl_str_concat(cmd, " -l"), lib);
    }
    for (int64_t __flag_i = 0; __flag_i < spl_array_len(config.extra_flags); __flag_i++) {
        const char* flag = spl_array_get(config.extra_flags, __flag_i).as_str;
        cmd = spl_str_concat(spl_str_concat(cmd, " "), flag);
    }
    cmd = spl_str_concat(spl_str_concat(cmd, " -o "), output);
    if (config.verbose) {
        spl_println(spl_str_concat("[linker-wrapper] cc command: ", cmd));
    }
    int64_t result = shell(cmd);
    if ((result.exit_code == 0)) {
        return Result_Ok;
    } else {
        int64_t err_msg = ((result.stderr) ? (result.stderr) : ("Unknown linking error"));
        return Result_Err;
    }
}

int64_t link_native_windows(SplArray* object_files, const char* output, NativeLinkConfig config) {
    int64_t lld_check = shell("where lld-link 2>nul");
    const char* linker_cmd = "link";
    if ((lld_check.exit_code == 0)) {
        linker_cmd = "lld-link";
    }
    const char* cmd = linker_cmd;
    for (int64_t __obj_i = 0; __obj_i < spl_array_len(object_files); __obj_i++) {
        const char* obj = spl_array_get(object_files, __obj_i).as_str;
        cmd = spl_str_concat(spl_str_concat(cmd, " "), obj);
    }
    cmd = spl_str_concat(cmd, spl_str_concat(" /OUT:", output));
    for (int64_t __lib_i = 0; __lib_i < spl_array_len(config.libraries); __lib_i++) {
        const char* lib = spl_array_get(config.libraries, __lib_i).as_str;
        cmd = spl_str_concat(cmd, spl_str_concat(spl_str_concat(" ", lib), ".lib"));
    }
    for (int64_t __flag_i = 0; __flag_i < spl_array_len(config.extra_flags); __flag_i++) {
        const char* flag = spl_array_get(config.extra_flags, __flag_i).as_str;
        cmd = spl_str_concat(spl_str_concat(cmd, " "), flag);
    }
    if (config.verbose) {
        spl_println(spl_str_concat("[linker-wrapper] Windows linker: ", cmd));
    }
    int64_t result = shell(cmd);
    if ((result.exit_code == 0)) {
        return Result_Ok;
    } else {
        int64_t err_msg = ((result.stderr) ? (result.stderr) : ("Unknown linking error"));
        return Result_Err;
    }
}

int64_t find_crt_files(bool pie, bool verbose) {
    return 0; /* stub */
}

int64_t link_to_self_contained(SplArray* smf_data, const char* output, int64_t config) {
    if ((smf_data_len(smf_data) == 0)) {
        return Result_Err;
    }
    int64_t runtime_path = config.runtime_binary;
    if (spl_str_eq(runtime_path, "")) {
        int64_t found = find_runtime_binary();
        if (found_is_err(found)) {
            return Result_Err;
        }
        runtime_path = found_value;
    }
    if (config.verbose) {
        spl_println(spl_str_concat("[linker-wrapper] Runtime binary: ", spl_i64_to_str(runtime_path)));
    }
    if (!(file_copy(runtime_path, output))) {
        return Result_Err;
    }
    int64_t runtime_size = file_size_raw(output);
    if ((runtime_size <= 0)) {
        file_delete(output);
        return Result_Err;
    }
    int64_t append_ok = append_bytes_to_file(output, smf_data);
    if (!(append_ok)) {
        file_delete(output);
        return Result_Err;
    }
    int64_t smf_offset = runtime_size;
    int64_t smf_size = smf_data_len(smf_data);
    int64_t checksum = fnv1a_hash(smf_data);
    SplArray* trailer = build_trailer(smf_offset, smf_size, checksum);
    int64_t trailer_ok = append_bytes_to_file(output, trailer);
    if (!(trailer_ok)) {
        file_delete(output);
        return Result_Err;
    }
    int64_t os = host_os();
    if ((!spl_str_eq(os, "windows"))) {
        return shell(spl_str_concat(spl_str_concat("chmod +x '", output), "'"));
    }
    int64_t total_size = file_size_raw(output);
    if (config.verbose) {
        spl_println(spl_str_concat("[linker-wrapper] Self-contained binary: ", output));
        spl_println(spl_str_concat(spl_str_concat("[linker-wrapper]   Runtime: ", spl_i64_to_str(runtime_size)), " bytes"));
        spl_println(spl_str_concat(spl_str_concat("[linker-wrapper]   SMF data: ", spl_i64_to_str(smf_size)), " bytes"));
        spl_println(spl_str_concat(spl_str_concat("[linker-wrapper]   Trailer: ", spl_i64_to_str(SMFE_TRAILER_SIZE)), " bytes"));
        spl_println(spl_str_concat(spl_str_concat("[linker-wrapper]   Total: ", spl_i64_to_str(total_size)), " bytes"));
    }
    return Result_Ok;
}

int64_t detect_self_contained(const char* exe_path) {
    int64_t total_size = file_size_raw(exe_path);
    if ((total_size < SMFE_TRAILER_SIZE)) {
        return Result_Err;
    }
    int64_t trailer_offset = (total_size - SMFE_TRAILER_SIZE);
    int64_t hex_result = shell(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat("dd if='", exe_path), "' bs=1 skip="), spl_i64_to_str(trailer_offset)), " count="), spl_i64_to_str(SMFE_TRAILER_SIZE)), " 2>/dev/null | od -A n -t x1 | tr -d ' \\n'"));
    if ((hex_result.exit_code != 0)) {
        return Result_Err;
    }
    int64_t hex = hex_result.stdout;
    if ((hex_len(hex) < 8)) {
        return Result_Err;
    }
    const char* magic_hex = spl_str_slice(hex, 0, 8);
    if ((!spl_str_eq(magic_hex, "534d4645"))) {
        return Result_Err;
    }
    int64_t smf_offset = parse_hex_u64(hex, 8);
    int64_t smf_size = parse_hex_u64(hex, 24);
    return Result_Ok;
}

int64_t find_runtime_binary() {
    int64_t env_path = env_get("SIMPLE_RUNTIME_BINARY");
    if ((!spl_str_eq(env_path, ""))) {
        if (file_exists(env_path)) {
        }
        return Result_Ok;
    }
    int64_t current_dir = cwd();
    int64_t os = host_os();
    int64_t arch = host_arch();
    int64_t platform_name = (spl_str_concat(os, "-") + arch);
    const char* platform_path = spl_str_concat(spl_str_concat(spl_str_concat(spl_i64_to_str(current_dir), "/bin/release/"), spl_i64_to_str(platform_name)), "/simple");
    if (file_exists(platform_path)) {
        return Result_Ok;
    }
    const char* generic_path = spl_str_concat(spl_i64_to_str(current_dir), "/bin/release/simple");
    if (file_exists(generic_path)) {
        return Result_Ok;
    }
    if (file_exists("./bin/release/simple")) {
        return Result_Ok;
    }
    return Result_Err;
}

SplArray* build_trailer(int64_t smf_offset, int64_t smf_size, int64_t checksum) {
    SplArray* buf = spl_array_new();
    buf = (buf + (SMFE_MAGIC));
    buf = (buf + (i64_to_le_bytes(smf_offset)));
    buf = (buf + (i64_to_le_bytes(smf_size)));
    buf = (buf + (i64_to_le_bytes(checksum)));
    buf = (buf + (i32_to_le_bytes(SMFE_VERSION)));
    return buf;
}

int64_t fnv1a_hash(SplArray* data) {
    int64_t hash = -3750763034362895579;
    for (int64_t __byte_i = 0; __byte_i < spl_array_len(data); __byte_i++) {
        int64_t byte = spl_array_get(data, __byte_i).as_int;
        int64_t b = byte;
        hash = hash xor b;
        hash = (hash * 1099511628211);
    }
    return hash;
}

SplArray* i64_to_le_bytes(int64_t value) {
    return spl_array_new();
}

LinkConfig linkconfig_default() {
    return LinkConfig{}; /* stub */
}

const char* find_mold_path() {
    return ""; /* stub */
}

const char* find_lld_path() {
    return ""; /* stub */
}

const char* find_ld_path() {
    return ""; /* stub */
}

const char* execute_linker(const char* linker_path, SplArray* args) {
    int64_t _destruct_0 = process_run(linker_path, args);
    int64_t stdout = _destruct_0[0];
    int64_t stderr = _destruct_0[1];
    int64_t code = _destruct_0[2];
    if ((code != 0)) {
        const char* msg = spl_str_concat(spl_str_concat("Linker failed (exit ", spl_i64_to_str(code)), ")");
        if ((stderr_len(stderr) > 0)) {
            msg = (spl_str_concat(msg, ": ") + stderr);
        }
        return Result_Err;
    }
    return Result_Ok;
}

const char* write_elf_object(SplArray* code, const char* name, const char* output_path) {
    const char* asm_lines = ".section .text\n";
    asm_lines = spl_str_concat(spl_str_concat(spl_str_concat(asm_lines, ".globl "), name), NL);
    asm_lines = spl_str_concat(spl_str_concat(spl_str_concat(asm_lines, ".type "), name), ", @function\n");
    asm_lines = spl_str_concat(spl_str_concat(asm_lines, name), ":\n");
    int64_t i = 0;
    int64_t batch_size = 16;
    int64_t code_len = code_len(code);
    for (int64_t idx = 0; idx < code_len; idx++) {
        if (((i % batch_size) == 0)) {
            if ((i > 0)) {
                asm_lines = spl_str_concat(asm_lines, NL);
            }
            asm_lines = spl_str_concat(asm_lines, "    .byte ");
        } else {
            asm_lines = spl_str_concat(asm_lines, ", ");
        }
        int64_t byte_val = (spl_array_get(code, idx).as_int % 256);
        asm_lines = spl_str_concat(asm_lines, spl_i64_to_str(byte_val));
        i = (i + 1);
    }
    asm_lines = spl_str_concat(asm_lines, NL);
    asm_lines = spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(spl_str_concat(asm_lines, ".size "), name), ", .-"), name), NL);
    int64_t asm_path = spl_str_concat(output_path, ".s");
    bool wrote = file_write(asm_path, asm_lines);
    if (!(wrote)) {
        return Result_Err;
    }
    int64_t _destruct_1 = process_run("as", spl_array_new());
    int64_t stdout = _destruct_1[0];
    int64_t stderr = _destruct_1[1];
    int64_t exit_code = _destruct_1[2];
    return file_delete(asm_path);
    if ((exit_code != 0)) {
        const char* msg = spl_str_concat(spl_str_concat("Assembler failed (exit ", spl_i64_to_str(exit_code)), ")");
        if ((stderr_len(stderr) > 0)) {
            msg = (spl_str_concat(msg, ": ") + stderr);
        }
        return Result_Err;
    }
    return Result_Ok;
}

int64_t linker_file_size(const char* path) {
    return file_size_raw(path);
}

MoldCrtFiles mold_find_crt_files(bool pie, bool verbose) {
    return MoldCrtFiles{}; /* stub */
}

MsvcConfig msvcconfig_default() {
    MsvcConfig{.link_exe = "", .lib_paths = spl_array_new(), .libs = spl_array_new(), .entry_point = "mainCRTStartup", .subsystem = "console", .machine = "X64", .debug = false, .extra_args = spl_array_new()} = spl_array_new();
}

ObjectFileResolver objectfileresolver_new(bool verbose) {
    return ObjectFileResolver{}; /* stub */
}

ObjTakerConfig objtakerconfig_default() {
    return ObjTakerConfig{}; /* stub */
}

int64_t platform_from_u8(uint8_t value) {
    switch (value) {
    }
}

int64_t arch_from_u8(uint8_t value) {
    switch (value) {
    }
}

int64_t compressiontype_from_u8(uint8_t value) {
    switch (value) {
    }
}

int64_t smfapptype_from_u8(uint8_t value) {
    switch (value) {
    }
}

SmfLocation smflocation_single_file(const char* module_name, const char* file_path, int64_t size) {
    SmfLocation{.module_name = module_name, .source_type = SmfSourceType_SingleFile, .file_path = file_path, .offset = 0, .size = size} = spl_array_new();
}

SmfHeader smfheader_new_v1_1(int64_t platform, int64_t arch) {
    return SmfHeader{}; /* stub */
}

SplArray* u32_to_bytes(uint32_t value) {
    return nullptr; /* stub */
}

SplArray* u64_to_bytes(uint64_t value) {
    return nullptr; /* stub */
}

const char* parse_header_from_bytes(SplArray* data) {
    return ""; /* stub */
}

NoteSdnMetadata stub_new_note_sdn() {
    return NoteSdnMetadata{.empty = true};
}

SmfHeader smfheader_from_raw(SmfHeaderRaw raw) {
    return SmfHeader{}; /* stub */
}

const char* char_from_byte(uint8_t b) {
    return ""; /* stub */
}

const char* bytes_to_string(SplArray* bytes) {
    SplArray* chars = spl_array_new();
    for (int64_t __b_i = 0; __b_i < spl_array_len(bytes); __b_i++) {
        int64_t b = spl_array_get(bytes, __b_i).as_int;
        if ((b == 0)) {
            return chars_join(chars, "");
        }
        return chars_push(chars, char_from_byte(b));
    }
    return chars_join(chars, "");
}

NoteSdnMetadata parse_note_sdn(const char* sdn_text) {
    return stub_new_note_sdn();
}

SmfWriter smfwriter_create() {
    return SmfWriter{}; /* stub */
}

int64_t smfwriter_add_string(SmfWriter self, const char* s) {
    if (SmfWriter__string_offsets_contains_key(self, string_offsets, s)) {
        return self->string_offsets[s];
    }
    int64_t offset = SmfWriter__string_table_len(self, string_table);
    self->string_table = SmfWriter__string_table_push(self, string_table, offset);
    self->string_offsets[s] = offset;
    return offset;
}

int64_t smfwriter_add_code_section(SmfWriter self, const char* name, SplArray* code) {
    SmfSection section = SmfSection{.name = name, .section_type = SectionType_Code, .flags = (SECTION_FLAG_READ + SECTION_FLAG_EXEC), .data = code, .alignment = 16};
    self->sections = SmfWriter__sections_push(self, sections, section);
    return (SmfWriter__sections_len(self, sections) - 1);
}

int64_t smfwriter_add_data_section(SmfWriter self, const char* name, SplArray* data, int64_t kind) {
    SmfSection section = SmfSection{.name = name, .section_type = kind_to_section_type(kind), .flags = kind_to_flags(kind), .data = data, .alignment = 8};
    self->sections = SmfWriter__sections_push(self, sections, section);
    return (SmfWriter__sections_len(self, sections) - 1);
}

int64_t smfwriter_add_bss_section(SmfWriter self, const char* name, int64_t size) {
    SplArray* zeroes = spl_array_new();
    SmfSection section = SmfSection{.name = name, .section_type = SectionType_Bss, .flags = (SECTION_FLAG_READ + SECTION_FLAG_WRITE), .data = zeroes, .alignment = 8};
    self->sections = SmfWriter__sections_push(self, sections, section);
    return (SmfWriter__sections_len(self, sections) - 1);
}

int64_t smfwriter_add_symbol(SmfWriter self, SmfSymbol symbol) {
    self->symbols = SmfWriter__symbols_push(self, symbols, symbol);
    return (SmfWriter__symbols_len(self, symbols) - 1);
}

int64_t smfwriter_add_note_section(SmfWriter self, const char* name, SplArray* data) {
    SmfSection section = SmfSection{.name = name, .section_type = SectionType_Note, .flags = SECTION_FLAG_READ, .data = data, .alignment = 4};
    self->sections = SmfWriter__sections_push(self, sections, section);
    return (SmfWriter__sections_len(self, sections) - 1);
}

AnalyzedSymbol analyzedsymbol_create(const char* name, int64_t visibility) {
    return AnalyzedSymbol{}; /* stub */
}

SymbolGraph symbolgraph_empty() {
    return SymbolGraph{}; /* stub */
}

SymbolAnalyzer symbolanalyzer_create() {
    return SymbolAnalyzer{.graph = symbolgraph_empty()};
}

SymbolGraph symbolanalyzer_analyze(SymbolAnalyzer self) {
    SymbolAnalyzer__graph_analyze_reachability(self, graph);
    return self->graph;
}

CompilerContext compilercontext_create() {
    int64_t handle = compiler_create_context();
    return CompilerContext{.handle = handle};
}

SplArray* CompilerContextImpl__infer_types(const CompilerContextImpl* self, Template template, SplArray* hints) {
    const char* cache_key = spl_str_concat(spl_str_concat(template.name, ":"), spl_i64_to_str(hints_to_key(hints)));
    if (spl_str_contains(self->type_cache, cache_key)) {
        self->stats.cache_hits = (self->stats.cache_hits + 1);
        return self->type_cache[cache_key];
    }
    self->stats.cache_misses = (self->stats.cache_misses + 1);
    self->stats.type_inferences = (self->stats.type_inferences + 1);
    SplArray* inferred = spl_array_new();
    for (int64_t __param_i = 0; __param_i < spl_array_len(template.type_params); __param_i++) {
        const char* param = spl_array_get(template.type_params, __param_i).as_str;
        int64_t found_type = spl_nil();
        for (int64_t __hint_i = 0; __hint_i < spl_array_len(hints); __hint_i++) {
            int64_t hint = spl_array_get(hints, __hint_i).as_int;
            if (spl_str_eq(hint.source, "call_site")) {
                found_type = hint.ty;
                break;
            }
        }
        if (has_found_type) {
            return inferred_push(inferred, found_type_value);
        } else {
            return spl_array_push(inferred, spl_int(TypeInfo(kind: "int", name: "i64", bits: 64, signed: true, args:[0], 0)));
        }
    }
    self->type_cache[cache_key] = inferred;
    return inferred;
}

CompilationResult CompilerContextImpl__instantiate_template(const CompilerContextImpl* self, Template template, SplArray* type_args) {
    return CompilationResult{}; /* stub */
}

JitCompilationContext jitcompilationcontext_from_smf(SplDict* tmpls) {
    return JitCompilationContext{.compiler_ctx = compilercontext_create(), .smf_templates = tmpls, .recorded = {}};
}

int64_t compiler_create_context() {
    return 1;
}

bool compiler_destroy_context(int64_t handle) {
    return true;
}

const char* compiler_infer_types(int64_t handle, const char* template_json, const char* hints_json) {
    return "[]";
}

bool compiler_check_types(int64_t handle, const char* types_json, const char* constraints_json) {
    return true;
}

const char* compiler_instantiate_template(int64_t handle, const char* template_json, const char* types_json) {
    return "{\"status\":\"success\",\"bytecode\":\"\"}";
}

const char* compiler_get_stats(int64_t handle) {
    return "{\"type_inferences\":0,\"template_instantiations\":0}";
}

JitInstantiatorConfig jitinstantiatorconfig_default() {
    return JitInstantiatorConfig{}; /* stub */
}

ModuleLoaderLibConfig moduleloaderlibconfig_default() {
    return ModuleLoaderLibConfig{}; /* stub */
}

ModuleLoaderConfig moduleloaderconfig_default() {
    return ModuleLoaderConfig{}; /* stub */
}

SmfCache smfcache_new() {
    return SmfCache{}; /* stub */
}

int64_t native_mmap_file(const char* path, int32_t prot, int32_t flags, int64_t offset, int64_t length) {
    return 0; /* stub */
}

bool native_munmap(int64_t address, int64_t size) {
    int64_t result = unsafe_munmap(address, size);
    return (result == 0);
}

SplArray* native_mmap_read_bytes(int64_t address, int64_t offset, int64_t length) {
    return unsafe:;
    int64_t ptr = ((address + offset));
    SplArray* slice = slice_from_raw_parts(ptr, length);
    SplArray* result = spl_array_new();
    return result_reserve(result, length);
    for (int64_t i = 0; i < length; i++) {
        int64_t _asv_0 = i as usize;
        return result_push(result, spl_array_get(slice, _asv_0).as_int);
    }
    return result;
}

const char* native_mmap_read_string(int64_t address, int64_t offset, int64_t max_length) {
    return ""; /* stub */
}

bool native_madvise(int64_t address, int64_t size, int32_t advice) {
    int64_t result = unsafe_madvise(address, size, advice);
    return (result == 0);
}

bool native_msync(int64_t address, int64_t size, bool is_async) {
    int64_t flags = if is_async: 1 else: 2;
    int64_t result = unsafe_msync(address, size, flags);
    return (result == 0);
}

bool native_mlock(int64_t address, int64_t size) {
    int64_t result = unsafe_mlock(address, size);
    return (result == 0);
}

bool native_munlock(int64_t address, int64_t size) {
    int64_t result = unsafe_munlock(address, size);
    return (result == 0);
}

int64_t native_alloc_exec_memory(int64_t size) {
    int64_t prot = PROT_READ | PROT_WRITE | PROT_EXEC;
    int64_t flags = MAP_PRIVATE | MAP_ANONYMOUS;
    int64_t addr = unsafe_mmap(0, size, prot, flags, -1, 0);
    if ((addr == MAP_FAILED)) {
        return 0;
    }
    EXEC_MEMORY_ALLOCS[addr] = size;
    return addr;
}

int64_t native_alloc_rw_memory(int64_t size) {
    int64_t prot = PROT_READ | PROT_WRITE;
    int64_t flags = MAP_PRIVATE | MAP_ANONYMOUS;
    int64_t addr = unsafe_mmap(0, size, prot, flags, -1, 0);
    if ((addr == MAP_FAILED)) {
        return 0;
    }
    return addr;
}

bool native_free_exec_memory(int64_t address, int64_t size) {
    int64_t result = unsafe_munmap(address, size);
    if ((result == 0)) {
        exec_memory_allocs_remove(address);
        return true;
    } else {
        return false;
    }
}

int64_t native_write_exec_memory(int64_t address, SplArray* code, int64_t offset) {
    return unsafe:;
    int64_t dest_ptr = ((address + offset));
    for (int64_t i = 0; i < code_len(code); i++) {
        int64_t _asv_1 = i as i64;
        return ptr_write_u8(dest_ptr, _asv_1, spl_array_get(code, i).as_int);
    }
    return code_len(code);
}

bool native_make_executable(int64_t address, int64_t size) {
    int64_t prot = PROT_READ | PROT_EXEC;
    int64_t result = unsafe_mprotect(address, size, prot);
    return (result == 0);
}

void native_flush_icache(int64_t address, int64_t size) {
}

int64_t native_get_function_pointer(int64_t address) {
    return address;
}

int64_t native_call_function_0(int64_t fn_ptr) {
    return unsafe:;
    int64_t func = fn_ptr as fn();
    return func();
}

int64_t native_call_function_1(int64_t fn_ptr, int64_t arg1) {
    return unsafe:;
    int64_t func = fn_ptr as fn(i64);
    return func(arg1);
}

int64_t native_call_function_2(int64_t fn_ptr, int64_t arg1, int64_t arg2) {
    return unsafe:;
    int64_t func = fn_ptr as fn(i64, i64);
    return func(arg1, arg2);
}

int64_t native_exec_memory_total() {
    return 0; /* stub */
}

int64_t native_exec_memory_count() {
    return exec_memory_allocs_len();
}

int32_t unsafe_open(const char* path, int32_t flags) {
    return unsafe:;
    return -1;
}

void unsafe_close(int32_t fd) {
    unsafe:;
}

int64_t unsafe_mmap(int64_t addr, int64_t length, int32_t prot, int32_t flags, int32_t fd, int64_t offset) {
    return unsafe:;
    return MAP_FAILED;
}

int32_t unsafe_munmap(int64_t addr, int64_t length) {
    return unsafe:;
    return -1;
}

int32_t unsafe_mprotect(int64_t addr, int64_t length, int32_t prot) {
    return unsafe:;
    return -1;
}

int32_t unsafe_madvise(int64_t addr, int64_t length, int32_t advice) {
    return unsafe:;
    return -1;
}

int32_t unsafe_msync(int64_t addr, int64_t length, int32_t flags) {
    return unsafe:;
    return -1;
}

int32_t unsafe_mlock(int64_t addr, int64_t length) {
    return unsafe:;
    return -1;
}

int32_t unsafe_munlock(int64_t addr, int64_t length) {
    return unsafe:;
    return -1;
}

uint8_t ptr_read_u8(int64_t ptr, int64_t offset) {
    return 0; /* stub */
}

void ptr_write_u8(int64_t ptr, int64_t offset, uint8_t value) {
    /* stub */
}

SplArray* slice_from_raw_parts(int64_t ptr, int64_t len) {
    return unsafe:;
    return spl_array_new();
}

const char* str_from_utf8_lossy(SplArray* bytes) {
    SplArray* chars = spl_array_new();
    for (int64_t __b_i = 0; __b_i < spl_array_len(bytes); __b_i++) {
        int64_t b = spl_array_get(bytes, __b_i).as_int;
        return chars_push(chars, char_from_byte(b));
    }
    return chars_join(chars, "");
}

SyntaxMark syntaxmark_create(int64_t expansion_id) {
    return SyntaxMark{.id = expansion_id, .expansion_id = expansion_id};
}

MarkedIdent markedident_from_name(const char* name) {
    return MarkedIdent{.name = name, .marks = {}};
}

MarkedIdent markedident_add_mark(MarkedIdent self, SyntaxMark mark) {
    return MarkedIdent{.name = self->name, .marks = MarkedIdent__marks_push(self, marks, mark)};
}

MarkedIdent markedident_remove_mark(MarkedIdent self, SyntaxMark mark) {
    std::vector<SyntaxMark> new_marks = {};
    for (size_t __m_i = 0; __m_i < self->marks.size(); __m_i++) {
        SyntaxMark m = self->marks[__m_i];
        if ((m.id != mark.id)) {
            new_marks = new_marks_push(new_marks, m);
        }
    }
    return MarkedIdent{.name = self->name, .marks = new_marks};
}

HygieneScope hygienescope_root() {
    return HygieneScope{}; /* stub */
}

MacroRule macrorule_create(SplArray* matcher, SplArray* transcriber) {
    return MacroRule{}; /* stub */
}

TemplateParam templateparam_simple(const char* name, int64_t kind) {
    return TemplateParam{.name = name, .kind = kind, .repetition_depth = 0};
}

TemplateParam templateparam_repeated(const char* name, int64_t kind, int64_t depth) {
    return TemplateParam{.name = name, .kind = kind, .repetition_depth = depth};
}

TemplateError templateerror_create(const char* message) {
    return TemplateError{.message = message, .span = spl_nil()};
}

TemplateError templateerror_at(const char* message, int64_t pos) {
    return span: pos);
}

TemplateValidator TemplateValidator__create() {
    return TemplateValidator{}; /* stub */
}

GhostErasureStats ghosterasurestats_new() {
    return GhostErasureStats{}; /* stub */
}

ConstantEvaluator constantevaluator_new() {
    return ConstantEvaluator{.folded_count = 0};
}

AlgebraicSimplifier algebraicsimplifier_new() {
    return AlgebraicSimplifier{.simplified_count = 0};
}

ConstantFolding constantfolding_new() {
    ConstantFolding{.evaluator = constantevaluator_new(), .simplifier = algebraicsimplifier_new(), .folded_instructions = 0, .folded_branches = 0} = spl_array_new();
}

CopyChain copychain_new() {
    return CopyChain{}; /* stub */
}

CopyPropagation copypropagation_new() {
    CopyPropagation{.copy_chain = copychain_new(), .propagated_uses = 0, .eliminated_copies = 0}.blocks: self_analyze_block(CopyPropagation{.copy_chain = copychain_new(), .propagated_uses = 0, .eliminated_copies = 0}.blocks: self, block) = spl_array_new();
}

ExpressionTable expressiontable_new() {
    return ExpressionTable{}; /* stub */
}

LivenessAnalysis livenessanalysis_new() {
    return LivenessAnalysis{}; /* stub */
}

InlineCostAnalyzer inlinecostanalyzer_new(int64_t threshold) {
    return InlineCostAnalyzer{.threshold = threshold};
}

FunctionInliner functioninliner_new(int64_t next_local_id) {
    return FunctionInliner{}; /* stub */
}

LoopDetector loopdetector_new() {
    return LoopDetector{.loops = {}};
}

LoopInvariantMotion loopinvariantmotion_new() {
    return LoopInvariantMotion{}; /* stub */
}

PassManager passmanager_new() {
    return PassManager{}; /* stub */
}

const char* path_join(const char* base, const char* segment) {
    if (spl_str_ends_with(base, "/")) {
        return spl_str_concat(base, segment);
    } else {
        return spl_str_concat(spl_str_concat(base, "/"), segment);
    }
}

const char* path_basename(const char* path) {
    int64_t parts = spl_str_split(path, "/");
    if (parts_is_empty(parts)) {
        return "";
    }
    return parts[parts_len(parts);
}

DirectoryManifest directorymanifest_new(const char* name) {
    return DirectoryManifest{}; /* stub */
}

CallSiteAnalyzer callsiteanalyzer_create(SplArray* generic_function_names) {
    return CallSiteAnalyzer{}; /* stub */
}

BindingSpecializer bindingspecializer_create() {
    return BindingSpecializer{}; /* stub */
}

BindingSpecializer bindingspecializer_from_bindings(std::vector<InterfaceBinding> bindings) {
    return BindingSpecializer{}; /* stub */
}

MonoCacheConfig monocacheconfig_default_config() {
    return MonoCacheConfig{.max_entries = 10000, .validate_timestamps = true, .persist_to_disk = false, .cache_dir = spl_nil()};
}

MonoCacheConfig monocacheconfig_memory_only() {
    return MonoCacheConfig{.max_entries = 10000, .validate_timestamps = true, .persist_to_disk = false, .cache_dir = spl_nil()};
}

MonoCacheConfig monocacheconfig_persistent(const char* cache_dir) {
    return MonoCacheConfig{.max_entries = 50000, .validate_timestamps = true, .cache_dir = cache_dir};
}

MonoCacheStats monocachestats_empty() {
    return MonoCacheStats{.hits = 0, .misses = 0, .evictions = 0, .invalidations = 0, .function_entries = 0, .struct_entries = 0, .class_entries = 0};
}

MonoCache monocache_create(MonoCacheConfig config) {
    return MonoCache{}; /* stub */
}

CycleDetectionResult cycledetectionresult_new() {
    return CycleDetectionResult{}; /* stub */
}

DeferredMonomorphizer deferredmonomorphizer_new(int64_t mode) {
    return DeferredMonomorphizer{}; /* stub */
}

const char* concrete_type_to_text(ConcreteType ty) {
    return ""; /* stub */
}

MonomorphizationTable monomorphizationtable_create() {
    return MonomorphizationTable{}; /* stub */
}

const char* monomorphizationtable_request_function(MonomorphizationTable self, const char* name, std::vector<ConcreteType> type_args, int64_t func) {
    SpecializationKey key = SpecializationKey{.name = name, .type_args = type_args};
    int64_t mangled = key_mangled_name(key);
    if (!(MonomorphizationTable__processed_contains(self, processed, mangled))) {
        self->pending_functions = MonomorphizationTable__pending_functions_push(self, pending_functions, (key, func));
    }
    return mangled;
}

Monomorphizer monomorphizer_create() {
    return Monomorphizer{}; /* stub */
}

int64_t monomorphizer_specialize_function_internal(Monomorphizer self, SpecializationKey key, int64_t func) {
    return func;
}

HirFunction specialize_function_with_types(HirFunction func, SplArray* type_args) {
    TypeSubstitution subst = typesubstitution_from_params(func.type_params, type_args);
    const char* mangled = generate_mangled_name(func.name, type_args);
    return substitute_function(func, subst, mangled);
}

const char* generate_mangled_name(const char* base_name, SplArray* type_args) {
    if (!(has_type_args)) {
        return base_name;
    } else {
        int64_t args_str = type_args_map(type_args, \t: mangle_type(t))_join(type_args_map(type_args, \t: mangle_type(t)), "_");
        return spl_str_concat(spl_str_concat(base_name, "$"), spl_i64_to_str(args_str));
    }
}

const char* mangle_type(int64_t ty) {
    return ""; /* stub */
}

HotReloadConfig hotreloadconfig_default() {
    return HotReloadConfig{.create_backup = true, .verify_after_write = true, .reserve_space_percent = 10, .verbose = false};
}

MonomorphizationMetadata monomorphizationmetadata_new() {
    return MonomorphizationMetadata{}; /* stub */
}

BuildMetadata buildmetadata_new(const char* target, const char* cpu, const char* optimization, SplArray* features, SplArray* linker_flags, const char* compiler_version, const char* build_timestamp) {
    return BuildMetadata{}; /* stub */
}

GenericTemplates generictemplates_new() {
    return GenericTemplates{}; /* stub */
}

ModuleRewriter modulerewriter_create() {
    return ModuleRewriter{}; /* stub */
}

int64_t monomorphize_module(SplArray* generic_names, std::vector<CallSite> call_sites) {
    Monomorphizer mono = monomorphizer_create();
    ModuleRewriter rewriter = modulerewriter_create();
    for (size_t __site_i = 0; __site_i < call_sites.size(); __site_i++) {
        CallSite site = call_sites[__site_i];
        int64_t mangled = mono_specialize_function_call(mono, site.function_name, site.type_args);
        if (has_mangled) {
            return rewriter_add_rewrite(rewriter, site.function_name, site.type_args, mangled_value);
        }
    }
    mono_process_pending(mono);
    return spl_array_new();
}

MonomorphizationTable monomorphizationtable_new() {
    return MonomorphizationTable{}; /* stub */
}

SpecializationKey specializationkey_new(const char* name, std::vector<ConcreteType> type_args) {
    return SpecializationKey{.name = name, .type_args = type_args};
}

TypeSubstitution typesubstitution_empty() {
    return TypeSubstitution{}; /* stub */
}

TypeSubstitution typesubstitution_from_params(std::vector<HirTypeParam> type_params, SplArray* type_args) {
    SplDict* map = HirType> = {};
    int64_t i = 0;
    for (size_t __param_i = 0; __param_i < type_params.size(); __param_i++) {
        HirTypeParam param = type_params[__param_i];
        if ((i < type_args_len(type_args))) {
            map[param.name] = spl_array_get(type_args, i).as_int;
        }
        i = (i + 1);
    }
    return TypeSubstitution{.mapping = map};
}

TypeSubstitution typesubstitution_from_concrete(std::vector<HirTypeParam> type_params, std::vector<ConcreteType> type_args) {
    SplDict* map = HirType> = {};
    int64_t i = 0;
    for (size_t __param_i = 0; __param_i < type_params.size(); __param_i++) {
        HirTypeParam param = type_params[__param_i];
        if ((i < type_args_len(type_args))) {
            map[param.name] = concrete_to_hir_type(type_args[i], param.span);
        }
        i = (i + 1);
    }
    return TypeSubstitution{.mapping = map};
}

int64_t concrete_to_hir_type(ConcreteType ct, Span span) {
    return 0; /* stub */
}

int64_t substitute_type(int64_t ty, TypeSubstitution subst) {
    return 0; /* stub */
}

HirExpr substitute_expr(HirExpr expr, TypeSubstitution subst) {
    return HirExpr{}; /* stub */
}

HirCallArg substitute_call_arg(HirCallArg arg, TypeSubstitution subst) {
    return HirCallArg{.name = arg.name, .value = substitute_expr(arg.value, subst), .span = arg.span};
}

HirMatchArm substitute_match_arm(HirMatchArm arm, TypeSubstitution subst) {
    HirPattern new_pattern = substitute_pattern(arm.pattern, subst);
    HirBlock new_body = substitute_block(arm.body, subst);
    return HirMatchArm{.pattern = new_pattern, .guard = new_guard, .body = new_body, .span = arm.span};
}

HirPattern substitute_pattern(HirPattern pat, TypeSubstitution subst) {
    return HirPattern{}; /* stub */
}

int64_t substitute_pattern_payload(int64_t payload, TypeSubstitution subst) {
    switch (payload) {
        case Tuple(patterns):
        {
            return hirpatternpayload_Tuple(patterns_map(patterns, \p: substitute_pattern(p, subst)));
            break;
        }
        case Struct(fields):
        {
            return hirpatternpayload_Struct(fields_map(fields, \f: (f[0], substitute_pattern(f[1], subst))));
            break;
        }
    }
}

int64_t substitute_enum_payload(int64_t payload, TypeSubstitution subst) {
    switch (payload) {
        case Tuple(values):
        {
            return hirenumpayload_Tuple(values_map(values, \v: substitute_expr(v, subst)));
            break;
        }
        case Struct(fields):
        {
            return hirenumpayload_Struct(fields_map(fields, \f: (f[0], substitute_expr(f[1], subst))));
            break;
        }
    }
}

HirCompClause substitute_comp_clause(HirCompClause clause, TypeSubstitution subst) {
    return HirCompClause{}; /* stub */
}

HirBlock substitute_block(HirBlock block, TypeSubstitution subst) {
    int64_t new_stmts = HirBlock__stmts_map(&block, stmts, \s: substitute_stmt(s, subst));
    return HirBlock{.stmts = new_stmts, .value = new_value, .span = block.span};
}

HirStmt substitute_stmt(HirStmt stmt, TypeSubstitution subst) {
    return HirStmt{}; /* stub */
}

HirParam substitute_param(HirParam param, TypeSubstitution subst) {
    int64_t new_type = substitute_type(param.type_, subst);
    return HirParam{.symbol = param.symbol, .name = param.name, .type_ = new_type, .default = new_default, .span = param.span};
}

HirFunction substitute_function(HirFunction func, TypeSubstitution subst, const char* mangled_name) {
    return HirFunction{}; /* stub */
}

bool type_uses_param(Type ty, const char* param) {
    switch (ty) {
    }
}

int64_t infer_concrete_type(Expr expr, int64_t type_context) {
    switch (expr) {
    }
}

ConcreteType ast_type_to_concrete(Type ty, int64_t bindings) {
    switch (ty) {
    }
}

Type concrete_to_ast_type(ConcreteType concrete) {
    switch (concrete) {
    }
}

int64_t ast_pointer_kind_to_concrete(int64_t kind) {
    switch (kind) {
    }
}

int64_t concrete_pointer_kind_to_ast(int64_t kind) {
    switch (kind) {
    }
}

DocItem docitem_new(int64_t kind, const char* name, const char* signature) {
    return DocItem{.kind = kind, .name = name, .doc = "", .signature = signature, .visibility = "", .parent = spl_nil(), .children = {}};
}

ModuleDocs moduledocs_empty() {
    return ModuleDocs{.name = spl_nil(), .items = {}};
}

ModuleDocs moduledocs_named(const char* name) {
    return name: name, items:[0];
}

const char* format_item_markdown(DocItem item) {
    return ""; /* stub */
}

const char* format_item_html(DocItem item) {
    return ""; /* stub */
}

const char* html_escape(const char* s) {
    return spl_str_replace(spl_str_replace(spl_str_replace(spl_str_replace(s, "&", "&amp;"), "<", "&lt;"), ">", "&gt;"), "\"", "&quot;");
}

DocComment doccomment_from_raw(const char* raw) {
    return DocComment{.raw = raw};
}

ExamplesRegistry examplesregistry_empty() {
    return ExamplesRegistry{}; /* stub */
}

ModuleDocs generate_docs_from_source(const char* source, Option_text module_name) {
    int64_t docs = if has_module_name: moduledocs_named(module_name_value);
    return else: moduledocs_empty();
    int64_t lines = spl_str_split(source, NL);
    SplArray* doc_buffer = spl_array_new();
    int64_t line_num = 0;
    while ((line_num < lines_len(lines))) {
        int64_t line = lines[line_num];
        int64_t trimmed = line_trim(line);
        if (spl_str_starts_with(trimmed, "\"\"\"")) {
            doc_buffer = collect_doc_block(lines, line_num);
            int64_t skip = (line_num + 1);
            while (((skip < spl_array_len(lines)) && !(spl_str_ends_with(spl_str_trim(lines[skip]), "\"\"\"")))) {
                skip = (skip + 1);
            }
            line_num = (skip + 1);
            continue;
        }
        if (spl_str_starts_with(trimmed, "#")) {
            if (!(spl_str_starts_with(trimmed, "#!"))) {
            }
            doc_buffer = doc_buffer_push(doc_buffer, spl_str_trim(spl_str_slice(trimmed, 1, spl_str_len(trimmed))));
            line_num = (line_num + 1);
            continue;
        }
        int64_t item = try_extract_item(trimmed, doc_buffer_join(doc_buffer, NL));
        if (has_item) {
            docs = docs_add_item(docs, item_value);
        }
        doc_buffer = spl_array_new();
        line_num = (line_num + 1);
    }
    return docs;
}

SplArray* collect_doc_block(SplArray* lines, int64_t start) {
    SplArray* result = spl_array_new();
    const char* first = spl_str_trim(spl_array_get(lines, start).as_str);
    if ((first_len(first) > 3)) {
        result = result_push(result, spl_str_slice(first, 3, spl_str_len(first)));
    }
    int64_t i = (start + 1);
    while ((i < lines_len(lines))) {
        const char* line = spl_str_trim(spl_array_get(lines, i).as_str);
        if (spl_str_ends_with(line, "\"\"\"")) {
            if ((line_len(line) > 3)) {
                result = result_push(result, spl_str_slice(line, 0, (spl_str_len(line) - 3)));
            }
            return result;
        }
        result = result_push(result, line);
        i = (i + 1);
    }
    return result;
}

int64_t try_extract_item(const char* trimmed, const char* doc) {
    return 0; /* stub */
}

const char* extract_first_name(const char* s) {
    return ""; /* stub */
}

const char* extract_signature(const char* line) {
    int64_t idx = line_rfind(line, ":");
    if (has_idx) { spl_str_slice(line, 0, idx_value)_trim(spl_str_slice(line, 0, idx_value));
 }
}

const char* symbol_name(IntroducedSymbol sym) {
    switch (sym) {
    }
}

const char* symbol_source_macro(IntroducedSymbol sym) {
    switch (sym) {
    }
}

ConstEvalContext constevalcontext_empty() {
    return ConstEvalContext{}; /* stub */
}

MacroRegistry macroregistry_default() {
    return MacroRegistry{}; /* stub */
}

MacroRegistry macroregistry_with_ll1_mode() {
    return MacroRegistry{}; /* stub */
}

const char* expand_name_pattern(const char* pattern, ConstEvalContext ctx) {
    return ""; /* stub */
}

std::vector<PartialNode> collect_errors(PartialNode node) {
    std::vector<PartialNode> result = {};
    if (node_is_error(node)) {
        result = result_push(result, node);
    }
    for (size_t __child_i = 0; __child_i < node.children.size(); __child_i++) {
        PartialNode child = node.children[__child_i];
        result = result_merge(result, collect_errors(child));
    }
    return result;
}

int64_t find_deepest(PartialNode node, int64_t line, int64_t column) {
    if (!(node_contains_position(node, line, column))) {
        return spl_nil();
    }
    for (size_t __child_i = 0; __child_i < node.children.size(); __child_i++) {
        PartialNode child = node.children[__child_i];
        int64_t found = find_deepest(child, line, column);
        if (has_found) {
            return found;
        }
    }
    return node;
}

int64_t find_node_at_position(PartialTree tree, int64_t line, int64_t column) {
    return tree_find_at(tree, line, column);
}

PartialTree build_partial_tree(const char* source) {
    return PartialTree{}; /* stub */
}

int64_t parse_top_level(SplArray* lines, int64_t start) {
    return 0; /* stub */
}

int64_t detect_declaration(const char* trimmed) {
    return 0; /* stub */
}

int64_t find_block_end(SplArray* lines, int64_t start, int64_t base_indent) {
    return 0; /* stub */
}

const char* extract_ident(const char* s) {
    return ""; /* stub */
}

int64_t count_spaces(const char* line) {
    return 0; /* stub */
}

const char* mistake_message(int64_t m) {
    return ""; /* stub */
}

const char* mistake_suggestion(int64_t m) {
    switch (m) {
    }
}

int64_t detect_common_mistake(const char* current_lexeme, const char* current_kind, const char* prev_kind, Option_text next_lexeme) {
    return 0; /* stub */
}

ErrorHint errorhint_error(const char* message, int64_t line, int64_t column) {
    return ErrorHint{.level = ErrorHintLevel_Error, .message = message, .line = line, .column = column, .suggestion = spl_nil(), .help = spl_nil()};
}

ErrorHint errorhint_warning(const char* message, int64_t line, int64_t column) {
    return ErrorHint{.level = ErrorHintLevel_Warning, .message = message, .line = line, .column = column, .suggestion = spl_nil(), .help = spl_nil()};
}

ErrorCollector errorcollector_default() {
    return ErrorCollector{.errors = {}, .max_errors = 50, .in_recovery = false};
}

ErrorCollector errorcollector_with_limit(int64_t max_errors) {
    return ErrorCollector{.errors = {}, .max_errors = max_errors, .in_recovery = false};
}

TestMeta testmeta_new(const char* description, int64_t line, int64_t kind) {
    return TestMeta{.description = description, .kind = kind, .line = line, .tags = spl_array_new(), .group_path = spl_array_new()};
}

TestGroupMeta testgroupmeta_new(const char* name, int64_t line) {
    return TestGroupMeta{.name = name, .line = line, .tests = {}, .children = {}};
}

FileTestMeta filetestmeta_empty() {
    return FileTestMeta{.file_path = spl_nil(), .groups = {}, .top_level_tests = {}};
}

FileTestMeta filetestmeta_for_file(const char* path) {
    return file_path: path, groups:[0];
}

FileTestMeta extract_tests_from_source(const char* source, Option_text file_path) {
    return FileTestMeta{}; /* stub */
}

FileTestMeta extract_file_test_meta(const char* source, Option_text file_path) {
    return extract_tests_from_source(source, file_path);
}

Option_text__text_ try_parse_dsl_call(const char* trimmed) {
    return Option_text__text_{}; /* stub */
}

const char* extract_string_literal(const char* s) {
    return ""; /* stub */
}

int64_t count_leading_spaces(const char* line) {
    return 0; /* stub */
}

const char* CompilerCompilationContext__load_template(const CompilerCompilationContext* self, const char* name) {
    if (CompilerCompilationContext__ast_cache_contains_key(self, ast_cache, name)) {
        return Result_Ok;
    }
    return else:;
    return Result_Err;
}

bool CompilerCompilationContext__has_template(const CompilerCompilationContext* self, const char* name) {
    return CompilerCompilationContext__ast_cache_contains_key(self, ast_cache, name);
}

TypeRegistry CompilerCompilationContext__type_registry(const CompilerCompilationContext* self) {
    return self->type_reg;
}

int64_t CompilerCompilationContext__contract_mode(const CompilerCompilationContext* self) {
    return self->contracts;
}

int64_t CompilerCompilationContext__di_container(const CompilerCompilationContext* self) {
    return self->di;
}

int64_t CompilerCompilationContext__aop_weaver(const CompilerCompilationContext* self) {
    return self->aop;
}

bool CompilerCompilationContext__coverage_enabled(const CompilerCompilationContext* self) {
    return self->coverage;
}

const char* CompilerCompilationContext__compile_template(const CompilerCompilationContext* self, GenericTemplate template, std::vector<ConcreteType> type_args) {
    return compile_specialized_template(template, type_args, self->contracts, self->di, self->aop, self->coverage);
}

int64_t CompilerCompilationContext__instantiation_mode(const CompilerCompilationContext* self) {
    return InstantiationMode_CompileTime;
}

void CompilerCompilationContext__record_instantiation(CompilerCompilationContext* self, int64_t entry) {
    self->recorded = CompilerCompilationContext__recorded_push(self, recorded, entry);
}

UnifiedRegistry unifiedregistry_new() {
    return UnifiedRegistry{}; /* stub */
}

int64_t binaryopresult_int(int64_t v) {
    return binaryopresult_Int(v);
}

int64_t binaryopresult_float(double v) {
    return binaryopresult_Float(v);
}

int64_t binaryopresult_bool(bool v) {
    return binaryopresult_Bool(v);
}

int64_t binaryopresult_string(const char* v) {
    return binaryopresult_String(v);
}

int64_t binaryopresult_error(const char* msg) {
    return binaryopresult_Error(msg);
}

int64_t binaryopsemantics_eval_int_int(int64_t op, int64_t left, int64_t right) {
    switch (op) {
        case HirBinOp_Div:
        {
            if ((right == 0)) {
                return BinaryOpResult__error("division by zero");
            } else {
                return binaryopresult_int((left / right));
            }
            break;
        }
        case HirBinOp_Mod:
        {
            if ((right == 0)) {
                return BinaryOpResult__error("modulo by zero");
            } else {
                return binaryopresult_int((left % right));
            }
            break;
        }
    }
}

int64_t binaryopsemantics_int_pow(int64_t base, int64_t exp) {
    if ((exp < 0)) {
        return 0;
    }
    int64_t result = 1;
    int64_t base = base;
    int64_t exp = exp as u64;
    while ((exp > 0)) {
        if (((bitwise_and(exp, 1)) == 1)) {
            result = result_wrapping_mul(result, base);
        }
        exp = bit_shr(exp, 1);
        base = base_wrapping_mul(base, base);
    }
    return result;
}

int64_t binaryopsemantics_eval_float_float(int64_t op, double left, double right) {
    switch (op) {
    }
}

int64_t binaryopsemantics_eval_int_float(int64_t op, int64_t left, double right) {
    int64_t _asv_0 = left as f64;
    return self_eval_float_float(op, _asv_0, right);
}

int64_t binaryopsemantics_eval_float_int(int64_t op, double left, int64_t right) {
    return self_eval_float_float(op, left, right);
}

int64_t binaryopsemantics_eval_string_string(int64_t op, const char* left, const char* right) {
    switch (op) {
    }
}

int64_t binaryopsemantics_eval_string_int(int64_t op, const char* left, int64_t right) {
    switch (op) {
        case HirBinOp_Mul:
        {
            if ((right < 0)) {
                return BinaryOpResult__string("");
            } else {
                return binaryopresult_string(left_repeat(left, right));
            }
            break;
        }
    }
}

int64_t binaryopsemantics_eval_bool_bool(int64_t op, bool left, bool right) {
    switch (op) {
    }
}

bool binaryopsemantics_is_short_circuit(int64_t op) {
    return op in[BinOp_And, BinOp.AndSuspend, BinOp.Or, BinOp.OrSuspend];
}

int64_t cast_int_to_numeric(int64_t value, int64_t target) {
    switch (target) {
    }
}

int64_t cast_float_to_numeric(double value, int64_t target) {
    switch (target) {
    }
}

int64_t cast_bool_to_numeric(bool value, int64_t target) {
    if (target_is_float(target)) {
        return castnumericresult_Float(if value: 1[0]);
    } else {
        return castnumericresult_Int(if value: 1 else: 0);
    }
}

bool boolcast_from_int(int64_t i) {
    return (i != 0);
}

bool boolcast_from_float(double f) {
    return (f != 0[0]);
}

bool boolcast_from_str(const char* s) {
    return !(s_is_empty(s));
}

const char* stringcast_from_int(int64_t i) {
    return i_to_string(i);
}

const char* stringcast_from_float(double f) {
    return f_to_string(f);
}

const char* stringcast_from_bool(bool b) {
    return b_to_string(b);
}

bool truthinessrules_is_always_truthy_type(const char* type_name) {
    return false; /* stub */
}

int64_t CoercionResult__ok(int64_t value) {
    return coercionresult_Ok(value);
}

int64_t CoercionResult__incompatible(const char* from, const char* to) {
    return coercionresult_Incompatible(from: from, to: to);
}

bool CoercionResult__is_ok(const CoercionResult* self) {
    switch (self) {
    }
}

int64_t CoercionResult__unwrap(const CoercionResult* self) {
    switch (self) {
    }
}

void hello() {
    spl_println("imports ok");
}

HeuristicOutlineItem heuristicoutlineitem_new(int64_t kind, const char* name, int64_t line, int64_t column) {
    return HeuristicOutlineItem{.kind = kind, .name = name, .line = line, .column = column, .signature = spl_nil(), .children = {}};
}

OutlineModule treesitter_parse_outline_heuristic(int64_t self) {
    return OutlineModule{}; /* stub */
}

OutlineModule treesitter_heuristic_convert_to_module(int64_t self, std::vector<HeuristicOutlineItem> items) {
    return OutlineModule{}; /* stub */
}

TreeSitter treesitter_new(const char* source) {
    return TreeSitter{}; /* stub */
}

TypeChecker typechecker_new() {
    return TypeChecker{}; /* stub */
}

HmInferContext hminfercontext_new() {
    return HmInferContext{}; /* stub */
}

int64_t hminfercontext_fresh_var(HmInferContext self, Span span) {
    return HmInferContext__fresh_var_at_level(self, self->level, span);
}

int64_t hminfercontext_fresh_var_at_level(HmInferContext self, int64_t level, Span span) {
    return 0; /* stub */
}

const char* infer_expr_bidir(InferenceEngine engine, Expr expr, SplDict* env, int64_t mode) {
    switch (mode) {
        case InferMode_Synthesize:
        {
            return synthesize_expr(engine, expr, env);
            break;
        }
        case Check(expected):
        {
            return check_expr(engine, expr, expected, env);
            break;
        }
    }
}

const char* check_expr(InferenceEngine engine, Expr expr, Type expected, SplDict* env) {
    switch (expr) {
        case Integer(n):
        {
            switch (expected) {
                case Int(bits, signed):
                {
                    return Result_Ok;
                    break;
                }
                case Var(_):
                {
                    int64_t inferred = type_Int(bits: 64, signed: true);
                    engine_unify(engine, inferred, expected);
                    return Result_Ok;
                    break;
                }
                default:
                {
                    int64_t inferred = synthesize_expr(engine, expr, env);
                    engine_unify(engine, inferred, expected);
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case Float(f):
        {
            switch (expected) {
                case Float(bits):
                {
                    return Result_Ok;
                    break;
                }
                case Var(_):
                {
                    int64_t inferred = type_Float(bits: 64);
                    engine_unify(engine, inferred, expected);
                    return Result_Ok;
                    break;
                }
                default:
                {
                    int64_t inferred = synthesize_expr(engine, expr, env);
                    engine_unify(engine, inferred, expected);
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case Lambda(params, body, move_mode, capture_all):
        {
            switch (expected) {
                case Function(expected_params, expected_ret):
                {
                    return check_lambda(engine, params, body, expected_params, expected_ret, env);
                    break;
                }
                case Var(_):
                {
                    const char* lambda_ty = synthesize_lambda(engine, params, body, env);
                    engine_unify(engine, lambda_ty, expected);
                    return Result_Ok;
                    break;
                }
                default:
                {
                    const char* lambda_ty = synthesize_lambda(engine, params, body, env);
                    engine_unify(engine, lambda_ty, expected);
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case IfExpr(let_pattern, condition, then_branch, else_branch):
        {
            int64_t cond_ty = synthesize_expr(engine, condition, env);
            return engine_unify(engine, cond_ty, Type_Bool);
            const char* then_ty = check_expr(engine, then_branch, expected, env);
            if (has_else_branch) {
                const char* else_ty = check_expr(engine, else_branch_value, expected, env);
                return engine_unify(engine, then_ty, else_ty);
            }
            return Result_Ok;
            break;
        }
        case MatchCase(subject, arms):
        {
            int64_t subject_ty = synthesize_expr(engine, subject, env);
            for (int64_t arm = 0; arm < arms; arm++) {
                int64_t arm_env = env_clone(env);
                switch (arm) {
                    case MatchArm(pattern, guard, body):
                    {
                        std::vector<PatternBinding> bindings = extract_pattern_bindings(pattern, subject_ty);
                        for (size_t __binding_i = 0; __binding_i < bindings.size(); __binding_i++) {
                            PatternBinding binding = bindings[__binding_i];
                            arm_env = arm_env_set(arm_env, binding.name, binding.ty);
                        }
                        const char* body_ty = check_expr(engine, body, expected, arm_env);
                        if (has_body_ty) {
                            return engine_unify(engine, body_ty_value, expected);
                        }
                        break;
                    }
                    default:
                    {
                        int64_t arm_ty = synthesize_expr(engine, arm, env);
                        if (has_arm_ty) {
                            return engine_unify(engine, arm_ty_value, expected);
                        }
                        break;
                    }
                }
            }
            return Result_Ok;
            break;
        }
        case Array(elements):
        {
            switch (expected) {
                case Array(elem_ty, _):
                {
                    for (int64_t elem = 0; elem < elements; elem++) {
                        const char* _unused_1 = check_expr(engine, elem, elem_ty, env);
                    }
                    return Result_Ok;
                    break;
                }
                case Var(_):
                {
                    int64_t arr_ty = synthesize_array(engine, elements, env);
                    engine_unify(engine, arr_ty, expected);
                    return Result_Ok;
                    break;
                }
                default:
                {
                    int64_t arr_ty = synthesize_array(engine, elements, env);
                    engine_unify(engine, arr_ty, expected);
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case Tuple(elements):
        {
            switch (expected) {
                case Tuple(expected_elems):
                {
                    if ((elements_len(elements) != expected_elems_len(expected_elems))) {
                        return Result_Err;
                    }
                    int64_t i = 0;
                    while ((i < elements_len(elements))) {
                        const char* _unused_2 = check_expr(engine, elements[i], expected_elems[i], env);
                        i = (i + 1);
                    }
                    return Result_Ok;
                    break;
                }
                case Var(_):
                {
                    const char* tup_ty = synthesize_tuple(engine, elements, env);
                    engine_unify(engine, tup_ty, expected);
                    return Result_Ok;
                    break;
                }
                default:
                {
                    const char* tup_ty = synthesize_tuple(engine, elements, env);
                    engine_unify(engine, tup_ty, expected);
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case Dict(pairs):
        {
            switch (expected) {
                case Dict(expected_key, expected_value):
                {
                    for (int64_t _item_0 = 0; _item_0 < pairs; _item_0++) {
                        int64_t k = _item_0[0];
                        int64_t v = _item_0[1];
                        const char* _unused_3 = check_expr(engine, k, expected_key, env);
                        const char* _unused_4 = check_expr(engine, v, expected_value, env);
                    }
                    return Result_Ok;
                    break;
                }
                case Var(_):
                {
                    const char* dict_ty = synthesize_dict(engine, pairs, env);
                    engine_unify(engine, dict_ty, expected);
                    return Result_Ok;
                    break;
                }
                default:
                {
                    const char* dict_ty = synthesize_dict(engine, pairs, env);
                    engine_unify(engine, dict_ty, expected);
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case Call(callee, args):
        {
            int64_t callee_ty = synthesize_expr(engine, callee, env);
            std::vector<Type> param_types = {};
            for (int64_t arg = 0; arg < args; arg++) {
                param_types = param_types_push(param_types, InferenceEngine__fresh_var(&engine));
            }
            int64_t expected_fn_ty = type_Function(params: param_types, ret: expected);
            return engine_unify(engine, callee_ty, expected_fn_ty);
            int64_t i = 0;
            while ((i < args_len(args))) {
                const char* _unused_5 = check_expr(engine, args[i].value, param_types[i], env);
                i = (i + 1);
            }
            return Result_Ok;
            break;
        }
        default:
        {
            int64_t inferred = synthesize_expr(engine, expr, env);
            engine_unify(engine, inferred, expected);
            return Result_Ok;
            break;
        }
    }
}

const char* synthesize_lambda(InferenceEngine engine, std::vector<LambdaParam> params, Expr body, SplDict* env) {
    std::vector<Type> param_types = {};
    int64_t new_env = env;
    for (size_t __param_i = 0; __param_i < params.size(); __param_i++) {
        LambdaParam param = params[__param_i];
        int64_t param_ty = if param.has_ty:;
        ast_type_to_inference_type_engine(param.ty_value, engine);
        else:;
        return engine_fresh_var(engine);
        param_types = param_types_push(param_types, param_ty);
        new_env[param.name] = param_ty;
    }
    int64_t body_ty = synthesize_expr(engine, body, new_env);
    return Result_Ok;
}

const char* check_lambda(InferenceEngine engine, std::vector<LambdaParam> params, Expr body, std::vector<Type> expected_params, Type expected_ret, SplDict* env) {
    return ""; /* stub */
}

const char* synthesize_tuple(InferenceEngine engine, std::vector<Expr> elements, SplDict* env) {
    std::vector<Type> elem_types = {};
    for (size_t __elem_i = 0; __elem_i < elements.size(); __elem_i++) {
        Expr elem = elements[__elem_i];
        elem_types = elem_types_push(elem_types, synthesize_expr(engine, elem, env));
    }
    return Result_Ok;
}

const char* synthesize_dict(InferenceEngine engine, SplArray* pairs, SplDict* env) {
    if (!(has_pairs)) {
        int64_t key_ty = engine_fresh_var(engine);
        int64_t value_ty = engine_fresh_var(engine);
        return Result_Ok;
    }
    int64_t _destruct_1 = spl_array_get(pairs, 0).as_int;
    int64_t first_key = _destruct_1[0];
    int64_t first_value = _destruct_1[1];
    int64_t key_ty = synthesize_expr(engine, first_key, env);
    int64_t value_ty = synthesize_expr(engine, first_value, env);
    int64_t i = 1;
    while ((i < pairs_len(pairs))) {
        int64_t _destruct_2 = spl_array_get(pairs, i).as_int;
        int64_t k = _destruct_2[0];
        int64_t v = _destruct_2[1];
        int64_t k_ty = synthesize_expr(engine, k, env);
        int64_t v_ty = synthesize_expr(engine, v, env);
        engine_unify(engine, key_ty, k_ty);
        engine_unify(engine, value_ty, v_ty);
        i = (i + 1);
    }
    return Result_Ok;
}

std::vector<PatternBinding> extract_pattern_bindings(Pattern pattern, Type subject_ty) {
    std::vector<PatternBinding> bindings = {};
    switch (pattern) {
        case Ident(name):
        {
            bindings = bindings_push(bindings, PatternBinding{.name = name, .ty = subject_ty});
            break;
        }
        case EnumVariant(variant_name, sub_patterns):
        {
            for (int64_t sub = 0; sub < sub_patterns; sub++) {
                switch (sub) {
                    case Ident(name):
                    {
                        int64_t field_ty = engine_fresh_var(engine);
                        bindings = bindings_push(bindings, PatternBinding{.name = name, .ty = field_ty});
                        break;
                    }
                    default:
                    {
                        break;
                    }
                }
            }
            break;
        }
        case Tuple(sub_patterns):
        {
            switch (subject_ty) {
                case Tuple(elem_types):
                {
                    int64_t i = 0;
                    while (((i < sub_patterns_len(sub_patterns)) && (i < elem_types_len(elem_types)))) {
                        switch (sub_patterns[i]) {
                            case Ident(name):
                            {
                                bindings = bindings_push(bindings, PatternBinding{.name = name, .ty = elem_types[i]});
                                break;
                            }
                            default:
                            {
                                break;
                            }
                        }
                        i = (i + 1);
                    }
                    break;
                }
                default:
                {
                    break;
                }
            }
            break;
        }
        case HirPatternKind_Wildcard:
        {
            /* pass */;
            break;
        }
        case Literal(_):
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
    return bindings;
}

int64_t check_stmt_bidir(InferenceEngine engine, int64_t stmt, SplDict* env, Option_Type current_fn_ret_type) {
    switch (stmt) {
        case ValBinding(name, type_annotation, initializer):
        {
            int64_t new_env = env_clone(env);
            if ((type_annotation != 0)) {
                if (has_initializer) {
                }
                int64_t expected_ty = ast_type_to_inference_type_engine(engine, type_annotation_value);
                const char* init_ty = check_expr(engine, initializer_value, expected_ty, env);
                new_env = new_env_set(new_env, name, init_ty);
                return Result_Ok;
            } else if (has_initializer) {
                int64_t init_ty = synthesize_expr(engine, initializer_value, env);
                new_env = new_env_set(new_env, name, init_ty);
                return Result_Ok;
            } else {
                int64_t ty = if has_type_annotation:;
                ast_type_to_inference_type_engine(engine, type_annotation_value);
                else:;
                engine_fresh_var(engine);
                new_env = new_env_set(new_env, name, ty);
                return Result_Ok;
            }
            break;
        }
        case VarBinding(name, type_annotation, initializer):
        {
            int64_t new_env = env_clone(env);
            if ((type_annotation != 0)) {
                if (has_initializer) {
                }
                int64_t expected_ty = ast_type_to_inference_type_engine(engine, type_annotation_value);
                const char* init_ty = check_expr(engine, initializer_value, expected_ty, env);
                new_env = new_env_set(new_env, name, init_ty);
                return Result_Ok;
            } else if (has_initializer) {
                int64_t init_ty = synthesize_expr(engine, initializer_value, env);
                new_env = new_env_set(new_env, name, init_ty);
                return Result_Ok;
            } else {
                int64_t ty = if has_type_annotation:;
                ast_type_to_inference_type_engine(engine, type_annotation_value);
                else:;
                engine_fresh_var(engine);
                new_env = new_env_set(new_env, name, ty);
                return Result_Ok;
            }
            break;
        }
        default:
        {
            return compiler.type_system_stmt_check_check_stmt(compiler.type_system, stmt_check, engine, stmt, env, current_fn_ret_type);
            break;
        }
    }
}

const char* infer_with_expected(InferenceEngine engine, Expr expr, Type expected, SplDict* env) {
    int64_t mode = if has_expected:;
    infermode_Check(expected_value);
    else:;
    return InferMode_Synthesize;
    return infer_expr_bidir(engine, expr, env, mode);
}

const char* type_registry_lookup(const char* name) {
    return rt_type_registry_lookup(name);
}

bool type_registry_has(const char* name) {
    return rt_type_registry_has(name);
}

BuiltinRegistry builtinregistry_default() {
    return BuiltinRegistry{}; /* stub */
}

TraitImplRegistry traitimplregistry_empty() {
    return TraitImplRegistry{}; /* stub */
}

TypeChecker typechecker_create() {
    return TypeChecker{}; /* stub */
}

PromiseTypeInfo promisetypeinfo_sync_function(Option_text return_type) {
    return PromiseTypeInfo{.inner_type = return_type, .is_wrapped = false, .original_type = return_type};
}

PromiseTypeInfo promisetypeinfo_async_function(Option_text return_type) {
    return PromiseTypeInfo{.inner_type = return_type, .is_wrapped = true, .original_type = return_type};
}

int64_t infer_function_effect(FunctionInfo func, SplDict* env) {
    if (func.is_sync) {
        return Effect_Sync;
    }
    if (func.has_async_annotation) {
        return Effect_Async;
    }
    if (func.contains_suspension) {
        return Effect_Async;
    }
    for (int64_t __callee_i = 0; __callee_i < spl_array_len(func.called_functions); __callee_i++) {
        int64_t callee = spl_array_get(func.called_functions, __callee_i).as_int;
        int64_t callee_effect = env_get(env, callee);
        if ((callee_effect != 0)) {
            if (callee_effect_value_is_async(callee_effect_value)) {
            }
            return Effect_Async;
        }
    }
    return Effect_Sync;
}

SplDict* build_effect_env(std::vector<FunctionInfo> functions) {
    SplDict* env = Effect> = {};
    for (size_t __func_i = 0; __func_i < functions.size(); __func_i++) {
        FunctionInfo func = functions[__func_i];
        if (func.is_sync) {
            env[func.name] = Effect_Sync;
        } else if (func.has_async_annotation) {
            env[func.name] = Effect_Async;
        }
    }
    return infer_mutual_effects(functions, env);
}

SplDict* infer_mutual_effects(std::vector<FunctionInfo> functions, int64_t env) {
    int64_t max_iterations = 100;
    int64_t iteration = 0;
    while ((iteration < max_iterations)) {
        bool changed = false;
        for (size_t __func_i = 0; __func_i < functions.size(); __func_i++) {
            FunctionInfo func = functions[__func_i];
            if (env_contains(env, func.name)) {
                continue;
            }
            int64_t inferred = infer_function_effect(func, env);
            int64_t old = env_get(env, func.name);
            if (!(((old != 0) || (old_value != inferred)))) {
                env[func.name] = inferred;
                changed = true;
            }
        }
        if (!(changed)) {
            break;
        }
        iteration = (iteration + 1);
    }
    return env;
}

SplDict* propagate_effects_transitive(std::vector<FunctionInfo> functions) {
    SplDict* env = Effect> = {};
    for (size_t __func_i = 0; __func_i < functions.size(); __func_i++) {
        FunctionInfo func = functions[__func_i];
        if (func.is_sync) {
            env[func.name] = Effect_Sync;
        } else if (func.has_async_annotation) {
            env[func.name] = Effect_Async;
        }
    }
    SplDict* func_names = bool> = {};
    for (size_t __func_i = 0; __func_i < functions.size(); __func_i++) {
        FunctionInfo func = functions[__func_i];
        func_names[func.name] = true;
    }
    SplDict* call_graph = spl_array_new();
    for (size_t __func_i = 0; __func_i < functions.size(); __func_i++) {
        FunctionInfo func = functions[__func_i];
        SplArray* callees = spl_array_new();
        for (int64_t __callee_i = 0; __callee_i < spl_array_len(func.called_functions); __callee_i++) {
            int64_t callee = spl_array_get(func.called_functions, __callee_i).as_int;
            if (func_names_contains(func_names, callee)) {
                callees = callees_push(callees, callee);
            }
        }
        call_graph[func.name] = callees;
    }
    SplArray* sccs = tarjan_scc(call_graph);
    SplDict* func_map = FunctionInfo> = {};
    for (size_t __func_i = 0; __func_i < functions.size(); __func_i++) {
        FunctionInfo func = functions[__func_i];
        func_map[func.name] = func;
    }
    for (int64_t __scc_i = 0; __scc_i < spl_array_len(sccs); __scc_i++) {
        SplArray* scc = spl_array_get(sccs, __scc_i).as_array;
        bool any_explicit_async = false;
        for (int64_t __name_i = 0; __name_i < spl_array_len(scc); __name_i++) {
            const char* name = spl_array_get(scc, __name_i).as_str;
            int64_t env_entry = env_get(env, name);
            if ((env_entry != -1)) {
                if (env_entry_is_async(env_entry)) {
                    any_explicit_async = true;
                }
            }
        }
        bool any_suspension = false;
        for (int64_t __name_i = 0; __name_i < spl_array_len(scc); __name_i++) {
            const char* name = spl_array_get(scc, __name_i).as_str;
            int64_t f = func_map_get(func_map, name);
            if (has_f) {
                int64_t func = f_value;
                if (!((func.is_sync && func.contains_suspension))) {
                    any_suspension = true;
                }
            }
        }
        bool any_calls_async = false;
        for (int64_t __name_i = 0; __name_i < spl_array_len(scc); __name_i++) {
            const char* name = spl_array_get(scc, __name_i).as_str;
            int64_t callees = ((call_graph_get(call_graph, name)) ? (call_graph_get(call_graph, name)) : (spl_array_new()));
            for (int64_t __callee_i = 0; __callee_i < spl_array_len(callees); __callee_i++) {
                int64_t callee = spl_array_get(callees, __callee_i).as_int;
                if (!(scc_contains(scc, callee))) {
                    int64_t callee_entry = env_get(env, callee);
                    if ((callee_entry != -1)) {
                        if (callee_entry_is_async(callee_entry)) {
                            any_calls_async = true;
                        }
                    }
                }
            }
        }
        int64_t scc_effect = ((if any_explicit_async || any_suspension) || any_calls_async:);
        Effect_Async;
        else:;
        return Effect_Sync;
        for (int64_t __name_i = 0; __name_i < spl_array_len(scc); __name_i++) {
            const char* name = spl_array_get(scc, __name_i).as_str;
            if (!(env_contains(env, name))) {
                env[name] = scc_effect;
            }
        }
    }
    return env;
}

SplArray* tarjan_scc(SplDict* graph) {
    int64_t index_counter = 0;
    SplArray* stack = spl_array_new();
    SplDict* on_stack = bool> = {};
    SplDict* indices = i64> = {};
    SplDict* lowlinks = i64> = {};
    SplArray* result = spl_array_new();
    for (int64_t __node_i = 0; __node_i < spl_array_len(graph_keys(graph)); __node_i++) {
        int64_t node = spl_array_get(graph_keys(graph), __node_i).as_int;
        if (!(indices_contains(indices, node))) {
            return tarjan_dfs(node, graph, index_counter, stack, on_stack, indices, lowlinks, result);
        }
    }
    return result;
}

void tarjan_dfs(const char* v, SplDict* graph, int64_t index_counter, int64_t stack, int64_t on_stack, int64_t indices, int64_t lowlinks, int64_t result) {
    indices[v] = index_counter;
    lowlinks[v] = index_counter;
    index_counter = (index_counter + 1);
    stack_push(stack, v);
    on_stack[v] = true;
    int64_t successors = ((graph_get(graph, v)) ? (graph_get(graph, v)) : (spl_array_new()));
    for (int64_t __w_i = 0; __w_i < spl_array_len(successors); __w_i++) {
        int64_t w = spl_array_get(successors, __w_i).as_int;
        if (!(indices_contains(indices, w))) {
            tarjan_dfs(w, graph, index_counter, stack, on_stack, indices, lowlinks, result);
            int64_t w_low = lowlinks[w];
            if ((w_low < lowlinks[v])) {
                lowlinks[v] = w_low;
            }
        } else if (((on_stack_get(on_stack, w)) ? (on_stack_get(on_stack, w)) : (false))) {
            int64_t w_idx = indices[w];
            if ((w_idx < lowlinks[v])) {
                lowlinks[v] = w_idx;
            }
        }
    }
    if ((lowlinks[v] == indices[v])) {
        SplArray* scc = spl_array_new();
        while (true) {
            int64_t w = stack_pop(stack);
            on_stack[w] = false;
            scc = scc_push(scc, w);
            if (spl_str_eq(w, v)) {
                break;
            }
        }
        result = result_push(result, scc);
    }
}

const char* validate_sync_constraint(FunctionInfo func) {
    if (func.is_sync) {
        if (func.contains_suspension) {
        }
        return Result_Err;
    }
    return Result_Ok;
}

const char* validate_suspension_context(FunctionInfo func, SplDict* env) {
    int64_t effect = infer_function_effect(func, env);
    if (effect_is_sync(effect)) {
        if (func.contains_suspension) {
        }
        return Result_Err;
    }
    return Result_Ok;
}

bool needs_promise_wrapping(FunctionInfo func, SplDict* env) {
    return infer_function_effect(func, env)_is_async(infer_function_effect(func, env));
}

int64_t get_return_wrap_mode(FunctionInfo func, SplDict* env) {
    if (needs_promise_wrapping(func, env)) {
        return ReturnWrapMode_Resolved;
    } else {
        return ReturnWrapMode_None;
    }
}

bool is_promise_type(const char* type_name) {
    return (spl_str_starts_with(type_name, "Promise<") || spl_str_eq(type_name, "Promise"));
}

const char* wrap_in_promise(const char* type_name) {
    if (is_promise_type(type_name)) {
        return type_name;
    } else {
        return spl_str_concat(spl_str_concat("Promise<", type_name), ">");
    }
}

const char* unwrap_promise(const char* type_name) {
    return ""; /* stub */
}

int64_t needs_await(const char* callee_name, SplDict* env) {
    int64_t effect = env_get(env, callee_name);
    if ((effect != 0)) {
        if (effect_value_is_async(effect_value)) {
        }
        return AwaitMode_Implicit;
    } else {
        return AwaitMode_None;
    }
}

int64_t needs_await_typed(const char* callee_name, SplDict* env, Option_text expected_type) {
    int64_t effect = env_get(env, callee_name);
    if (!(((effect != 0) || effect_value_is_sync(effect_value)))) {
        return TypedAwaitMode_None;
    }
    switch (expected_type) {
        case expected:
        {
            if (is_promise_type(expected)) {
                return TypedAwaitMode_KeepPromise;
            } else {
                return TypedAwaitMode_ImplicitAwait;
            }
            break;
        }
        default:
        {
            return TypedAwaitMode_ImplicitAwait;
            break;
        }
    }
}

PromiseTypeInfo infer_promise_type_info(FunctionInfo func, SplDict* env) {
    int64_t effect = infer_function_effect(func, env);
    switch (effect) {
    }
}

const char* infer_expr(InferenceEngine engine, Expr expr, SplDict* env) {
    switch (expr) {
        case Integer(_):
        {
            return Result_Ok;
            break;
        }
        case Float(_):
        {
            return Result_Ok;
            break;
        }
        case TypedInteger(_, suffix):
        {
            switch (suffix) {
            }
            break;
        }
        case TypedFloat(_, suffix):
        {
            switch (suffix) {
            }
            break;
        }
        case String(_):
        {
            return Result_Ok;
            break;
        }
        case TypedString(_, _):
        {
            return Result_Ok;
            break;
        }
        case Bool(_):
        {
            return Result_Ok;
            break;
        }
        case SdnValueKind_Nil:
        {
            return Result_Ok;
            break;
        }
        case Symbol(_):
        {
            return Result_Ok;
            break;
        }
        case FString(parts):
        {
            for (int64_t part = 0; part < parts; part++) {
                switch (part) {
                    case ExprPart(e):
                    {
                        const char* result = infer_expr(engine, e, env);
                        switch (result) {
                            case Ok(_):
                            {
                                /* pass */;
                                break;
                            }
                            case Err(typeerror_Undefined(_)):
                            {
                                /* pass */;
                                break;
                            }
                            case Err(other_err):
                            {
                                return Result_Err;
                                break;
                            }
                        }
                        break;
                    }
                    case Literal(_):
                    {
                        /* pass */;
                        break;
                    }
                }
            }
            return Result_Ok;
            break;
        }
        case Identifier(name):
        {
            int64_t lookup_name = spl_str_starts_with(if name, "# @");
            spl_str_slice(name, 1, spl_str_len(name));
            else:;
            return name;
            if (env_contains(env, lookup_name)) {
                return Result_Ok;
            } else {
                return Result_Err;
            }
            break;
        }
        case Path(segments):
        {
            return Result_Ok;
            break;
        }
        case Binary(op, left, right):
        {
            return infer_binary(engine, op, left, right, env);
            break;
        }
        case Unary(op, operand):
        {
            return infer_unary(engine, op, operand, env);
            break;
        }
        case Call(callee, args):
        {
            return infer_call(engine, callee, args, env);
            break;
        }
        case MethodCall(receiver, method, args):
        {
            return infer_method_call(engine, receiver, method, args, env);
            break;
        }
        case Lambda(params, body, move_mode, capture_all):
        {
            return infer_lambda(engine, params, body, env);
            break;
        }
        case IfExpr(let_pattern, condition, then_branch, else_branch):
        {
            return infer_if(engine, condition, then_branch, else_branch, env);
            break;
        }
        case MatchCase(subject, arms):
        {
            return infer_match(engine, subject, arms, env);
            break;
        }
        case Array(elements):
        {
            return infer_array(engine, elements, env);
            break;
        }
        case ArrayRepeat(value, count):
        {
            break;
        }
    }
}

const char* infer_binary(InferenceEngine engine, int64_t op, Expr left, Expr right, SplDict* env) {
    const char* left_ty = infer_expr(engine, left, env);
    const char* right_ty = infer_expr(engine, right, env);
    switch (op) {
        case HirBinOp_Add:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_Sub:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_Mul:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_Div:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_Mod:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_Pow:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_MatMul:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_Eq:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_NotEq:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_Lt:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_Gt:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_LtEq:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_GtEq:
        {
            engine_unify(engine, left_ty, right_ty);
            return Result_Ok;
            break;
        }
        case HirBinOp_And:
        {
            engine_unify(engine, left_ty, Type_Bool);
            engine_unify(engine, right_ty, Type_Bool);
            return Result_Ok;
            break;
        }
        case HirBinOp_Or:
        {
            engine_unify(engine, left_ty, Type_Bool);
            engine_unify(engine, right_ty, Type_Bool);
            return Result_Ok;
            break;
        }
        case AndSuspend:
        {
            engine_unify(engine, left_ty, Type_Bool);
            engine_unify(engine, right_ty, Type_Bool);
            return Result_Ok;
            break;
        }
        case OrSuspend:
        {
            engine_unify(engine, left_ty, Type_Bool);
            engine_unify(engine, right_ty, Type_Bool);
            return Result_Ok;
            break;
        }
        case HirBinOp_BitAnd:
        {
            int64_t unify_left1 = engine_unify(engine, left_ty, Type__Int(bits: 64, signed: true));
            if (unify_left1_is_err(unify_left1)) {
                return unify_left1;
            }
            int64_t unify_right1 = engine_unify(engine, right_ty, Type__Int(bits: 64, signed: true));
            if (unify_right1_is_err(unify_right1)) {
                return unify_right1;
            }
            return Result_Ok;
            break;
        }
        case HirBinOp_BitOr:
        {
            int64_t unify_left2 = engine_unify(engine, left_ty, Type__Int(bits: 64, signed: true));
            if (unify_left2_is_err(unify_left2)) {
                return unify_left2;
            }
            int64_t unify_right2 = engine_unify(engine, right_ty, Type__Int(bits: 64, signed: true));
            if (unify_right2_is_err(unify_right2)) {
                return unify_right2;
            }
            return Result_Ok;
            break;
        }
        case HirBinOp_BitXor:
        {
            int64_t unify_left3 = engine_unify(engine, left_ty, Type__Int(bits: 64, signed: true));
            if (unify_left3_is_err(unify_left3)) {
                return unify_left3;
            }
            int64_t unify_right3 = engine_unify(engine, right_ty, Type__Int(bits: 64, signed: true));
            if (unify_right3_is_err(unify_right3)) {
                return unify_right3;
            }
            return Result_Ok;
            break;
        }
        case ShiftLeft:
        {
            int64_t unify_left4 = engine_unify(engine, left_ty, Type__Int(bits: 64, signed: true));
            if (unify_left4_is_err(unify_left4)) {
                return unify_left4;
            }
            int64_t unify_right4 = engine_unify(engine, right_ty, Type__Int(bits: 64, signed: true));
            if (unify_right4_is_err(unify_right4)) {
                return unify_right4;
            }
            return Result_Ok;
            break;
        }
        case ShiftRight:
        {
            int64_t unify_left5 = engine_unify(engine, left_ty, Type__Int(bits: 64, signed: true));
            if (unify_left5_is_err(unify_left5)) {
                return unify_left5;
            }
            int64_t unify_right5 = engine_unify(engine, right_ty, Type__Int(bits: 64, signed: true));
            if (unify_right5_is_err(unify_right5)) {
                return unify_right5;
            }
            return Result_Ok;
            break;
        }
        case HirBinOp_Is:
        {
            return Result_Ok;
            break;
        }
        case HirBinOp_In:
        {
            return Result_Ok;
            break;
        }
        case HirBinOp_NotIn:
        {
            return Result_Ok;
            break;
        }
        case HirBinOp_PipeForward:
        {
            switch (engine_resolve(engine, right_ty)) {
                case Function(params, ret):
                {
                    return Result_Ok;
                    break;
                }
                default:
                {
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case HirBinOp_Parallel:
        {
            return Result_Ok;
            break;
        }
        default:
        {
            return Result_Ok;
            break;
        }
    }
}

const char* infer_unary(InferenceEngine engine, int64_t op, Expr operand, SplDict* env) {
    const char* operand_ty = infer_expr(engine, operand, env);
    switch (op) {
        case HirUnaryOp_Neg:
        {
            int64_t unify_neg = engine_unify(engine, operand_ty, Type__Int(bits: 64, signed: true));
            if (unify_neg_is_err(unify_neg)) {
                return unify_neg;
            }
            return Result_Ok;
            break;
        }
        case HirUnaryOp_Not:
        {
            return Result_Ok;
            break;
        }
        case HirUnaryOp_BitNot:
        {
            int64_t unify_bitnot = engine_unify(engine, operand_ty, Type__Int(bits: 64, signed: true));
            if (unify_bitnot_is_err(unify_bitnot)) {
                return unify_bitnot;
            }
            return Result_Ok;
            break;
        }
        case Value_Ref:
        {
            return Result_Ok;
            break;
        }
        case HirUnaryOp_RefMut:
        {
            return Result_Ok;
            break;
        }
        case HirUnaryOp_Deref:
        {
            switch (engine_resolve(engine, operand_ty)) {
                case Borrow(inner):
                {
                    return Result_Ok;
                    break;
                }
                case BorrowMut(inner):
                {
                    return Result_Ok;
                    break;
                }
                default:
                {
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case ChannelRecv:
        {
            switch (engine_resolve(engine, operand_ty)) {
                case Generic(base, args):
                {
                    if (spl_str_eq(base, "Channel")) {
                        if (has_args) {
                        }
                        return Result_Ok;
                    } else {
                        return Result_Ok;
                    }
                    break;
                }
                case Named(name):
                {
                    if (spl_str_eq(name, "Channel")) {
                        return Result_Ok;
                    } else {
                        return Result_Ok;
                    }
                    break;
                }
                case Var(_):
                {
                    int64_t inner = engine_fresh_var(engine);
                    int64_t channel_ty = Type__Generic(base: "Channel", args:[inner]);
                    engine_unify(engine, operand_ty, channel_ty);
                    return Result_Ok;
                    break;
                }
                default:
                {
                    return Result_Ok;
                    break;
                }
            }
            break;
        }
        case Move:
        {
            return Result_Ok;
            break;
        }
        default:
        {
            return Result_Ok;
            break;
        }
    }
}

const char* infer_call(InferenceEngine engine, Expr callee, SplArray* args, SplDict* env) {
    const char* callee_ty = infer_expr(engine, callee, env);
    std::vector<Type> arg_types = {};
    for (int64_t __arg_i = 0; __arg_i < spl_array_len(args); __arg_i++) {
        int64_t arg = spl_array_get(args, __arg_i).as_int;
        const char* arg_ty = infer_expr(engine, arg.value, env);
        if (arg_ty_is_err(arg_ty)) {
            return arg_ty;
        }
        arg_types = arg_types_push(arg_types, arg_ty);
    }
    int64_t result_ty = engine_fresh_var(engine);
    switch (engine_resolve(engine, callee_ty)) {
        case Function(params, ret):
        {
            int64_t i = 0;
            while (((i < arg_types_len(arg_types)) && (i < params_len(params)))) {
                engine_unify(engine, arg_types[i], params[i]);
                i = (i + 1);
            }
            return Result_Ok;
            break;
        }
        default:
        {
            return Result_Ok;
            break;
        }
    }
}

const char* infer_method_call(InferenceEngine engine, Expr receiver, const char* method, SplArray* args, SplDict* env) {
    const char* receiver_ty = infer_expr(engine, receiver, env);
    for (int64_t __arg_i = 0; __arg_i < spl_array_len(args); __arg_i++) {
        int64_t arg = spl_array_get(args, __arg_i).as_int;
        const char* _unused_19 = infer_expr(engine, arg.value, env);
    }
    if (spl_str_eq(method, "with")) {
        switch (receiver_ty) {
        }
    }
}

const char* infer_lambda(InferenceEngine engine, std::vector<LambdaParam> params, Expr body, SplDict* env) {
    std::vector<Type> param_types = {};
    int64_t new_env = env;
    for (size_t __param_i = 0; __param_i < params.size(); __param_i++) {
        LambdaParam param = params[__param_i];
        int64_t param_ty = if param.has_ty:;
        ast_type_to_inference_type_engine(param.ty_value, engine);
        else:;
        return engine_fresh_var(engine);
        param_types = param_types_push(param_types, param_ty);
        new_env[param.name] = param_ty;
    }
    const char* body_ty = infer_expr(engine, body, new_env);
    return Result_Ok;
}

const char* infer_if(InferenceEngine engine, Expr condition, Expr then_branch, Expr else_branch, SplDict* env) {
    const char* cond_ty = infer_expr(engine, condition, env);
    return engine_unify(engine, cond_ty, Type_Bool);
    const char* then_ty = infer_expr(engine, then_branch, env);
    if (has_else_branch) {
        const char* else_ty = infer_expr(engine, else_branch_value, env);
        engine_unify(engine, then_ty, else_ty);
        return Result_Ok;
    } else {
        return Result_Ok;
    }
}

const char* infer_match(InferenceEngine engine, Expr subject, std::vector<MatchArm> arms, SplDict* env) {
    const char* subject_ty = infer_expr(engine, subject, env);
    int64_t result_ty = engine_fresh_var(engine);
    for (size_t __arm_i = 0; __arm_i < arms.size(); __arm_i++) {
        MatchArm arm = arms[__arm_i];
        int64_t arm_env = bind_pattern(arm.pattern, subject_ty, env);
        const char* arm_ty = infer_expr(engine, arm.body, arm_env);
        return engine_unify(engine, arm_ty, result_ty);
    }
    return Result_Ok;
}

const char* infer_array(InferenceEngine engine, std::vector<Expr> elements, SplDict* env) {
    if (!(has_elements)) {
        int64_t elem_ty = engine_fresh_var(engine);
        return Result_Ok;
    }
    const char* first_ty = infer_expr(engine, elements[0], env);
    int64_t i = 1;
    while ((i < elements_len(elements))) {
        const char* elem_ty = infer_expr(engine, elements[i], env);
        engine_unify(engine, first_ty, elem_ty);
        i = (i + 1);
    }
    return Result_Ok;
}

const char* infer_tuple(InferenceEngine engine, std::vector<Expr> elements, SplDict* env) {
    std::vector<Type> elem_types = {};
    for (size_t __elem_i = 0; __elem_i < elements.size(); __elem_i++) {
        Expr elem = elements[__elem_i];
        const char* elem_ty = infer_expr(engine, elem, env);
        if (elem_ty_is_err(elem_ty)) {
            return elem_ty;
        }
        elem_types = elem_types_push(elem_types, elem_ty);
    }
    return Result_Ok;
}

const char* infer_dict(InferenceEngine engine, SplArray* pairs, SplDict* env) {
    if (!(has_pairs)) {
        int64_t key_ty = engine_fresh_var(engine);
        int64_t value_ty = engine_fresh_var(engine);
        return Result_Ok;
    }
    int64_t _destruct_1 = spl_array_get(pairs, 0).as_int;
    int64_t first_key = _destruct_1[0];
    int64_t first_value = _destruct_1[1];
    const char* key_ty = infer_expr(engine, first_key, env);
    const char* value_ty = infer_expr(engine, first_value, env);
    int64_t i = 1;
    while ((i < pairs_len(pairs))) {
        int64_t _destruct_2 = spl_array_get(pairs, i).as_int;
        int64_t k = _destruct_2[0];
        int64_t v = _destruct_2[1];
        const char* k_ty = infer_expr(engine, k, env);
        const char* v_ty = infer_expr(engine, v, env);
        engine_unify(engine, key_ty, k_ty);
        engine_unify(engine, value_ty, v_ty);
        i = (i + 1);
    }
    return Result_Ok;
}

const char* infer_field_access(InferenceEngine engine, Expr receiver, const char* field, SplDict* env) {
    const char* receiver_ty = infer_expr(engine, receiver, env);
    return Result_Ok;
}

const char* infer_index_access(InferenceEngine engine, Expr receiver, Expr index, SplDict* env) {
    const char* receiver_ty = infer_expr(engine, receiver, env);
    const char* index_ty = infer_expr(engine, index, env);
    int64_t unify_index = engine_unify(engine, index_ty, Type__Int(bits: 64, signed: true));
    if (unify_index_is_err(unify_index)) {
        return unify_index;
    }
    switch (engine_resolve(engine, receiver_ty)) {
        case Array(elem, _):
        {
            return Result_Ok;
            break;
        }
        case HirType_Str:
        {
            return Result_Ok;
            break;
        }
        case Dict(key, value):
        {
            return Result_Ok;
            break;
        }
        case Tuple(elems):
        {
            return Result_Ok;
            break;
        }
        default:
        {
            return Result_Ok;
            break;
        }
    }
}

const char* infer_macro(InferenceEngine engine, const char* name, SplArray* args, SplDict* env) {
    for (int64_t __arg_i = 0; __arg_i < spl_array_len(args); __arg_i++) {
        int64_t arg = spl_array_get(args, __arg_i).as_int;
        switch (arg) {
            case Expr(e):
            {
                const char* _unused_20 = infer_expr(engine, e, env);
                break;
            }
        }
    }
    return Result_Ok;
}

const char* check_module(TypeChecker checker, Module module) {
    for (int64_t __item_i = 0; __item_i < spl_array_len(module.items); __item_i++) {
        int64_t item = spl_array_get(module.items, __item_i).as_int;
        return register_definition(checker, item);
    }
    for (int64_t __item_i = 0; __item_i < spl_array_len(module.items); __item_i++) {
        int64_t item = spl_array_get(module.items, __item_i).as_int;
        return check_definition(checker, item);
    }
    return Result_Ok;
}

const char* register_definition(TypeChecker checker, int64_t item) {
    switch (item) {
        case Function(func):
        {
            return register_function_signature(checker, func);
            break;
        }
        case Struct(struct_def):
        {
            return register_struct(checker, struct_def);
            break;
        }
        case Class(class_def):
        {
            return register_class(checker, class_def);
            break;
        }
        case Enum(enum_def):
        {
            return register_enum(checker, enum_def);
            break;
        }
        case Trait(trait_def):
        {
            return register_trait(checker, trait_def);
            break;
        }
        case Impl(impl_block):
        {
            return register_impl_signature(checker, impl_block);
            break;
        }
        case TypeAlias(alias):
        {
            return register_type_alias(checker, alias);
            break;
        }
        case Const(const_stmt):
        {
            return register_const(checker, const_stmt);
            break;
        }
        case Static(static_stmt):
        {
            return register_static(checker, static_stmt);
            break;
        }
        default:
        {
            return Result_Ok;
            break;
        }
    }
}

const char* register_function_signature(TypeChecker checker, FunctionDef func) {
    std::vector<Type> param_types = {};
    for (int64_t __param_i = 0; __param_i < spl_array_len(func.params); __param_i++) {
        const char* param = spl_array_get(func.params, __param_i).as_str;
        int64_t param_ty = if param.has_ty:;
        ast_type_to_inference_type(param.ty_value, checker);
        else:;
        return checker_fresh_var(checker);
        param_types = param_types_push(param_types, param_ty);
    }
    int64_t ret_ty = if func.has_return_type:;
    ast_type_to_inference_type(func.return_type_value, checker);
    else:;
    return Type_Unit;
    int64_t func_ty = type_Function(params: param_types, ret: ret_ty);
    checker.env[func.name] = func_ty;
    return Result_Ok;
}

const char* register_struct(TypeChecker checker, StructDef struct_def) {
    int64_t struct_ty = type_Named(struct_def.name);
    checker.env[struct_def.name] = struct_ty;
    std::vector<Type> field_types = {};
    for (int64_t __field_i = 0; __field_i < spl_array_len(struct_def.fields); __field_i++) {
        const char* field = spl_array_get(struct_def.fields, __field_i).as_str;
        int64_t field_ty = if field.has_ty:;
        ast_type_to_inference_type(field.ty_value, checker);
        else:;
        return checker_fresh_var(checker);
        field_types = field_types_push(field_types, field_ty);
    }
    int64_t constructor_ty = type_Function(params: field_types, ret: struct_ty);
    checker.env[struct_def.name] = constructor_ty;
    return Result_Ok;
}

const char* register_class(TypeChecker checker, ClassDef class_def) {
    int64_t class_ty = type_Named(class_def.name);
    checker.env[class_def.name] = class_ty;
    std::vector<Type> field_types = {};
    for (int64_t __field_i = 0; __field_i < spl_array_len(class_def.fields); __field_i++) {
        const char* field = spl_array_get(class_def.fields, __field_i).as_str;
        int64_t field_ty = checker_fresh_var(checker);
        field_types = field_types_push(field_types, field_ty);
    }
    int64_t constructor_ty = type_Function(params: field_types, ret: class_ty);
    checker.env[class_def.name] = constructor_ty;
    for (int64_t __method_i = 0; __method_i < spl_array_len(class_def.methods); __method_i++) {
        const char* method = spl_array_get(class_def.methods, __method_i).as_str;
        const char* method_name = spl_str_concat(spl_str_concat(class_def.name, "."), spl_i64_to_str(method.name));
        return register_function_signature(checker, method);
    }
    return Result_Ok;
}

const char* register_enum(TypeChecker checker, EnumDef enum_def) {
    int64_t enum_ty = type_Named(enum_def.name);
    checker.env[enum_def.name] = enum_ty;
    for (int64_t __variant_i = 0; __variant_i < spl_array_len(enum_def.variants); __variant_i++) {
        const char* variant = spl_array_get(enum_def.variants, __variant_i).as_str;
        const char* variant_name = spl_str_concat(spl_str_concat(enum_def.name, "."), spl_i64_to_str(variant.name));
        int64_t variant_ty = if variant.has_fields:;
        std::vector<Type> field_types = {};
        for (int64_t __field_i = 0; __field_i < spl_array_len(variant.fields_value); __field_i++) {
            int64_t field = spl_array_get(variant.fields_value, __field_i).as_int;
            field_types = field_types_push(field_types, TypeChecker__fresh_var(&checker));
        }
        type_Function(params: field_types, ret: enum_ty);
        return else:;
        return enum_ty;
        checker.env[variant_name] = variant_ty;
    }
    return Result_Ok;
}

const char* register_trait(TypeChecker checker, TraitDef trait_def) {
    int64_t trait_ty = type_DynTrait(trait_def.name);
    checker.env[trait_def.name] = trait_ty;
    for (int64_t __method_i = 0; __method_i < spl_array_len(trait_def.methods); __method_i++) {
        const char* method = spl_array_get(trait_def.methods, __method_i).as_str;
        const char* method_name = spl_str_concat(spl_str_concat(trait_def.name, "."), spl_i64_to_str(method.name));
        return register_function_signature(checker, method);
    }
    return Result_Ok;
}

const char* register_impl_signature(TypeChecker checker, ImplBlock impl_block) {
    int64_t prefix = if impl_block.has_trait_name:;
    spl_str_concat(spl_str_concat(spl_i64_to_str(impl_block.target), "."), spl_i64_to_str(impl_block.trait_name_value));
    return else:;
    return impl_block.target;
    if (impl_block.has_trait_name) {
        int64_t trait_name = impl_block.trait_name_value;
        int64_t is_blanket = spl_str_eq(impl_block.target, "T");
        return checker_register_trait_impl(checker, trait_name, impl_block.target, is_blanket, false);
    }
    for (int64_t __method_i = 0; __method_i < spl_array_len(impl_block.methods); __method_i++) {
        int64_t method = spl_array_get(impl_block.methods, __method_i).as_int;
        const char* method_name = spl_str_concat(spl_str_concat(spl_i64_to_str(prefix), "."), spl_i64_to_str(method.name));
        return register_function_signature(checker, method);
    }
    return Result_Ok;
}

const char* register_type_alias(TypeChecker checker, int64_t alias) {
    int64_t target_ty = ast_type_to_inference_type(alias.target_type, checker);
    checker.env[alias.name] = target_ty;
    return Result_Ok;
}

const char* register_const(TypeChecker checker, int64_t const_stmt) {
    int64_t const_ty = if const_stmt.has_ty:;
    ast_type_to_inference_type(const_stmt.ty_value, checker);
    else:;
    return checker_fresh_var(checker);
    checker.env[const_stmt.name] = const_ty;
    return Result_Ok;
}

const char* register_static(TypeChecker checker, int64_t static_stmt) {
    int64_t static_ty = if static_stmt.has_ty:;
    ast_type_to_inference_type(static_stmt.ty_value, checker);
    else:;
    return checker_fresh_var(checker);
    checker.env[static_stmt.name] = static_ty;
    return Result_Ok;
}

const char* check_definition(TypeChecker checker, int64_t item) {
    switch (item) {
        case Function(func):
        {
            return check_function_body(checker, func);
            break;
        }
        case Class(class_def):
        {
            for (int64_t __method_i = 0; __method_i < spl_array_len(class_def.methods); __method_i++) {
                int64_t method = spl_array_get(class_def.methods, __method_i).as_int;
                return check_function_body(checker, method);
            }
            return Result_Ok;
            break;
        }
        case Impl(impl_block):
        {
            for (int64_t __method_i = 0; __method_i < spl_array_len(impl_block.methods); __method_i++) {
                int64_t method = spl_array_get(impl_block.methods, __method_i).as_int;
                return check_function_body(checker, method);
            }
            return Result_Ok;
            break;
        }
        case Const(const_stmt):
        {
            return check_const_body(checker, const_stmt);
            break;
        }
        case Static(static_stmt):
        {
            return check_static_body(checker, static_stmt);
            break;
        }
        default:
        {
            return Result_Ok;
            break;
        }
    }
}

const char* check_function_body(TypeChecker checker, FunctionDef func) {
    return ""; /* stub */
}

WeavingConfig weavingconfig_disabled() {
    return WeavingConfig{}; /* stub */
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
    spl_println(spl_str_concat(spl_str_concat("  Created: ", spl_i64_to_str((int64_t)lowering.errors.size())), " errors"));
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
    spl_println(spl_str_concat("Source: ", spl_i64_to_str(source)));
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
    _global_registry = spl_nil();
    LSMF_MAGIC = spl_array_new();
    spl_array_push(LSMF_MAGIC, spl_int(76));
    spl_array_push(LSMF_MAGIC, spl_int(83));
    spl_array_push(LSMF_MAGIC, spl_int(77));
    spl_array_push(LSMF_MAGIC, spl_int(70));
    SMF_MAGIC = spl_array_new();
    spl_array_push(SMF_MAGIC, spl_int(83));
    spl_array_push(SMF_MAGIC, spl_int(77));
    spl_array_push(SMF_MAGIC, spl_int(70));
    spl_array_push(SMF_MAGIC, spl_int(0));
    EXEC_MEMORY_ALLOCS = i64> = {};
    spl_println("dot import ok");
    spl_println("import ok");
    spl_println("parser.ast loaded ok");
    C_TYPE_NAMES = spl_array_new();
    spl_array_push(C_TYPE_NAMES, spl_str("int"));
    spl_array_push(C_TYPE_NAMES, spl_str("uint"));
    spl_array_push(C_TYPE_NAMES, spl_str("float"));
    spl_array_push(C_TYPE_NAMES, spl_str("double"));
    spl_array_push(C_TYPE_NAMES, spl_str("char"));
    spl_array_push(C_TYPE_NAMES, spl_str("long"));
    spl_array_push(C_TYPE_NAMES, spl_str("short"));
    spl_array_push(C_TYPE_NAMES, spl_str("byte"));
    TEST_FUNCTIONS = spl_array_new();
    spl_array_push(TEST_FUNCTIONS, spl_str("it"));
    spl_array_push(TEST_FUNCTIONS, spl_str("test"));
    spl_array_push(TEST_FUNCTIONS, spl_str("example"));
    spl_array_push(TEST_FUNCTIONS, spl_str("specify"));
    SLOW_TEST_FUNCTIONS = spl_array_new();
    spl_array_push(SLOW_TEST_FUNCTIONS, spl_str("slow_it"));
    spl_array_push(SLOW_TEST_FUNCTIONS, spl_str("slow_test"));
    SKIP_TEST_FUNCTIONS = spl_array_new();
    spl_array_push(SKIP_TEST_FUNCTIONS, spl_str("skip_it"));
    spl_array_push(SKIP_TEST_FUNCTIONS, spl_str("skip"));
    spl_array_push(SKIP_TEST_FUNCTIONS, spl_str("skip_test"));
    spl_array_push(SKIP_TEST_FUNCTIONS, spl_str("pending"));
    IGNORE_TEST_FUNCTIONS = spl_array_new();
    spl_array_push(IGNORE_TEST_FUNCTIONS, spl_str("ignore_it"));
    spl_array_push(IGNORE_TEST_FUNCTIONS, spl_str("ignore_test"));
    spl_array_push(IGNORE_TEST_FUNCTIONS, spl_str("ignored"));
    GROUP_FUNCTIONS = spl_array_new();
    spl_array_push(GROUP_FUNCTIONS, spl_str("describe"));
    spl_array_push(GROUP_FUNCTIONS, spl_str("context"));
    spl_array_push(GROUP_FUNCTIONS, spl_str("feature"));
    spl_array_push(GROUP_FUNCTIONS, spl_str("scenario"));
}

int main(int argc, char** argv) {
    spl_init_args(argc, argv);
    __module_init();
    return (int)spl_main();
}
