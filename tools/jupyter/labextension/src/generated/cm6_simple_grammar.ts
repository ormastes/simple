// GENERATED FILE — do not hand-edit.
//
// Produced by scripts/gen_cm6_grammar.mjs from the Tree-sitter highlight
// queries at src/compiler/10.frontend/parser/treesitter/queries/*.scm
// (same source the VSCode extension's TextMate grammar, syntaxes/simple.tmLanguage.json
// under src/app/vscode_extension/, is hand-derived from).
//
// Regenerate: node scripts/gen_cm6_grammar.mjs
// Verify not stale: node scripts/gen_cm6_grammar.mjs --check
// SHA gate: tools/jupyter/labextension/src/generated/grammar.sha256.json
//
// source: highlights.scm sha256=c4bfd8f3b70c19e2c94aa279e6d491fb33011410e86fb25c1cc3a468166262a5

import { tags } from "@lezer/highlight";
import { StreamLanguage, type StreamParser } from "@codemirror/language";

export interface Cm6TokenGroup {
  readonly captureTag: string;
  readonly tokenName: string;
  readonly tokens: readonly string[];
  readonly lezerTag: import("@lezer/highlight").Tag;
}

export const TOKENS_BOOLEAN: readonly string[] = ["false", "true"];

export const TOKENS_CONSTANT_BUILTIN: readonly string[] = ["None", "Some", "nil"];

export const TOKENS_KEYWORD_AOP: readonly string[] = ["allow", "aspect", "bind", "forbid", "mock", "on"];

export const TOKENS_KEYWORD_AOP_POINTCUT: readonly string[] = ["args", "call", "cflow", "execution", "target", "this", "within"];

export const TOKENS_KEYWORD_ASM: readonly string[] = ["asm", "volatile"];

export const TOKENS_KEYWORD_CAPABILITY: readonly string[] = ["dyn", "iso", "mut", "ref"];

export const TOKENS_KEYWORD_CONTRACT: readonly string[] = ["assert", "assume", "calc", "check", "ensures", "invariant", "out", "out_err", "requires"];

export const TOKENS_KEYWORD_CONTRACT_QUANTIFIER: readonly string[] = ["exists", "forall"];

export const TOKENS_KEYWORD_CONTROL: readonly string[] = ["pass", "pass_dn", "pass_do_nothing", "pass_todo", "todo"];

export const TOKENS_KEYWORD_CONTROL_ASYNC: readonly string[] = ["async", "await", "receive", "send", "spawn"];

export const TOKENS_KEYWORD_CONTROL_CONDITIONAL: readonly string[] = ["case", "elif", "else", "if", "match"];

export const TOKENS_KEYWORD_CONTROL_EXCEPTION: readonly string[] = ["catch", "finally", "panic", "throw", "try"];

export const TOKENS_KEYWORD_CONTROL_REPEAT: readonly string[] = ["break", "continue", "for", "loop", "while"];

export const TOKENS_KEYWORD_CONTROL_RETURN: readonly string[] = ["return", "yield"];

export const TOKENS_KEYWORD_CONTROL_SUSPENSION: readonly string[] = ["and~", "for~", "if~", "match~", "not~", "or~", "while~"];

export const TOKENS_KEYWORD_FUNCTION: readonly string[] = ["fn", "me"];

export const TOKENS_KEYWORD_GPU: readonly string[] = ["block", "bounds", "gpu", "grid", "kernel", "shared", "simd", "vec"];

export const TOKENS_KEYWORD_MODULE: readonly string[] = ["common", "export", "import", "mod", "priv", "pub", "use"];

export const TOKENS_KEYWORD_TEST: readonly string[] = ["and_then", "but", "context", "describe", "examples", "feature", "given", "it", "scenario", "slow_it", "then", "when"];

export const TOKENS_KEYWORD_TYPE: readonly string[] = ["actor", "class", "enum", "impl", "implements", "mixin", "struct", "trait", "type", "union", "unit"];

export const TOKENS_KEYWORD_TYPE_MODIFIER: readonly string[] = ["Self", "extends", "self", "where"];

export const TOKENS_KEYWORD_VARIABLE: readonly string[] = ["const", "let", "static", "val", "var"];

export const TOKENS_OPERATOR: readonly string[] = ["->", ".", ":", "::", "=>", "\\\\"];

export const TOKENS_OPERATOR_ARITHMETIC: readonly string[] = ["%", "*", "**", "+", "-", "/"];

export const TOKENS_OPERATOR_ASSIGNMENT: readonly string[] = ["%=", "&=", "*=", "+=", "-=", "/=", "<<=", "=", ">>=", "^=", "|="];

export const TOKENS_OPERATOR_BITWISE: readonly string[] = ["&", "<<", ">>", "|", "~"];

export const TOKENS_OPERATOR_BROADCAST: readonly string[] = [".%", ".*", ".+", ".-", "./", ".^"];

export const TOKENS_OPERATOR_COMPARISON: readonly string[] = ["!=", "<", "<=", "==", ">", ">="];

export const TOKENS_OPERATOR_LOGICAL: readonly string[] = ["and", "not", "or", "xor"];

export const TOKENS_OPERATOR_MATRIX: readonly string[] = ["@"];

export const TOKENS_OPERATOR_OPTIONAL: readonly string[] = [".?", "?", "?.", "??"];

export const TOKENS_OPERATOR_PIPELINE: readonly string[] = ["//", "|>", "~>"];

export const TOKENS_OPERATOR_RANGE: readonly string[] = ["..", "..="];

export const TOKENS_PUNCTUATION_BRACKET: readonly string[] = ["(", ")", "[", "]", "{", "}"];

export const TOKENS_PUNCTUATION_DELIMITER: readonly string[] = [",", ";"];

export const TOKENS_TYPE_BUILTIN: readonly string[] = ["bool", "char", "f32", "f64", "i128", "i16", "i32", "i64", "i8", "string", "text", "u128", "u16", "u32", "u64", "u8"];

/** Token groups in Tree-sitter @capture.tag order, first-match wins (mirrors
 * Tree-sitter query precedence: earlier `[...] @tag` blocks in
 * highlights.scm win ties, see mergeGroups() in the generator). */
export const CM6_TOKEN_GROUPS: readonly Cm6TokenGroup[] = [
  { captureTag: "boolean", tokenName: "boolean", tokens: TOKENS_BOOLEAN, lezerTag: tags.bool },
  { captureTag: "constant.builtin", tokenName: "constant_builtin", tokens: TOKENS_CONSTANT_BUILTIN, lezerTag: tags.atom },
  { captureTag: "keyword.aop", tokenName: "keyword_aop", tokens: TOKENS_KEYWORD_AOP, lezerTag: tags.keyword },
  { captureTag: "keyword.aop.pointcut", tokenName: "keyword_aop_pointcut", tokens: TOKENS_KEYWORD_AOP_POINTCUT, lezerTag: tags.keyword },
  { captureTag: "keyword.asm", tokenName: "keyword_asm", tokens: TOKENS_KEYWORD_ASM, lezerTag: tags.keyword },
  { captureTag: "keyword.capability", tokenName: "keyword_capability", tokens: TOKENS_KEYWORD_CAPABILITY, lezerTag: tags.modifier },
  { captureTag: "keyword.contract", tokenName: "keyword_contract", tokens: TOKENS_KEYWORD_CONTRACT, lezerTag: tags.keyword },
  { captureTag: "keyword.contract.quantifier", tokenName: "keyword_contract_quantifier", tokens: TOKENS_KEYWORD_CONTRACT_QUANTIFIER, lezerTag: tags.keyword },
  { captureTag: "keyword.control", tokenName: "keyword_control", tokens: TOKENS_KEYWORD_CONTROL, lezerTag: tags.controlKeyword },
  { captureTag: "keyword.control.async", tokenName: "keyword_control_async", tokens: TOKENS_KEYWORD_CONTROL_ASYNC, lezerTag: tags.controlKeyword },
  { captureTag: "keyword.control.conditional", tokenName: "keyword_control_conditional", tokens: TOKENS_KEYWORD_CONTROL_CONDITIONAL, lezerTag: tags.controlKeyword },
  { captureTag: "keyword.control.exception", tokenName: "keyword_control_exception", tokens: TOKENS_KEYWORD_CONTROL_EXCEPTION, lezerTag: tags.controlKeyword },
  { captureTag: "keyword.control.repeat", tokenName: "keyword_control_repeat", tokens: TOKENS_KEYWORD_CONTROL_REPEAT, lezerTag: tags.controlKeyword },
  { captureTag: "keyword.control.return", tokenName: "keyword_control_return", tokens: TOKENS_KEYWORD_CONTROL_RETURN, lezerTag: tags.controlKeyword },
  { captureTag: "keyword.control.suspension", tokenName: "keyword_control_suspension", tokens: TOKENS_KEYWORD_CONTROL_SUSPENSION, lezerTag: tags.controlKeyword },
  { captureTag: "keyword.function", tokenName: "keyword_function", tokens: TOKENS_KEYWORD_FUNCTION, lezerTag: tags.keyword },
  { captureTag: "keyword.gpu", tokenName: "keyword_gpu", tokens: TOKENS_KEYWORD_GPU, lezerTag: tags.keyword },
  { captureTag: "keyword.module", tokenName: "keyword_module", tokens: TOKENS_KEYWORD_MODULE, lezerTag: tags.keyword },
  { captureTag: "keyword.test", tokenName: "keyword_test", tokens: TOKENS_KEYWORD_TEST, lezerTag: tags.keyword },
  { captureTag: "keyword.type", tokenName: "keyword_type", tokens: TOKENS_KEYWORD_TYPE, lezerTag: tags.keyword },
  { captureTag: "keyword.type.modifier", tokenName: "keyword_type_modifier", tokens: TOKENS_KEYWORD_TYPE_MODIFIER, lezerTag: tags.modifier },
  { captureTag: "keyword.variable", tokenName: "keyword_variable", tokens: TOKENS_KEYWORD_VARIABLE, lezerTag: tags.keyword },
  { captureTag: "operator", tokenName: "operator", tokens: TOKENS_OPERATOR, lezerTag: tags.operator },
  { captureTag: "operator.arithmetic", tokenName: "operator_arithmetic", tokens: TOKENS_OPERATOR_ARITHMETIC, lezerTag: tags.arithmeticOperator },
  { captureTag: "operator.assignment", tokenName: "operator_assignment", tokens: TOKENS_OPERATOR_ASSIGNMENT, lezerTag: tags.definitionOperator },
  { captureTag: "operator.bitwise", tokenName: "operator_bitwise", tokens: TOKENS_OPERATOR_BITWISE, lezerTag: tags.bitwiseOperator },
  { captureTag: "operator.broadcast", tokenName: "operator_broadcast", tokens: TOKENS_OPERATOR_BROADCAST, lezerTag: tags.operator },
  { captureTag: "operator.comparison", tokenName: "operator_comparison", tokens: TOKENS_OPERATOR_COMPARISON, lezerTag: tags.compareOperator },
  { captureTag: "operator.logical", tokenName: "operator_logical", tokens: TOKENS_OPERATOR_LOGICAL, lezerTag: tags.logicOperator },
  { captureTag: "operator.matrix", tokenName: "operator_matrix", tokens: TOKENS_OPERATOR_MATRIX, lezerTag: tags.operator },
  { captureTag: "operator.optional", tokenName: "operator_optional", tokens: TOKENS_OPERATOR_OPTIONAL, lezerTag: tags.derefOperator },
  { captureTag: "operator.pipeline", tokenName: "operator_pipeline", tokens: TOKENS_OPERATOR_PIPELINE, lezerTag: tags.operator },
  { captureTag: "operator.range", tokenName: "operator_range", tokens: TOKENS_OPERATOR_RANGE, lezerTag: tags.punctuation },
  { captureTag: "punctuation.bracket", tokenName: "punctuation_bracket", tokens: TOKENS_PUNCTUATION_BRACKET, lezerTag: tags.name },
  { captureTag: "punctuation.delimiter", tokenName: "punctuation_delimiter", tokens: TOKENS_PUNCTUATION_DELIMITER, lezerTag: tags.name },
  { captureTag: "type.builtin", tokenName: "type_builtin", tokens: TOKENS_TYPE_BUILTIN, lezerTag: tags.name },
];

// token spelling -> flat tokenName (dot-free), built once for O(1)
// classification. The tokenName string (not a Tag object) is what
// token() returns; CM6's StreamParser.tokenTable resolves it to a Tag.
const TOKEN_TO_TOKEN_NAME = new Map<string, string>();
for (const group of CM6_TOKEN_GROUPS) {
  for (const tok of group.tokens) {
    if (!TOKEN_TO_TOKEN_NAME.has(tok)) TOKEN_TO_TOKEN_NAME.set(tok, group.tokenName);
  }
}

/** name (as returned from token()) -> @lezer/highlight Tag, passed to
 * StreamLanguage via StreamParser.tokenTable. Includes every @capture.tag
 * from highlights.scm (flattened to a dot-free tokenName) plus the handful
 * of lexical categories (comment, string, number, identifier) the tokenizer
 * recognizes structurally rather than by keyword spelling. */
export const TOKEN_TABLE: { [name: string]: import("@lezer/highlight").Tag } = {
  "boolean": tags.bool,
  "constant_builtin": tags.atom,
  "keyword_aop": tags.keyword,
  "keyword_aop_pointcut": tags.keyword,
  "keyword_asm": tags.keyword,
  "keyword_capability": tags.modifier,
  "keyword_contract": tags.keyword,
  "keyword_contract_quantifier": tags.keyword,
  "keyword_control": tags.controlKeyword,
  "keyword_control_async": tags.controlKeyword,
  "keyword_control_conditional": tags.controlKeyword,
  "keyword_control_exception": tags.controlKeyword,
  "keyword_control_repeat": tags.controlKeyword,
  "keyword_control_return": tags.controlKeyword,
  "keyword_control_suspension": tags.controlKeyword,
  "keyword_function": tags.keyword,
  "keyword_gpu": tags.keyword,
  "keyword_module": tags.keyword,
  "keyword_test": tags.keyword,
  "keyword_type": tags.keyword,
  "keyword_type_modifier": tags.modifier,
  "keyword_variable": tags.keyword,
  "operator": tags.operator,
  "operator_arithmetic": tags.arithmeticOperator,
  "operator_assignment": tags.definitionOperator,
  "operator_bitwise": tags.bitwiseOperator,
  "operator_broadcast": tags.operator,
  "operator_comparison": tags.compareOperator,
  "operator_logical": tags.logicOperator,
  "operator_matrix": tags.operator,
  "operator_optional": tags.derefOperator,
  "operator_pipeline": tags.operator,
  "operator_range": tags.punctuation,
  "punctuation_bracket": tags.name,
  "punctuation_delimiter": tags.name,
  "type_builtin": tags.name,
  comment: tags.blockComment,
  lineComment: tags.lineComment,
  string: tags.string,
  number: tags.number,
  variableName: tags.variableName,
};

const IDENTIFIER_RE = /^[A-Za-z_][A-Za-z0-9_]*/;
const NUMBER_RE = /^(0x[0-9a-fA-F_]+|0b[01_]+|0o[0-7_]+|[0-9][0-9_]*(\.[0-9][0-9_]*)?([eE][+-]?[0-9]+)?)/;
const WHITESPACE_RE = /^[ \t]+/;
// Longest-match-first so multi-char operators (e.g. "<<=", "|>", "??") are
// not shadowed by their single-char prefixes.
const OPERATOR_TOKENS = [...TOKEN_TO_TOKEN_NAME.keys()]
  .filter((t) => !IDENTIFIER_RE.test(t))
  .sort((a, b) => b.length - a.length);

export interface Cm6SimpleTokenState {
  inBlockComment: boolean;
  inString: "\"" | "'" | "`" | null;
}

/** CM6 StreamLanguage token classifier derived from the Tree-sitter keyword /
 * operator / literal capture groups above. This is a lexical (regex-driven)
 * approximation of highlights.scm's node-shaped queries — adequate for
 * syntax-highlighting a notebook cell without embedding a full Lezer parser
 * for the Simple grammar. */
export const simpleStreamParser: StreamParser<Cm6SimpleTokenState> = {
  name: "simple",
  tokenTable: TOKEN_TABLE,
  startState(): Cm6SimpleTokenState {
    return { inBlockComment: false, inString: null };
  },
  token(stream, state) {
    if (state.inBlockComment) {
      if (stream.match(/^[\s\S]*?\*\//)) {
        state.inBlockComment = false;
      } else {
        stream.skipToEnd();
      }
      return "comment";
    }
    if (state.inString !== null) {
      const quote = state.inString;
      if (stream.match(new RegExp("^(?:\\\\.|[^" + quote + "\\\\])*" + quote))) {
        state.inString = null;
      } else {
        stream.skipToEnd();
      }
      return "string";
    }
    if (stream.eatSpace()) return null;

    if (stream.match("//")) {
      stream.skipToEnd();
      return "lineComment";
    }
    if (stream.match("/*")) {
      state.inBlockComment = true;
      return "comment";
    }
    for (const q of ["\"", "'", "`"] as const) {
      if (stream.match(q)) {
        state.inString = q;
        return "string";
      }
    }
    if (stream.match(NUMBER_RE)) return "number";

    for (const op of OPERATOR_TOKENS) {
      if (stream.match(op)) {
        return TOKEN_TO_TOKEN_NAME.get(op) || null;
      }
    }

    const idMatch = stream.match(IDENTIFIER_RE);
    if (idMatch) {
      const word = Array.isArray(idMatch) ? idMatch[0] : stream.current();
      const tokenName = TOKEN_TO_TOKEN_NAME.get(word);
      if (tokenName) return tokenName;
      return "variableName";
    }

    stream.next();
    return null;
  },
};

export const simpleCm6Language = StreamLanguage.define(simpleStreamParser);
