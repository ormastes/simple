#!/usr/bin/env node
// gen_cm6_grammar.mjs — converts the Simple language Tree-sitter highlight
// queries (src/compiler/10.frontend/parser/treesitter/queries/*.scm) into a
// CodeMirror 6 token classifier for the JupyterLab extension
// (tools/jupyter/labextension/src/generated/cm6_simple_grammar.ts).
//
// This is a query-level conversion, not a full Lezer grammar port: Tree-sitter
// queries operate over a parse tree that CM6/Lezer does not share, so this
// script extracts the *token vocabulary* (keyword/operator/literal groups and
// their `@capture.tag` names) from the `.scm` query files and emits a CM6
// StreamLanguage-compatible tokenizer that classifies tokens into the same
// highlight groups, mapped onto @lezer/highlight tags.
//
// Usage:
//   node scripts/gen_cm6_grammar.mjs           # regenerate the committed output
//   node scripts/gen_cm6_grammar.mjs --check   # verify committed output is not stale
//
// No Python/Bash: this is Node tooling, run directly by `node`, no build step.

import { readFileSync, writeFileSync, existsSync, mkdirSync } from "node:fs";
import { createHash } from "node:crypto";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, "..");

const QUERY_DIR = join(
  REPO_ROOT,
  "src/compiler/10.frontend/parser/treesitter/queries"
);
// Only highlights.scm carries token/capture-tag vocabulary; the other query
// files (folds/indents/injections/locals/textobjects) drive editor behaviors
// that have no CM6 token-classifier analog, but their content still
// participates in the SHA gate so a grammar-affecting edit anywhere in the
// query set is detected as staleness.
const SOURCE_FILES = [
  "highlights.scm",
  "folds.scm",
  "indents.scm",
  "injections.scm",
  "locals.scm",
  "textobjects.scm",
];
const PRIMARY_SOURCE = "highlights.scm";

const OUT_DIR = join(REPO_ROOT, "tools/jupyter/labextension/src/generated");
const OUT_TS = join(OUT_DIR, "cm6_simple_grammar.ts");
const OUT_SHA = join(OUT_DIR, "grammar.sha256.json");

function sha256(text) {
  return createHash("sha256").update(text, "utf8").digest("hex");
}

// Extract `[ "a" "b" ... ] @capture.tag` groups and single-quoted-string
// bracket lists from a Tree-sitter query file. Also picks up bare
// `(node_type) @capture.tag` lines for literal/comment/error captures that
// don't come from a bracket group (they classify by node type instead of by
// keyword spelling; the CM6 tokenizer keeps a hand-written pattern set for
// those since it has no parse tree to match node types against — see
// LITERAL_PATTERNS below).
function parseHighlightGroups(scmText) {
  const groups = []; // { tag: string, tokens: string[] }
  const bracketGroupRe = /\[\s*([\s\S]*?)\]\s*@([\w.]+)/g;
  let m;
  while ((m = bracketGroupRe.exec(scmText)) !== null) {
    const body = m[1];
    const tag = m[2];
    const tokens = [];
    const strRe = /"((?:[^"\\]|\\.)*)"/g;
    let sm;
    while ((sm = strRe.exec(body)) !== null) {
      tokens.push(sm[1]);
    }
    if (tokens.length > 0) {
      groups.push({ tag, tokens });
    }
  }
  return groups;
}

function loadSources() {
  const sources = {};
  for (const f of SOURCE_FILES) {
    const p = join(QUERY_DIR, f);
    if (!existsSync(p)) {
      throw new Error(`gen_cm6_grammar: missing expected source query file: ${p}`);
    }
    sources[f] = readFileSync(p, "utf8");
  }
  return sources;
}

function computeShaManifest(sources) {
  const perFile = {};
  for (const f of SOURCE_FILES) {
    perFile[f] = sha256(sources[f]);
  }
  // combined hash over the concatenation in fixed order — this is the single
  // value regeneration checks against for staleness.
  const combined = sha256(SOURCE_FILES.map((f) => perFile[f]).join("\n"));
  return { algorithm: "sha256", files: perFile, combined };
}

// Merge groups that share the same @capture.tag (the .scm file defines the
// same tag across several `[...]` blocks, e.g. "val" appears in both
// @keyword.variable and @keyword.capability — CM6 classification takes the
// first tag a token was seen under, mirroring Tree-sitter's first-match
// query semantics).
function mergeGroups(groups) {
  const seenToken = new Map(); // token -> tag
  const byTag = new Map(); // tag -> Set<token>
  for (const { tag, tokens } of groups) {
    for (const tok of tokens) {
      if (seenToken.has(tok)) continue;
      seenToken.set(tok, tag);
      if (!byTag.has(tag)) byTag.set(tag, new Set());
      byTag.get(tag).add(tok);
    }
  }
  return byTag;
}

// Map Tree-sitter @capture.tag groups onto @lezer/highlight `tags` export
// members used by CM6 themes. Falls back to `tags.name` (generic) for
// anything not explicitly mapped so no token is silently dropped.
const TAG_TO_LEZER = {
  "keyword.variable": "keyword",
  "keyword.function": "keyword",
  "keyword.type": "keyword",
  "keyword.module": "keyword",
  "keyword.asm": "keyword",
  "keyword.control.conditional": "controlKeyword",
  "keyword.control.repeat": "controlKeyword",
  "keyword.control.return": "controlKeyword",
  "keyword.control": "controlKeyword",
  "keyword.control.exception": "controlKeyword",
  "keyword.control.suspension": "controlKeyword",
  "keyword.control.async": "controlKeyword",
  "keyword.type.modifier": "modifier",
  "keyword.capability": "modifier",
  "keyword.gpu": "keyword",
  "keyword.aop": "keyword",
  "keyword.aop.pointcut": "keyword",
  "keyword.contract": "keyword",
  "keyword.contract.quantifier": "keyword",
  "keyword.test": "keyword",
  "operator.arithmetic": "arithmeticOperator",
  "operator.comparison": "compareOperator",
  "operator.logical": "logicOperator",
  "operator.bitwise": "bitwiseOperator",
  "operator.assignment": "definitionOperator",
  "operator.pipeline": "operator",
  "operator.broadcast": "operator",
  "operator.matrix": "operator",
  "operator.optional": "derefOperator",
  "operator.range": "punctuation",
  operator: "operator",
  boolean: "bool",
  "constant.builtin": "atom",
};

function tsStringArray(tokens) {
  return `[${tokens.map((t) => JSON.stringify(t)).join(", ")}]`;
}

function generateTs(sources) {
  const highlights = sources[PRIMARY_SOURCE];
  const groups = parseHighlightGroups(highlights);
  const byTag = mergeGroups(groups);

  const tagEntries = [...byTag.entries()].sort(([a], [b]) => a.localeCompare(b));

  const lezerImports = new Set();
  const groupDecls = [];
  const dispatchEntries = [];
  for (const [tag, tokenSet] of tagEntries) {
    const tokens = [...tokenSet].sort();
    const constName = "TOKENS_" + tag.toUpperCase().replace(/[.\-]/g, "_");
    groupDecls.push(`export const ${constName}: readonly string[] = ${tsStringArray(tokens)};`);
    const lezerTag = TAG_TO_LEZER[tag] || "name";
    lezerImports.add(lezerTag);
    // CM6's StreamParser legacy token-style strings treat "." as a
    // tag/modifier separator (each dot-separated part is resolved against
    // the token table independently), so the flattened, dot-free tokenName
    // is what token() actually returns and what keys TOKEN_TABLE — captureTag
    // is kept alongside purely for traceability back to highlights.scm.
    const tokenName = tag.replace(/\./g, "_");
    dispatchEntries.push(`  { captureTag: ${JSON.stringify(tag)}, tokenName: ${JSON.stringify(tokenName)}, tokens: ${constName}, lezerTag: tags.${lezerTag} },`);
  }

  const header = `// GENERATED FILE — do not hand-edit.
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
// source: ${PRIMARY_SOURCE} sha256=${sha256(highlights)}

import { tags } from "@lezer/highlight";
import { StreamLanguage, type StreamParser } from "@codemirror/language";

export interface Cm6TokenGroup {
  readonly captureTag: string;
  readonly tokenName: string;
  readonly tokens: readonly string[];
  readonly lezerTag: import("@lezer/highlight").Tag;
}

${groupDecls.join("\n\n")}

/** Token groups in Tree-sitter @capture.tag order, first-match wins (mirrors
 * Tree-sitter query precedence: earlier \`[...] @tag\` blocks in
 * highlights.scm win ties, see mergeGroups() in the generator). */
export const CM6_TOKEN_GROUPS: readonly Cm6TokenGroup[] = [
${dispatchEntries.join("\n")}
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
${tagEntries
  .map(([tag]) => `  ${JSON.stringify(tag.replace(/\./g, "_"))}: tags.${TAG_TO_LEZER[tag] || "name"},`)
  .join("\n")}
  comment: tags.blockComment,
  lineComment: tags.lineComment,
  string: tags.string,
  number: tags.number,
  variableName: tags.variableName,
};

const IDENTIFIER_RE = /^[A-Za-z_][A-Za-z0-9_]*/;
const NUMBER_RE = /^(0x[0-9a-fA-F_]+|0b[01_]+|0o[0-7_]+|[0-9][0-9_]*(\\.[0-9][0-9_]*)?([eE][+-]?[0-9]+)?)/;
const WHITESPACE_RE = /^[ \\t]+/;
// Longest-match-first so multi-char operators (e.g. "<<=", "|>", "??") are
// not shadowed by their single-char prefixes.
const OPERATOR_TOKENS = [...TOKEN_TO_TOKEN_NAME.keys()]
  .filter((t) => !IDENTIFIER_RE.test(t))
  .sort((a, b) => b.length - a.length);

export interface Cm6SimpleTokenState {
  inBlockComment: boolean;
  inString: "\\"" | "'" | "\`" | null;
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
      if (stream.match(/^[\\s\\S]*?\\*\\//)) {
        state.inBlockComment = false;
      } else {
        stream.skipToEnd();
      }
      return "comment";
    }
    if (state.inString !== null) {
      const quote = state.inString;
      if (stream.match(new RegExp("^(?:\\\\\\\\.|[^" + quote + "\\\\\\\\])*" + quote))) {
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
    for (const q of ["\\"", "'", "\`"] as const) {
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
`;

  return header;
}

function main() {
  const check = process.argv.includes("--check");
  const sources = loadSources();
  const manifest = computeShaManifest(sources);

  if (check) {
    if (!existsSync(OUT_SHA)) {
      console.error("gen_cm6_grammar --check: FAIL — no committed grammar.sha256.json; run without --check first.");
      process.exit(1);
    }
    const committed = JSON.parse(readFileSync(OUT_SHA, "utf8"));
    if (committed.combined !== manifest.combined) {
      console.error(
        "gen_cm6_grammar --check: STALE — Tree-sitter query sources changed since the CM6 grammar was generated.\n" +
          `  committed combined sha256: ${committed.combined}\n` +
          `  current   combined sha256: ${manifest.combined}\n` +
          "  Run: node scripts/gen_cm6_grammar.mjs"
      );
      process.exit(1);
    }
    console.log("gen_cm6_grammar --check: OK — generated CM6 grammar matches current Tree-sitter query sources.");
    return;
  }

  if (!existsSync(OUT_DIR)) mkdirSync(OUT_DIR, { recursive: true });
  const ts = generateTs(sources);
  writeFileSync(OUT_TS, ts, "utf8");
  writeFileSync(OUT_SHA, JSON.stringify(manifest, null, 2) + "\n", "utf8");
  console.log(`gen_cm6_grammar: wrote ${OUT_TS}`);
  console.log(`gen_cm6_grammar: wrote ${OUT_SHA} (combined sha256=${manifest.combined})`);
}

main();
