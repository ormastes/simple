import { readFileSync } from "node:fs";
import { join } from "node:path";
import { highlightTree, classHighlighter } from "@lezer/highlight";
import {
  simpleCm6Language,
  TOKEN_TABLE,
  TOKENS_KEYWORD_FUNCTION,
  TOKENS_KEYWORD_VARIABLE,
  TOKENS_KEYWORD_CONTROL_CONDITIONAL,
  TOKENS_KEYWORD_CONTROL_RETURN,
  TOKENS_OPERATOR_COMPARISON,
} from "../src/generated/cm6_simple_grammar";

const FIXTURE_PATH = join(__dirname, "fixtures", "hello.spl");

interface TokenSpan {
  from: number;
  to: number;
  classes: string;
  text: string;
}

/** Parse `doc` with the generated Simple CM6 language and collect every
 * highlighted span via @lezer/highlight's `classHighlighter` — the same
 * highlighter and the same highlightTree path a CM6 EditorView uses to turn
 * parse-tree tags into `tok-*` CSS classes for a real theme. */
function highlightAll(doc: string): TokenSpan[] {
  const tree = simpleCm6Language.parser.parse(doc);
  const spans: TokenSpan[] = [];
  highlightTree(tree, classHighlighter, (from, to, classes) => {
    spans.push({ from, to, classes, text: doc.slice(from, to) });
  });
  return spans;
}

function findSpan(spans: TokenSpan[], text: string): TokenSpan | undefined {
  return spans.find((s) => s.text === text);
}

describe("Simple CM6 grammar (generated from Tree-sitter highlights.scm)", () => {
  const fixture = readFileSync(FIXTURE_PATH, "utf8");

  it("token vocabulary is non-empty and sourced from highlights.scm", () => {
    expect(TOKENS_KEYWORD_FUNCTION).toContain("fn");
    expect(TOKENS_KEYWORD_VARIABLE).toContain("val");
    expect(TOKENS_KEYWORD_VARIABLE).toContain("var");
    expect(TOKENS_KEYWORD_CONTROL_CONDITIONAL).toContain("if");
    expect(TOKENS_OPERATOR_COMPARISON).toContain("==");
  });

  it("highlights the fixture .spl cell with expected CM6 token classes", () => {
    const spans = highlightAll(fixture);
    expect(spans.length).toBeGreaterThan(0);

    // Rendered classes, via @lezer/highlight's classHighlighter (what a real
    // CM6 EditorView + theme sees). keyword.function/variable/control.* all
    // map onto @lezer/highlight's `keyword`/`controlKeyword` tags, which
    // classHighlighter's built-in ruleset both render as "tok-keyword" — CM6
    // themes are free to add a rule distinguishing controlKeyword, but the
    // shipped default does not, same as VSCode's TextMate scopes collapsing
    // onto a handful of editor.tokenColorCustomizations buckets.
    for (const kw of ["fn", "val", "var", "if", "return"]) {
      const span = findSpan(spans, kw);
      expect(span).toBeDefined();
      expect(span!.classes).toBe("tok-keyword");
    }
    for (const op of ["->", "=", "==", "+"]) {
      const span = findSpan(spans, op);
      expect(span).toBeDefined();
      expect(span!.classes).toBe("tok-operator");
    }

    const str = findSpan(spans, '"hello world"');
    expect(str).toBeDefined();
    expect(str!.classes).toBe("tok-string");

    const num = findSpan(spans, "0");
    expect(num).toBeDefined();
    expect(num!.classes).toBe("tok-number");

    const comment = spans.find((s) => s.classes === "tok-comment");
    expect(comment).toBeDefined();
    expect(comment!.text).toContain("fixture cell");
  });

  it("does not misclassify a plain identifier as a keyword", () => {
    const spans = highlightAll(fixture);
    const greeting = findSpan(spans, "greeting");
    expect(greeting).toBeDefined();
    expect(greeting!.classes).not.toContain("keyword");
    expect(greeting!.classes).toBe("tok-variableName");
  });

  it("preserves Tree-sitter's finer capture taxonomy at the data layer, even where CM6's default theme renders it collapsed", () => {
    // TOKEN_TABLE is keyed by the flattened tokenName (dots -> underscores)
    // straight from highlights.scm's @capture.tag names, so "fn"
    // (keyword.function) and "if" (keyword.control.conditional) resolve to
    // distinct table entries even though both currently render as the same
    // @lezer/highlight `keyword`-family tag under classHighlighter above.
    expect(TOKEN_TABLE["keyword_function"]).toBeDefined();
    expect(TOKEN_TABLE["keyword_control_conditional"]).toBeDefined();
    expect(TOKEN_TABLE["keyword_function"]).not.toBe(TOKEN_TABLE["keyword_control_conditional"]);
    expect(TOKENS_KEYWORD_FUNCTION).not.toEqual(
      expect.arrayContaining(TOKENS_KEYWORD_CONTROL_CONDITIONAL)
    );
    expect(TOKENS_KEYWORD_CONTROL_RETURN).toContain("return");
  });
});
