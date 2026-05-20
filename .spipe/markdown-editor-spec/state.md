# Phase 4: Markdown Editor Test Specification
**Agent:** QA Lead (Spec Agent)  
**Date:** 2026-05-11  
**Status:** Superseded — Implementation Complete  
**Deliverable:** Comprehensive test matrix for Phase 5 implementation

---

## Pipeline Status Update (2026-05-20)

**This spec pipeline (Phase 4) is complete and superseded.**

The Phase 5 implementation was carried out under the `editor-ide-platform` pipeline
(all 8 phases marked done 2026-05-19) and the `md-editor-production` pipeline
(65/65 tests passing).

### What was actually implemented

The implementation uses a different but equivalent architecture to the API names
proposed in this spec document:

| Spec concept | Actual implementation |
|---|---|
| `MarkdownLexer` / `MarkdownParser` | `std.common.markdown.{parse,block,inline,adapter}` |
| `MarkdownTuiRenderer` | `std.editor.render.md_renderer` |
| `MarkdownEditor` | `std.editor.core.session` + `app.editor.editor_controller` |
| `MarkdownPreviewPane` | `std.editor.view.preview_pane` |
| `MarkdownDiagnostics` | `std.editor.services.md_diagnostics` |
| Command palette | `std.editor.extensions.builtin.md_commands` + `md_edit_assist` |

### Actual test coverage (system specs)

| File | Tests |
|---|---|
| `test/system/editor_markdown_spec.spl` | 84 |
| `test/system/editor_markdown_document_decor_spec.spl` | 6 |
| `test/system/editor_markdown_office_layout_spec.spl` | 17 |
| `test/tools/desktop/markdown_visual_editor_spec.spl` | 6 |
| **Total** | **113** |

### Why the spec API names differ

This state.md was written as an aspirational API sketch on 2026-05-11 before
architecture was finalized. The `editor-ide-platform` pipeline adopted a
layered library architecture (`std.editor.*`, `std.common.markdown.*`) which
covers the same semantic surface with different class/function names.

### No further action needed

- The 83 test cases listed below remain as spec documentation only.
- Do NOT create new spec files based on the API names in this document
  (`MarkdownLexer`, `MarkdownParser`, etc.) — they do not match the real
  implementation and would produce false-failing tests.
- To run the actual markdown editor tests: `bin/simple test test/system/editor_markdown_spec.spl`

---

---

## Executive Summary

This specification defines the test matrix, acceptance criteria, and edge case coverage for the markdown editor implementation. It translates Phase 3 architectural contracts into concrete, measurable test scenarios covering:

1. **Markdown AST Parser** — Lexer, block/inline parsing, incremental updates, CommonMark compliance
2. **Markdown Renderer** — TUI (ANSI), GUI (SDL2), LSP (diagnostic) fidelity
3. **Editor Command Palette** — 50+ markdown-specific commands with dispatch verification
4. **Markdown Diagnostics** — Link validation, heading outline, code fence checking
5. **Preview Pane Integration** — Sync latency <100ms, correctness, split-pane layout
6. **Performance & Stress Testing** — 10MB+ documents, memory bounds, render frame rates
7. **Cross-Platform Validation** — macOS, Linux, Windows equivalence

---

## 1. Markdown AST Parser Specification

### 1.1 Lexer Tests

**Objective:** Verify tokenization of markdown input into structured tokens.

**Test Suite: markdown_lexer_spec.spl**

```
describe "MarkdownLexer tokenization":
  it "tokenizes heading level 1 (#)":
    val lexer = MarkdownLexer.new("# Hello")
    val tokens = lexer.lex()
    expect(tokens[0].type).to_equal(TokenType.Heading)
    expect(tokens[0].level).to_equal(1)
    expect(tokens[0].text).to_equal("Hello")

  it "tokenizes unordered list (- item)":
    val lexer = MarkdownLexer.new("- Item 1\n- Item 2")
    val tokens = lexer.lex()
    expect(tokens[0].type).to_equal(TokenType.ListItem)
    expect(tokens[0].ordered).to_equal(false)

  it "tokenizes code block (``` lang)":
    val lexer = MarkdownLexer.new("```rust\nfn main() {}\n```")
    val tokens = lexer.lex()
    expect(tokens[0].type).to_equal(TokenType.CodeBlock)
    expect(tokens[0].language).to_equal("rust")

  it "tokenizes emphasis (*text*, **bold**)":
    val lexer = MarkdownLexer.new("*italic* **bold**")
    val tokens = lexer.lex()
    expect(tokens[0].type).to_equal(TokenType.Emphasis)
    expect(tokens[1].type).to_equal(TokenType.Strong)

  it "tokenizes links [text](url)":
    val lexer = MarkdownLexer.new("[link](https://example.com)")
    val tokens = lexer.lex()
    expect(tokens[0].type).to_equal(TokenType.Link)
    expect(tokens[0].url).to_equal("https://example.com")

  it "tokenizes inline code (`code`)":
    val lexer = MarkdownLexer.new("Use `var x = 1` in expressions")
    val tokens = lexer.lex()
    expect(tokens[1].type).to_equal(TokenType.InlineCode)

  it "tokenizes block quote (> text)":
    val lexer = MarkdownLexer.new("> Quote\n> Line 2")
    val tokens = lexer.lex()
    expect(tokens[0].type).to_equal(TokenType.BlockQuote)

  it "handles nested list indentation":
    val lexer = MarkdownLexer.new("- Item 1\n  - Nested 1\n  - Nested 2\n- Item 2")
    val tokens = lexer.lex()
    expect(tokens[1].indent_level).to_equal(1)
    expect(tokens[3].indent_level).to_equal(0)

  it "tokenizes horizontal rule (---, ***, ___)":
    val lexer = MarkdownLexer.new("---")
    val tokens = lexer.lex()
    expect(tokens[0].type).to_equal(TokenType.HorizontalRule)

  it "handles line breaks (\\\\ or two spaces)":
    val lexer = MarkdownLexer.new("Line 1  \nLine 2")
    val tokens = lexer.lex()
    expect(tokens[1].type).to_equal(TokenType.HardBreak)
```

**Edge Cases (marked slow tests):**
- Malformed markdown (mismatched delimiters, unclosed code blocks)
- Deeply nested structures (10+ levels)
- Mixed emphasis markers (`*text_with_underscore*`)
- Escaped characters (`\*not italic\*`)
- Unicode in headings and links
- Empty tokens (blank lines, trailing whitespace)

**Acceptance Criteria:**
- AC-1.1: All token types defined in Phase 3 AST recognized
- AC-1.2: Nesting levels captured (list indent, blockquote depth)
- AC-1.3: Edge cases handled without panic/crash

---

### 1.2 Parser (Block/Inline) Tests

**Objective:** Verify AST construction from token stream.

**Test Suite: markdown_parser_spec.spl**

```
describe "MarkdownParser AST construction":
  it "parses paragraph block":
    val parser = MarkdownParser.new("This is a paragraph.")
    val ast = parser.parse()
    expect(ast[0].type).to_equal(BlockType.Paragraph)
    expect(ast[0].inline_nodes.len()).to_be_greater_than(0)

  it "parses heading with inline nodes":
    val parser = MarkdownParser.new("# **Bold** Heading")
    val ast = parser.parse()
    expect(ast[0].type).to_equal(BlockType.Heading)
    expect(ast[0].level).to_equal(1)
    expect(ast[0].inline_nodes[0].type).to_equal(InlineNodeType.Strong)

  it "parses unordered list with items":
    val parser = MarkdownParser.new("- Item 1\n- Item 2")
    val ast = parser.parse()
    expect(ast[0].type).to_equal(BlockType.List)
    expect(ast[0].ordered).to_equal(false)
    expect(ast[0].items.len()).to_equal(2)

  it "parses code block with language":
    val parser = MarkdownParser.new("```python\nprint('hello')\n```")
    val ast = parser.parse()
    expect(ast[0].type).to_equal(BlockType.CodeBlock)
    expect(ast[0].language).to_equal("python")

  it "parses nested blockquote":
    val parser = MarkdownParser.new("> Quote\n> > Nested")
    val ast = parser.parse()
    expect(ast[0].type).to_equal(BlockType.BlockQuote)
    expect(ast[0].children[1].type).to_equal(BlockType.BlockQuote)

  it "parses mixed block types in document":
    val parser = MarkdownParser.new("# Heading\n\nParagraph.\n\n- List item")
    val ast = parser.parse()
    expect(ast.len()).to_equal(3)
    expect(ast[0].type).to_equal(BlockType.Heading)
    expect(ast[1].type).to_equal(BlockType.Paragraph)
    expect(ast[2].type).to_equal(BlockType.List)

  it "parses link with title attribute":
    val parser = MarkdownParser.new('[link](url "title")')
    val ast = parser.parse()
    val link = ast[0].inline_nodes[0]
    expect(link.type).to_equal(InlineNodeType.Link)
    expect(link.title).to_equal(Option.Some("title"))

  it "parses image syntax ![alt](src)":
    val parser = MarkdownParser.new('![alt text](image.png)')
    val ast = parser.parse()
    val img = ast[0].inline_nodes[0]
    expect(img.type).to_equal(InlineNodeType.Image)
    expect(img.alt).to_equal("alt text")
```

**Edge Cases:**
- Empty document
- Document with only blank lines
- Paragraph with complex inline formatting
- List items with multi-line content
- Deeply nested blockquotes (5+ levels)
- Incomplete markdown (unclosed code block at EOF)

**Acceptance Criteria:**
- AC-1.3: Block AST matches Phase 3 data structure
- AC-1.4: Inline nodes correctly nested in blocks
- AC-1.5: 95%+ CommonMark subset compliance (verified against spec test suite)

---

### 1.3 Incremental Parsing Tests

**Objective:** Verify that edits produce minimal re-parsing without losing correctness.

**Test Suite: markdown_incremental_parser_spec.spl**

```
describe "MarkdownParser incremental updates":
  it "reparsing after single character insertion":
    var parser = MarkdownParser.new("Hello world")
    var ast1 = parser.parse()
    parser.edit(position: 5, inserted: " bold", deleted: 0)
    var ast2 = parser.parse_incremental()
    expect(ast1.len()).to_equal(ast2.len())
    # Verify text content updated
    expect(parser.text).to_contain("Hello bold world")

  it "reparsing after line deletion":
    var parser = MarkdownParser.new("Line 1\nLine 2\nLine 3")
    parser.edit(position: 0, inserted: "", deleted: 7)  # Delete "Line 1\n"
    var ast = parser.parse_incremental()
    expect(ast[0].text).to_start_with("Line 2")

  it "reparsing after heading level change":
    var parser = MarkdownParser.new("# Heading")
    parser.edit(position: 0, inserted: "##", deleted: 1)  # Change # to ##
    var ast = parser.parse_incremental()
    expect(ast[0].level).to_equal(2)

  it "reparsing preserves unmodified blocks":
    var parser = MarkdownParser.new("# H1\n\nPara\n\n# H2")
    var ast1 = parser.parse()
    parser.edit(position: 8, inserted: "NEW ", deleted: 0)  # Edit middle paragraph
    var ast2 = parser.parse_incremental()
    # Blocks 0 (H1) and 2 (H2) should be unchanged
    expect(ast1[0]).to_equal(ast2[0])
    expect(ast1[2]).to_equal(ast2[2])

  it "handles list item addition":
    var parser = MarkdownParser.new("- Item 1\n- Item 2")
    parser.edit(position: 18, inserted: "\n- Item 3", deleted: 0)
    var ast = parser.parse_incremental()
    expect(ast[0].items.len()).to_equal(3)

  it "handles code block language change":
    var parser = MarkdownParser.new("```python\ncode\n```")
    parser.edit(position: 3, inserted: "rust", deleted: 6)
    var ast = parser.parse_incremental()
    expect(ast[0].language).to_equal("rust")
```

**Performance Targets:**
- Incremental parse <50ms for typical edits (insertion/deletion <100 chars)
- Reparsing only affected block and adjacent siblings

**Acceptance Criteria:**
- AC-1.6: Incremental parser detects minimal change scope
- AC-1.7: Edit-to-AST latency <50ms for realistic edits

---

## 2. Markdown Renderer Specification

### 2.1 TUI Renderer (ANSI Terminal)

**Test Suite: markdown_tui_renderer_spec.spl**

```
describe "MarkdownTuiRenderer ANSI output":
  it "renders heading with bold ANSI codes":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("# Bold Heading").parse()
    var output = renderer.render(ast)
    expect(output).to_contain("\x1b[1m")  # Bold ANSI code
    expect(output).to_contain("# Bold Heading")

  it "renders emphasis with color codes":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("*italic* **bold**").parse()
    var output = renderer.render(ast)
    expect(output).to_contain("\x1b[3m")  # Italic ANSI code
    expect(output).to_contain("\x1b[1m")  # Bold ANSI code

  it "renders code with monospace marker":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("`inline code`").parse()
    var output = renderer.render(ast)
    expect(output).to_contain("inline code")

  it "renders list with indentation":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("- Item 1\n  - Nested\n- Item 2").parse()
    var output = renderer.render(ast)
    var lines = output.split("\n")
    expect(lines[1]).to_start_with("  ")  # Nested indented

  it "renders code block with fence":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("```python\nprint('hi')\n```").parse()
    var output = renderer.render(ast)
    expect(output).to_contain("print('hi')")
    expect(output).to_contain("```")  # Code fence preserved

  it "renders blockquote with prefix":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("> Quote text").parse()
    var output = renderer.render(ast)
    expect(output).to_start_with("> ")

  it "renders link with URL visible":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("[text](http://url.com)").parse()
    var output = renderer.render(ast)
    expect(output).to_contain("text")
    expect(output).to_contain("http://url.com")

  it "renders image with alt text":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("![alt](img.png)").parse()
    var output = renderer.render(ast)
    expect(output).to_contain("alt")
    expect(output).to_contain("img.png")

  it "renders horizontal rule":
    var renderer = MarkdownTuiRenderer.new()
    var ast = MarkdownParser.new("---").parse()
    var output = renderer.render(ast)
    expect(output).to_match(/^-{3,}$/)  # Horizontal line of dashes
```

**Syntax Highlighting Coverage Matrix:**
- Headings (6 levels)
- Emphasis (italic, bold, bold-italic)
- Code (inline, block with language highlighting)
- Links (text + URL)
- Lists (ordered, unordered, nested)
- Blockquotes (nested)
- Horizontal rules

**Acceptance Criteria:**
- AC-2.1: All markdown block types rendered with visual hierarchy
- AC-2.2: ANSI color/formatting codes applied correctly
- AC-2.3: Terminal width constraints respected (word wrapping, line truncation)

---

### 2.2 GUI Renderer (SDL2/HTML)

**Test Suite: markdown_gui_renderer_spec.spl**

```
describe "MarkdownGuiRenderer SDL2/HTML output":
  it "renders heading as larger text":
    var renderer = MarkdownGuiRenderer.new()
    var ast = MarkdownParser.new("# Heading").parse()
    var gui_output = renderer.render(ast)
    expect(gui_output.elements[0].type).to_equal(Element.Text)
    expect(gui_output.elements[0].font_size).to_be_greater_than(16)

  it "renders bold text with weight":
    var renderer = MarkdownGuiRenderer.new()
    var ast = MarkdownParser.new("**bold text**").parse()
    var gui_output = renderer.render(ast)
    expect(gui_output.elements[0].font_weight).to_equal(700)

  it "renders code block with monospace font":
    var renderer = MarkdownGuiRenderer.new()
    var ast = MarkdownParser.new("```\ncode\n```").parse()
    var gui_output = renderer.render(ast)
    expect(gui_output.elements[0].font_family).to_contain("monospace")

  it "renders link as clickable element":
    var renderer = MarkdownGuiRenderer.new()
    var ast = MarkdownParser.new("[link](url)").parse()
    var gui_output = renderer.render(ast)
    expect(gui_output.elements[0].type).to_equal(Element.Link)
    expect(gui_output.elements[0].href).to_equal("url")

  it "renders image as bitmap element":
    var renderer = MarkdownGuiRenderer.new()
    var ast = MarkdownParser.new("![alt](img.png)").parse()
    var gui_output = renderer.render(ast)
    expect(gui_output.elements[0].type).to_equal(Element.Image)
    expect(gui_output.elements[0].src).to_equal("img.png")

  it "renders list with proper layout":
    var renderer = MarkdownGuiRenderer.new()
    var ast = MarkdownParser.new("- Item 1\n- Item 2").parse()
    var gui_output = renderer.render(ast)
    expect(gui_output.elements[0].type).to_equal(Element.List)
    expect(gui_output.elements[0].items.len()).to_equal(2)

  it "renders blockquote with visual styling":
    var renderer = MarkdownGuiRenderer.new()
    var ast = MarkdownParser.new("> Quote").parse()
    var gui_output = renderer.render(ast)
    expect(gui_output.elements[0].style.border_left).to_be_truthy()
```

**Cross-Platform Fidelity:**
- Font rendering consistency (macOS, Linux, Windows)
- Color palette consistency (light/dark modes)
- Layout spacing (padding, margins, line-height)

**Acceptance Criteria:**
- AC-2.4: GUI renderer produces layoutable elements
- AC-2.5: Cross-platform rendering within 5% pixel accuracy
- AC-2.6: Images and links resolveably (local/http paths)

---

### 2.3 LSP Renderer (Diagnostic/Hover)

**Test Suite: markdown_lsp_renderer_spec.spl**

```
describe "MarkdownLspRenderer diagnostic output":
  it "renders hover for heading":
    var renderer = MarkdownLspRenderer.new()
    var ast = MarkdownParser.new("# Heading").parse()
    var hover = renderer.hover_for_block(ast[0])
    expect(hover.contents).to_contain("Heading (level 1)")

  it "renders diagnostic for unclosed code block":
    var renderer = MarkdownLspRenderer.new()
    var ast = MarkdownParser.new("```\ncode").parse()
    var diags = renderer.diagnostics(ast)
    expect(diags.len()).to_be_greater_than(0)
    expect(diags[0].severity).to_equal(DiagnosticSeverity.Warning)

  it "renders completion suggestions for link":
    var renderer = MarkdownLspRenderer.new()
    var position = (line: 0, col: 1)
    var completions = renderer.completions_at_position(position)
    expect(completions.len()).to_be_greater_than(0)
```

**Acceptance Criteria:**
- AC-2.7: Hover information available for all block types
- AC-2.8: Diagnostics mapped to source location (line, column)
- AC-2.9: Completions available for commands, links, languages

---

## 3. Editor Command Palette Specification

### 3.1 Markdown-Specific Commands (50+)

**Test Suite: markdown_commands_spec.spl**

```
describe "MarkdownCommandPalette":
  it "command 'Toggle Bold' wraps selection":
    var editor = MarkdownEditor.new()
    editor.insert_text("hello world")
    editor.set_selection(0, 5)  # "hello"
    editor.execute_command("toggle-bold")
    expect(editor.text).to_contain("**hello**")

  it "command 'Toggle Italic' wraps selection":
    var editor = MarkdownEditor.new()
    editor.insert_text("hello")
    editor.set_selection(0, 5)
    editor.execute_command("toggle-italic")
    expect(editor.text).to_contain("*hello*")

  it "command 'Toggle Code' wraps selection":
    var editor = MarkdownEditor.new()
    editor.insert_text("var x")
    editor.set_selection(0, 5)
    editor.execute_command("toggle-code")
    expect(editor.text).to_contain("`var x`")

  it "command 'Insert Link' opens dialog":
    var editor = MarkdownEditor.new()
    editor.insert_text("link text")
    editor.execute_command("insert-link")
    # Command should prompt for URL
    expect(editor.dialog_open).to_equal(true)

  it "command 'Insert List' creates unordered list":
    var editor = MarkdownEditor.new()
    editor.execute_command("insert-list")
    expect(editor.text).to_contain("- ")

  it "command 'Promote Heading' increases level":
    var editor = MarkdownEditor.new()
    editor.insert_text("## Heading")
    editor.cursor_line = 0
    editor.execute_command("promote-heading")
    expect(editor.text).to_start_with("### ")

  it "command 'Demote Heading' decreases level":
    var editor = MarkdownEditor.new()
    editor.insert_text("### Heading")
    editor.cursor_line = 0
    editor.execute_command("demote-heading")
    expect(editor.text).to_start_with("## ")

  it "command 'Insert Code Block' inserts triple backticks":
    var editor = MarkdownEditor.new()
    editor.execute_command("insert-code-block")
    expect(editor.text).to_contain("```")

  it "command 'Indent List Item' increases nesting":
    var editor = MarkdownEditor.new()
    editor.insert_text("- Item")
    editor.cursor_line = 0
    editor.execute_command("indent-list-item")
    expect(editor.text).to_contain("  - Item")

  it "command 'Dedent List Item' decreases nesting":
    var editor = MarkdownEditor.new()
    editor.insert_text("  - Item")
    editor.cursor_line = 0
    editor.execute_command("dedent-list-item")
    expect(editor.text).to_contain("- Item")

  it "command 'Insert Quote' wraps in blockquote":
    var editor = MarkdownEditor.new()
    editor.insert_text("text")
    editor.set_selection(0, 4)
    editor.execute_command("insert-blockquote")
    expect(editor.text).to_contain("> text")

  it "command 'Insert Horizontal Rule' adds ---":
    var editor = MarkdownEditor.new()
    editor.execute_command("insert-horizontal-rule")
    expect(editor.text).to_contain("---")

  it "command 'Insert Table' creates 3x2 grid":
    var editor = MarkdownEditor.new()
    editor.execute_command("insert-table")
    expect(editor.text).to_contain("|")

  it "command 'Convert to Ordered List' changes bullets":
    var editor = MarkdownEditor.new()
    editor.insert_text("- Item 1\n- Item 2")
    editor.execute_command("convert-to-ordered-list")
    expect(editor.text).to_contain("1. Item 1")
    expect(editor.text).to_contain("2. Item 2")

  it "command 'Jump to Heading' shows outline":
    var editor = MarkdownEditor.new()
    editor.insert_text("# H1\n## H2\n### H3")
    editor.execute_command("jump-to-heading")
    expect(editor.outline.len()).to_equal(3)

  it "command 'Format Table' aligns columns":
    var editor = MarkdownEditor.new()
    editor.insert_text("| A | B |\n|---|---|\n| 1 | 22 |")
    editor.execute_command("format-table")
    # Table should have aligned columns
    var lines = editor.text.split("\n")
    expect(lines[2]).to_match(/\|\s+1\s+\|\s+22\s+\|/)
```

**Command Palette Coverage Matrix:**

| Category | Commands | Count |
|----------|----------|-------|
| Text Formatting | Bold, Italic, Code, Strikethrough | 4 |
| Headings | Promote, Demote, Set Level (1-6) | 8 |
| Lists | Insert, Indent, Dedent, Toggle Ordered/Unordered | 4 |
| Blocks | Quote, Code Block, HR, Table | 4 |
| Links/Media | Insert Link, Insert Image, Insert Reference | 3 |
| Outline | Jump to Heading, Show Outline, Goto Line | 3 |
| Selection | Expand Selection, Shrink Selection, Select Block | 3 |
| Formatting | Format Document, Format Paragraph, Cleanup Whitespace | 3 |
| Navigation | Move to Next Heading, Move to Previous Heading | 2 |
| Advanced | Insert TOC, Insert Footnote, Insert Macro | 3 |
| **Total** | | **~37-50** |

**Acceptance Criteria:**
- AC-3.1: All 50+ commands implemented and discoverable in palette
- AC-3.2: Command execution produces correct text mutations
- AC-3.3: Undo/redo reversible for all commands

---

## 4. Markdown Diagnostics Specification

### 4.1 Link Validation

**Test Suite: markdown_diagnostics_links_spec.spl**

```
describe "MarkdownDiagnostics link validation":
  it "detects broken reference links":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("[text][undefined_ref]").parse()
    var warnings = diag.validate_links(ast)
    expect(warnings.len()).to_equal(1)
    expect(warnings[0].type).to_equal(DiagnosticType.BrokenLink)

  it "validates http(s) URLs":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("[link](https://example.com)").parse()
    var warnings = diag.validate_links(ast)
    expect(warnings.len()).to_equal(0)

  it "detects malformed URLs":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("[link](not a url)").parse()
    var warnings = diag.validate_links(ast)
    expect(warnings.len()).to_be_greater_than(0)

  it "validates relative file paths":
    var diag = MarkdownDiagnostics.new(workspace_root: "/project")
    var ast = MarkdownParser.new("[link](./README.md)").parse()
    var warnings = diag.validate_links(ast)
    # Should resolve path and check existence
    expect(warnings.len()).to_be_less_than(2)  # 0 if exists, 1 if missing
```

### 4.2 Heading Outline Consistency

**Test Suite: markdown_diagnostics_outline_spec.spl**

```
describe "MarkdownDiagnostics heading outline":
  it "detects skipped heading levels":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("# H1\n### H3 (skip H2)").parse()
    var warnings = diag.validate_heading_outline(ast)
    expect(warnings.len()).to_equal(1)
    expect(warnings[0].type).to_equal(DiagnosticType.HeadingLevelSkip)

  it "allows h1->h2->h3 progression":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("# H1\n## H2\n### H3").parse()
    var warnings = diag.validate_heading_outline(ast)
    expect(warnings.len()).to_equal(0)

  it "detects multiple h1 headings":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("# H1\n# Another H1").parse()
    var warnings = diag.validate_heading_outline(ast)
    expect(warnings.len()).to_equal(1)
    expect(warnings[0].type).to_equal(DiagnosticType.MultipleH1)
```

### 4.3 Code Fence Language Validation

**Test Suite: markdown_diagnostics_code_fence_spec.spl**

```
describe "MarkdownDiagnostics code fence language":
  it "validates known language identifiers":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("```rust\nfn main() {}\n```").parse()
    var warnings = diag.validate_code_fences(ast)
    expect(warnings.len()).to_equal(0)

  it "warns on unknown language identifier":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("```unknownlang\ncode\n```").parse()
    var warnings = diag.validate_code_fences(ast)
    expect(warnings.len()).to_equal(1)
    expect(warnings[0].severity).to_equal(DiagnosticSeverity.Information)

  it "detects unclosed code blocks":
    var diag = MarkdownDiagnostics.new()
    var ast = MarkdownParser.new("```python\ncode\n(no closing backticks)").parse()
    var warnings = diag.validate_code_fences(ast)
    expect(warnings.len()).to_be_greater_than(0)
```

**Acceptance Criteria:**
- AC-4.1: Link validation catches broken references and malformed URLs
- AC-4.2: Heading outline enforces valid progression
- AC-4.3: Code fence language identifiers validated against known list
- AC-4.4: Diagnostics mapped to source location (line, column, end)

---

## 5. Preview Pane Integration Specification

### 5.1 Sync Latency & Correctness

**Test Suite: markdown_preview_pane_spec.spl**

```
describe "MarkdownPreviewPane sync":
  it "renders initial document on open":
    var editor = MarkdownEditor.new("# Heading\n\nParagraph")
    var preview = MarkdownPreviewPane.new(editor)
    preview.open()
    expect(preview.rendered_text).to_contain("Heading")
    expect(preview.rendered_text).to_contain("Paragraph")

  it "updates preview after text insertion (latency <100ms)":
    var editor = MarkdownEditor.new("# Old")
    var preview = MarkdownPreviewPane.new(editor)
    preview.open()
    
    var start_time = now()
    editor.insert_text(" Title")
    preview.sync()  # Should trigger diff-based update
    var elapsed = now() - start_time
    
    expect(elapsed).to_be_less_than(100)  # milliseconds
    expect(preview.rendered_text).to_contain("Old Title")

  it "debounces rapid edits (batches into one render)":
    var editor = MarkdownEditor.new("text")
    var preview = MarkdownPreviewPane.new(editor)
    var render_count = 0
    preview.on_render = lambda: { render_count = render_count + 1 }
    
    preview.open()
    for i in 1..10:
      editor.insert_text("a")
    # Should only render ~2 times (initial + batched update), not 10
    expect(render_count).to_be_less_than(5)

  it "preserves scroll position on sync":
    var editor = MarkdownEditor.new("# H1\n\n" + ("Para\n" * 100))
    var preview = MarkdownPreviewPane.new(editor)
    preview.open()
    preview.scroll_to(position: 2000)
    var before_scroll = preview.scroll_position
    
    editor.insert_text("text")
    preview.sync()
    
    # Scroll position should remain close to original
    expect((preview.scroll_position - before_scroll).abs()).to_be_less_than(50)

  it "renders with correct ANSI colors (TUI)":
    var editor = MarkdownEditor.new("**bold text**")
    var preview = MarkdownPreviewPane.new(editor, renderer: "tui")
    preview.open()
    expect(preview.rendered_text).to_contain("\x1b[1m")  # Bold ANSI code

  it "renders with correct styles (GUI)":
    var editor = MarkdownEditor.new("**bold text**")
    var preview = MarkdownPreviewPane.new(editor, renderer: "gui")
    preview.open()
    var elements = preview.gui_elements()
    expect(elements[0].font_weight).to_equal(700)
```

**Performance Targets:**
- Initial render: <200ms for typical document (10KB)
- Incremental update: <100ms after single edit
- Debounce window: 50-200ms (batches rapid edits)
- Frame rate: ≥60fps for smooth scrolling (TUI/GUI)

**Acceptance Criteria:**
- AC-5.1: Preview syncs with editor in <100ms
- AC-5.2: Scroll position preserved across renders
- AC-5.3: Renders correctly in TUI (ANSI) and GUI (SDL2)
- AC-5.4: No visual tearing or flicker

---

## 6. Performance & Stress Testing Specification

### 6.1 Large Document Handling

**Test Suite: markdown_stress_spec.spl (marked slow tests)**

```
describe "MarkdownParser stress tests":
  it "parses 10MB markdown document in <5 seconds":
    var large_doc = generate_markdown(size_mb: 10)  # ~100k lines
    var start = now()
    var parser = MarkdownParser.new(large_doc)
    var ast = parser.parse()
    var elapsed = now() - start
    
    expect(elapsed).to_be_less_than(5000)  # milliseconds
    expect(ast.len()).to_be_greater_than(0)

  it "incremental parse <50ms for single-line edit in 10MB doc":
    var large_doc = generate_markdown(size_mb: 10)
    var parser = MarkdownParser.new(large_doc)
    parser.parse()  # Warm up
    
    var start = now()
    parser.edit(position: 1000000, inserted: "new text", deleted: 0)
    parser.parse_incremental()
    var elapsed = now() - start
    
    expect(elapsed).to_be_less_than(50)

  it "memory usage stays <200MB for 10MB document":
    var large_doc = generate_markdown(size_mb: 10)
    var parser = MarkdownParser.new(large_doc)
    
    var mem_before = system_memory_used()
    var ast = parser.parse()
    var mem_after = system_memory_used()
    var mem_delta = mem_after - mem_before
    
    expect(mem_delta).to_be_less_than(200 * 1024 * 1024)  # 200MB

  it "render 10MB document in <200ms (TUI)":
    var large_doc = generate_markdown(size_mb: 10)
    var ast = MarkdownParser.new(large_doc).parse()
    var renderer = MarkdownTuiRenderer.new()
    
    var start = now()
    var output = renderer.render(ast)
    var elapsed = now() - start
    
    expect(elapsed).to_be_less_than(200)

  it "handles deeply nested structures (10+ levels)":
    var nested_doc = ""
    for i in 1..10:
      nested_doc = "> " + nested_doc + "\nQuote level " + i.to_string()
    
    var parser = MarkdownParser.new(nested_doc)
    var ast = parser.parse()
    
    expect(ast[0].children.len()).to_be_greater_than(5)
```

**Acceptance Criteria:**
- AC-6.1: Parser handles 10MB files in <5s
- AC-6.2: Incremental updates <50ms for typical edits
- AC-6.3: Memory usage capped at 200MB
- AC-6.4: Render latency <200ms even for large documents
- AC-6.5: No out-of-memory crashes, graceful degradation

---

## 7. Cross-Platform Validation Specification

### 7.1 Platform Equivalence

**Test Suite: markdown_cross_platform_spec.spl (integration tests)**

```
describe "MarkdownEditor cross-platform validation":
  it "produces identical AST on macOS and Linux":
    var doc = load_test_document("sample.md")
    
    var ast_macos = MarkdownParser.new(doc).parse()  // Run on macOS
    var ast_linux = MarkdownParser.new(doc).parse()  // Run on Linux
    
    expect(ast_macos).to_equal(ast_linux)

  it "TUI renderer produces compatible ANSI on all platforms":
    var doc = "**bold** *italic* `code`"
    var renderer = MarkdownTuiRenderer.new()
    
    var output_macos = renderer.render(doc)      // Run on macOS
    var output_linux = renderer.render(doc)      // Run on Linux
    var output_windows = renderer.render(doc)    // Run on Windows
    
    # All should contain ANSI codes
    expect(output_macos).to_contain("\x1b[")
    expect(output_linux).to_contain("\x1b[")
    expect(output_windows).to_contain("\x1b[")

  it "file path resolution works on all platforms":
    var doc = "![img](./assets/image.png)"
    var diag = MarkdownDiagnostics.new(workspace_root: "/project")
    
    var warnings_macos = diag.validate_links(ast)    // /project/assets/image.png
    var warnings_linux = diag.validate_links(ast)    // /project/assets/image.png
    var warnings_windows = diag.validate_links(ast)  // C:\project\assets\image.png
    
    # All should resolve paths correctly without errors
    expect(warnings_macos.len()).to_equal(warnings_linux.len())
    expect(warnings_windows.len()).to_equal(warnings_macos.len())
```

**Acceptance Criteria:**
- AC-7.1: Parser produces identical AST across platforms
- AC-7.2: Renderer output is visually equivalent (within 5% pixel accuracy for GUI)
- AC-7.3: File path resolution works with platform-specific separators
- AC-7.4: Unicode handling consistent across macOS, Linux, Windows

---

## Test Execution Matrix

| Test Suite | Tests | Expected Pass | Category | Platform |
|------------|-------|---------------|----------|----------|
| markdown_lexer_spec.spl | 10 | 10 | Lexer | All |
| markdown_parser_spec.spl | 8 | 8 | Parser | All |
| markdown_incremental_parser_spec.spl | 6 | 6 | Incremental | All |
| markdown_tui_renderer_spec.spl | 9 | 9 | TUI Render | TUI |
| markdown_gui_renderer_spec.spl | 7 | 7 | GUI Render | GUI |
| markdown_lsp_renderer_spec.spl | 3 | 3 | LSP Render | LSP |
| markdown_commands_spec.spl | 16 | 16 | Commands | All |
| markdown_diagnostics_links_spec.spl | 4 | 4 | Diagnostics | All |
| markdown_diagnostics_outline_spec.spl | 3 | 3 | Diagnostics | All |
| markdown_diagnostics_code_fence_spec.spl | 3 | 3 | Diagnostics | All |
| markdown_preview_pane_spec.spl | 6 | 6 | Preview | TUI/GUI |
| markdown_stress_spec.spl | 5 | 5 | Stress | All |
| markdown_cross_platform_spec.spl | 3 | 3 | Integration | All/macOS/Linux/Windows |
| **Total** | **83** | **83** | | |

---

## Integration Test Cases

1. **Full Editor Flow:**
   - Create new markdown file → Insert text → Preview pane syncs → Save → Reopen → AST reconstructs correctly

2. **Command Palette Integration:**
   - Open palette → Filter by "bold" → Execute "Toggle Bold" → Undo → Redo → Selection updated

3. **LSP Integration:**
   - Open editor → Type markdown → Diagnostics appear in status bar → Hover shows tooltip → Completions available

4. **Multi-File Scenario:**
   - Edit file A (links to file B) → File B missing → Diagnostic shown → Create file B → Diagnostic cleared

5. **Performance Under Load:**
   - Open 10MB document → Scroll → Edits → Preview pane keeps up → No lag/stutter

---

## Acceptance Criteria Summary

| AC# | Criterion | Phase | Status |
|-----|-----------|-------|--------|
| AC-1.1 | Lexer recognizes all token types | 5 | ⬜ Pending |
| AC-1.2 | Parser builds correct AST | 5 | ⬜ Pending |
| AC-1.3 | 95%+ CommonMark compliance | 5 | ⬜ Pending |
| AC-1.4 | Incremental parser <50ms | 5 | ⬜ Pending |
| AC-1.5 | InlineNode nesting correct | 5 | ⬜ Pending |
| AC-1.6 | Minimal change scope detection | 5 | ⬜ Pending |
| AC-1.7 | Edit-to-AST <50ms | 5 | ⬜ Pending |
| AC-2.1 | TUI renders all block types | 5 | ⬜ Pending |
| AC-2.2 | ANSI codes applied correctly | 5 | ⬜ Pending |
| AC-2.3 | Terminal constraints respected | 5 | ⬜ Pending |
| AC-2.4 | GUI produces layoutable elements | 5 | ⬜ Pending |
| AC-2.5 | Cross-platform within 5% accuracy | 7 | ⬜ Pending |
| AC-2.6 | Image/link resolution | 5 | ⬜ Pending |
| AC-2.7 | Hover info for all blocks | 5 | ⬜ Pending |
| AC-2.8 | Diagnostics mapped to location | 5 | ⬜ Pending |
| AC-2.9 | Completions available | 5 | ⬜ Pending |
| AC-3.1 | 50+ commands implemented | 5 | ⬜ Pending |
| AC-3.2 | Command execution correct | 5 | ⬜ Pending |
| AC-3.3 | Commands reversible (undo/redo) | 5 | ⬜ Pending |
| AC-4.1 | Link validation working | 5 | ⬜ Pending |
| AC-4.2 | Heading outline validation | 5 | ⬜ Pending |
| AC-4.3 | Code fence language validation | 5 | ⬜ Pending |
| AC-4.4 | Diagnostics mapped to source | 5 | ⬜ Pending |
| AC-5.1 | Preview syncs <100ms | 5 | ⬜ Pending |
| AC-5.2 | Scroll position preserved | 5 | ⬜ Pending |
| AC-5.3 | Renders TUI/GUI correctly | 5 | ⬜ Pending |
| AC-5.4 | No tearing/flicker | 5 | ⬜ Pending |
| AC-6.1 | 10MB parse <5s | 5 | ⬜ Pending |
| AC-6.2 | Incremental <50ms | 5 | ⬜ Pending |
| AC-6.3 | Memory <200MB | 5 | ⬜ Pending |
| AC-6.4 | Render <200ms | 5 | ⬜ Pending |
| AC-6.5 | Graceful degradation (no OOM crash) | 5 | ⬜ Pending |
| AC-7.1 | Cross-platform AST equivalence | 7 | ⬜ Pending |
| AC-7.2 | Cross-platform render equivalence | 7 | ⬜ Pending |
| AC-7.3 | Path resolution all platforms | 5 | ⬜ Pending |
| AC-7.4 | Unicode consistent all platforms | 5 | ⬜ Pending |

---

## Phase 4 Summary

This specification translates Phase 3 architectural contracts into 83 concrete test cases organized across 13 test suites, covering:

- **Parser Layer (Layer 10):** Lexer, block/inline AST, incremental updates, CommonMark compliance
- **Semantic Layer (Layer 35):** Diagnostics (links, outline, code fences)
- **Backend Layer (Layer 70):** Multi-renderer (TUI, GUI, LSP)
- **Tools Layer (Layer 90):** Command palette, editor integration

**Key Quality Gates:**
- Parser performance: <5s for 10MB, <50ms incremental
- Preview sync: <100ms edit-to-render
- Memory: <200MB for large documents
- Command coverage: 50+ discoverable commands
- Diagnostics: Full link/outline/code fence validation
- Cross-platform: macOS, Linux, Windows equivalence

**Next Step:** Phase 5 (Engineer) implements these specifications using this test matrix as the acceptance criteria.

---

## Appendix A: Test Data Generators

```
fun generate_markdown(size_mb: Int) -> Text:
  var doc = "# Large Document\n\n"
  var target_bytes = size_mb * 1024 * 1024
  while doc.len() < target_bytes:
    doc = doc + "## Section\n\nParagraph with content.\n\n- List item\n\n"
  return doc.substring(0, target_bytes)

fun load_test_document(name: Text) -> Text:
  # Load from test/fixtures/markdown/{name}
  return read_file("/test/fixtures/markdown/" + name)
```

---

**Document ID:** phase-4-markdown-editor-spec  
**Version:** 1.0  
**Author:** QA Lead (Spec Agent)  
**Last Updated:** 2026-05-11  
**Next Phase:** Phase 5 (Engineer Implementation)

