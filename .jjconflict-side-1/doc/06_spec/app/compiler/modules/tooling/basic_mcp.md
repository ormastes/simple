# Model Context Preview (MCP-MCP) Specification

**Version:** 1.0
**Status:** Draft
**Last Updated:** 2025-12-25

**Target Language:** Simple (colon + indentation)
**Outline Notation:** Block-mark (LLM-first, collapsed by default)

## Overview

MCP-MCP (Model Context Preview) provides a compact, navigable, LLM-friendly representation of Simple codebases. It reduces token usage by 90%+ while preserving semantic information, making it ideal for AI-assisted development and code review.

**Note:** MCP-MCP is distinct from "Model Context Protocol" (Anthropic's MCP), which is a protocol for connecting AI assistants to external data sources.

**Key Benefits:**
- **Token Efficiency:** Default view shows only public API outlines
- **On-Demand Detail:** Expand signatures, bodies, docs, traits, tests via MCP-MCP tools
- **Virtual Information:** Expose implicit traits, AOP pointcuts, coverage, diagnostics explicitly
- **LLM-Optimized:** Single JSON text field format minimizes token overhead

**Related Features:**
- [#890-893: Context Pack Generator](../features/feature.md) - Minimal symbol extraction
- [#885-889: AST/IR Export](../features/feature.md) - Machine-readable output
- [LLM-Friendly Development Guide](../guides/llm_friendly.md) - Best practices

---

## 1. Design Principles

### 1.1 Token Minimization

- **Default:** Public API outline only (`pub` symbols)
- **Collapsed:** Bodies shown as `{ … }` inline
- **No Noise:** No UI hints like `[expand]`, `(click)`, etc.
- **Single Field:** JSON with one `text` field (no per-line arrays)

### 1.2 Semantic Preservation

- **Code Column:** Simple-like syntax (colon + indentation when expanded)
- **Block Marks:** Left-margin ASCII markers (`C>`, `F>`, `T>`, `P>`, `V•`)
- **Virtual Info:** Implicit traits, AOP pointcuts, coverage made explicit

### 1.3 Progressive Disclosure

- **Outline First:** Names and signatures
- **Expand on Demand:** Via MCP tool calls (not inline hints)
- **Context Aware:** Show only symbols referenced by target module

---

## 2. Output Format

### 2.1 Default JSON Structure (LLM Mode)

**Format:**
```json
{
  "text": "<mcp_collapsed_text_block>"
}
```

**Properties:**
- Exactly one string containing the whole collapsed preview
- No per-line arrays (token efficiency)
- No metadata by default

**Example:**
```json
{
  "text": "C> pub class UserService { … }\nF> pub fn get_user { … }\nF> pub fn create_user { … }\nV• auto impls: Send, Sync"
}
```

### 2.2 Optional Metadata (Non-Default)

```json
{
  "text": "...",
  "meta": {
    "mode": "mcp",
    "line_numbers": "plain|zpad",
    "show_coverage": false,
    "show_block_guides": false
  }
}
```

**Metadata Fields:**
- `mode`: Always `"mcp"`
- `line_numbers`: `"plain"` (no padding) | `"zpad"` (zero-padded)
- `show_coverage`: `false` (default) | `true` (show `V•` coverage overlays)
- `show_block_guides`: `false` (default) | `true` (show `V• end` markers)

---

## 3. Text Block Format

### 3.1 Line Structure

```
<block_mark> <simple_like_code>
```

**Block Marks (Leftmost Column, ASCII):**

| Mark | Meaning | Expanded Form |
|------|---------|---------------|
| `C>` | Class/struct (collapsed) | `C▼` (expanded) |
| `F>` | Function/method (collapsed) | `F▼` (expanded) |
| `T>` | Trait (collapsed) | `T▼` (expanded) |
| `P>` | AOP pointcut (collapsed) | `P▼` (expanded) |
| `V•` | Virtual information (non-source) | N/A (always visible) |

### 3.2 Code Column Syntax

- **Collapsed:** Simple-like with inline `{ … }` for bodies
- **Expanded:** Full Simple syntax (colon + indentation)
- **Consistency:** Same grammar as Simple source when expanded

**Example (Collapsed):**
```
C> pub class User { … }
F> pub fn login(name: String) -> bool { … }
```

**Example (Expanded):**
```
C▼ pub class User:
    name: String
    age: i64

F▼ pub fn login(name: String) -> bool:
    # Implementation
    return true
```

---

## 4. Folding and Shrinking Rules

### 4.1 Default View (Public API Only)

**Show:**
- `pub class`, `pub struct`, `pub trait`, `pub fn`
- Public method signatures (name + params + return type)

**Hide:**
- Private symbols
- Function/method bodies (show as `{ … }`)
- Member field types (show names only)
- Attributes/decorators

**Example:**
```
C> pub class UserService { … }
F> pub fn get_user { … }
F> pub fn create_user { … }
V• members: repo, cache
V• pub methods: get_user, create_user, delete_user
```

### 4.2 Class/Struct Member Shrinking

**Collapsed View:**
- Field names only (types optional)
- Methods: signature or name only
- Attributes/decorators hidden
- Long generics elided (`User<T, …>`)

**Optional Virtual Summaries:**
```
V• members: repo, cache
V• pub methods: get_user, create_user, delete_user
V• traits: Display, Debug
```

### 4.3 Function Signature Shrinking

**Collapsed (Default):**
```
F> fn login { … }
```

**Expanded (On Demand):**
```
F▼ fn login(name: String, password: String) -> Result<User, AuthError>:
    # Implementation
    …
```

### 4.4 No Inline Expand Hints

**Forbidden:**
- `[expand]`, `(click to expand)`, `⊕`, `▶`, etc.

**Correct:**
- Expansion driven solely by MCP tool calls
- Client UI may add visual affordances (not part of MCP text)

---

## 5. Virtual Information (V• Lines)

### 5.1 Implicit Traits

**Collapsed:**
```
T> trait Injectable { … }
```

**Expanded:**
```
T▼ trait Injectable:
    provides: ctor_injection(self.repo)
    requires: container binding for IUserRepo
```

### 5.2 AOP Pointcuts

**Collapsed:**
```
P> pointcut logging @ UserService.*
```

**Expanded:**
```
P▼ pointcut logging @ UserService.*:
    before: all
    after: all
```

**Note:** Pointcuts appear once per class (not per method)

### 5.3 Coverage Overlays (Optional)

```
V• coverage: 83% (lines), 71% (branches)
```

**When to Show:**
- Only if `meta.show_coverage = true`
- Aggregated per class/module
- No per-line coverage by default

### 5.4 Block Guides (Optional)

```
F▼ fn login(name: String) -> bool:
    …
V• end fn login

C▼ pub class UserService:
    …
V• end class UserService
```

**When to Show:**
- Only if `meta.show_block_guides = true`
- Helps with indentation-based syntax
- Not shown by default (redundant for collapsed view)

---

## 6. Markdown Document Folding

### 6.1 Heading-Based Folding

**Markdown Headings as Foldable Blocks:**
```
# Language Basics
## Functions { … }
## Classes { … }
```

**Collapsed by Default:**
- Section bodies under headings are shrinked
- Heading hierarchy preserved

**Example:**
```
# Simple Language Reference
## 1. Types { … }
## 2. Functions { … }
## 3. Classes { … }
```

---

## 7. Logs and Diagnostics

### 7.1 Collapsible Log Groups

**Default View:**
```
V• task: simple compile app.spl
V• INFO x18
V• WARN x2
V• ERROR x1
```

**Expanded Error Group:**
```
V• task: simple compile app.spl
V• ERROR src/app/user_service.spl:44
    type mismatch: expected i64, got i32

    suggestion: add explicit cast `.as_i64()`
```

### 7.2 Log Level Filtering

- **Default:** Show counts only
- **Expand:** Show full messages for WARN/ERROR
- **Filter:** Client can request specific levels via tool calls

---

## 8. MCP Tool API (Behavioral)

### 8.1 Core Tools

```
read_file(path: str, mode: "mcp") -> { text: str }
```
- Returns collapsed MCP text for file
- Default mode is `"mcp"`

```
expand_at(path: str, selector: str | line: int, what: "body" | "signature" | "docs" | "all") -> { text: str }
```
- `selector`: Symbol name (e.g., `"UserService"`, `"login"`)
- `line`: Line number in original source
- `what`: What to expand
- Returns expanded MCP text for symbol

```
goto_definition(symbol: str) -> { text: str, location: {...} }
```
- Returns MCP text and location for symbol definition

```
search(query: str, filter: "public" | "all") -> { matches: [...] }
```
- Search across codebase
- `filter="public"`: Only public symbols (default)

### 8.2 Task Tools

```
run_compile(target: str, flags: [...]) -> { task_id: str }
```
- Start compilation task
- Returns task ID for monitoring

```
read_task_log(task_id: str, group: "INFO" | "WARN" | "ERROR") -> { text: str }
```
- Read log group from task
- Returns collapsed log (counts only) or expanded (full messages)

---

## 9. Example: Default MCP Read

### 9.1 Source Code (Simple)

```simple
pub class User:
    name: String
    age: Int

    pub fn login(name: String) -> bool:
        # Implementation
        return true

trait Display:
    fn show() -> String

pointcut logging @ User.login
```

### 9.2 MCP Output (JSON)

```json
{
  "text": "C> pub class User { … }\nF> pub fn login(name: String) -> bool { … }\nT> trait Display { … }\nP> pointcut logging @ User.login\nV• auto traits: Send, Sync"
}
```

### 9.3 Expanded Class (On Demand)

**Tool Call:**
```
expand_at(path="user.spl", selector="User", what="all")
```

**Response:**
```json
{
  "text": "C▼ pub class User:\n    name: String\n    age: Int\n\n    pub fn login(name: String) -> bool { … }\n\nV• auto traits: Send, Sync\nV• methods: 1 public, 0 private"
}
```

---

## 10. Implementation Notes

### 10.1 For Compiler Authors

- **Block-Mark Layer:** MCP is an outline format over Simple grammar
- **Expansion:** Simple syntax applies when expanded (colon + indentation)
- **Virtual Facts:** Keep minimal and non-redundant
- **Ellipsis:** Always inline on same line as block header

### 10.2 For Tool Authors

- **Default JSON:** Single `text` field for LLM consumption
- **Expansion:** Use `expand_at()` tool calls, not inline hints
- **Context Packs:** Combine MCP with dependency analysis for minimal context
- **Caching:** MCP views are deterministic and cacheable

### 10.3 For LLM Integration

- **Token Reduction:** 90%+ reduction vs. full source
- **Semantic Search:** Use `search()` with `filter="public"`
- **Progressive Detail:** Start with outline, expand only what's needed
- **Error Context:** Use expanded logs for diagnostics

---

## 11. Formal Grammar (EBNF)

### 11.1 MCP Text Block

```ebnf
mcp_file       ::= mcp_line*
mcp_line       ::= block_mark " " code_text "\n"
block_mark     ::= "C>" | "C▼" | "F>" | "F▼" | "T>" | "T▼" | "P>" | "P▼" | "V•"
code_text      ::= simple_syntax | collapsed_block
collapsed_block ::= identifier " { … }"
```

### 11.2 JSON Schema

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "type": "object",
  "properties": {
    "text": { "type": "string", "description": "MCP collapsed text block" },
    "meta": {
      "type": "object",
      "properties": {
        "mode": { "const": "mcp" },
        "line_numbers": { "enum": ["plain", "zpad"] },
        "show_coverage": { "type": "boolean" },
        "show_block_guides": { "type": "boolean" }
      }
    }
  },
  "required": ["text"]
}
```

---

## 12. Comparison with Alternatives

| Feature | MCP | LSP Symbols | Tree-sitter | Full Source |
|---------|-----|-------------|-------------|-------------|
| Token Count | 10% | 30% | 50% | 100% |
| Semantic Info | ✅ | ✅ | ✅ | ✅ |
| Virtual Facts | ✅ | ❌ | ❌ | ❌ |
| LLM-Optimized | ✅ | ❌ | ❌ | ❌ |
| Expandable | ✅ | ❌ | ❌ | N/A |
| Single Field JSON | ✅ | ❌ | ❌ | ❌ |

---

## 13. Future Extensions

### 13.1 Planned

- **Diff Mode:** Show only changed symbols (`± prefix`)
- **Blame Integration:** Attach author/commit info to symbols
- **Cross-References:** Show call sites, implementations inline

### 13.2 Considered

- **Binary Format:** Protobuf for faster parsing
- **Streaming:** Incremental MCP for large files
- **Semantic Highlighting:** Inline syntax token types

---

## Appendix A: CLI Integration

### A.1 Simple Compiler Flags

```bash
# Generate MCP outline for file
simple mcp app.spl

# Generate MCP with coverage overlay
simple mcp app.spl --show-coverage

# Generate MCP with metadata
simple mcp app.spl --format=json-meta

# Expand specific symbol
simple mcp app.spl --expand UserService --what=all
```

### A.2 Context Pack Integration

```bash
# Extract minimal context (MCP + dependencies)
simple context app.service --format=mcp > context.json

# Impact: 90% token reduction vs. full source
```

---

## Appendix B: References

**Simple Language Specifications:**
- [Language Spec](language.md) - Core syntax and semantics
- [Module System](modules.md) - Import/export rules
- [AOP Spec](../research/aop.md) - Pointcut grammar

**LLM-Friendly Features:**
- [LLM Development Guide](../guides/llm_friendly.md) - Best practices
- [Context Pack Generator (#890-893)](../features/feature.md) - Minimal symbol extraction
- [AST/IR Export (#885-889)](../features/feature.md) - Machine-readable formats

**Implementation Status:**
- Feature #1230: MCP Tooling - 📋 Planned (see feature.md)

---

## Changelog

**v1.0 (2025-12-22):**
- Initial specification
- LLM-optimized JSON format
- Block-mark notation
- Virtual information support
- Tool API definitions
