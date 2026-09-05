# SPipe MCP (spipe-mcp) Design & Architecture

**Date:** 2026-07-01  
**Domain:** infra/tooling  
**Status:** Executive Decision & Design Spec  
**Keywords:** MCP, language-neutral context, log parsing, tree rendering, minimality gate

## Executive Summary

**spipe-mcp** is a new MCP server to be implemented in **Simple Language** (not JavaScript/Node). It fills a language-neutral role between external codebase packing (codebase-mcp), Simple-specific actions (simple-mcp), and language semantics (simple-lsp-mcp).

**Core responsibility:** Store, parse, tree-structure, and retrieve command output, logs, file hierarchies, and codebase snapshots in a unified tree model. Implement Ponytail minimality checks as a gate. Normalize hook events across Claude, Codex, Gemini, and others.

**Implementation location:**
```
src/app/spipe_mcp/main.spl
src/lib/nogc_sync_mut/spipe/*.spl
bin/spipe_mcp_server (compiled binary)
```

## Role Split: Three MCP Servers

| Server | Role | Best For | Not Best For |
|--------|------|----------|-------------|
| **codebase-mcp** | External RepoMix packer | Remote GitHub repo snapshot, broad file pack, saved codebase dump | Simple-specific build/check/test/LSP/semantic actions |
| **simple-mcp** | Simple project action server | Build, check, test, lint, VCS, Simple repo operations | Language-neutral context/log parsing, remote repo packing |
| **simple-lsp-mcp** | Simple language semantic server | Diagnostics, hover, definition, references, completion for .spl/.shs | Non-Simple files, cross-language contexts |
| **spipe-mcp** | Language-neutral context/tree/hook layer | Parsing command output, storing context, tree-aware retrieval, RepoMix ingestion, Ponytail minimality checks, hook normalization | Simple-specific compiler diagnostics or LSP semantics |

## What Moves into spipe-mcp

### Language-Neutral Features

1. Context storage and retrieval (context-mode-like)
2. Command output parsing
3. Log-level detection and grouping
4. File/dir tree parsing and rendering
5. RepoMix/codebase-mcp packed-output ingestion
6. Raw original-text retrieval
7. Common tree rendering format
8. Hook event normalization (Claude, Codex, Gemini, etc.)
9. Ponytail minimality gate implementation
10. Parser registry for standard CLI outputs (Ubuntu, Linux toolchain)

### Stays Outside spipe-mcp

1. .spl/.shs parser/compiler diagnostics
2. Simple LSP symbol semantics
3. Simple build/check/test command semantics
4. Simple runtime-family rules
5. Simple-specific VCS/build/test wrappers

**Design principle:** spipe-mcp is reusable and **never** becomes a second simple-mcp.

## Log-Level Design

### Rule

Log level should be shown only if the parser actually detects a log level. **Never invent INFO for tools that do not emit levels.**

```
if any node has explicit level:
    group by level first
    then tree/file/path/function
    put unlevelled lines in level=none
else:
    skip level grouping
    render normal tree/path order
    show header: level_detected=false
```

### Canonical Fields

Each parsed node stores both normalized and original level:

```
level_norm: TRACE | DEBUG | INFO | WARN | ERROR | FATAL | NONE
level_raw: original text token (e.g., "[ERR]", "warning:", "E", "ERROR")
level_confidence: exact | parser | heuristic | none
level_present: true | false
```

**Confidence levels:**
- `level_confidence=exact/parser` → allowed to group as real level
- `level_confidence=heuristic` → do not group by default; expose as hint only
- `level_confidence=none` → no level detected

**Example:** A line containing the word "error" in normal prose remains unlevelled unless the parser knows the tool's format.

### Conservative Log Regex

Only use these patterns for parser-level signals on **known** compiler/build/test outputs:

```
^\s*(TRACE|DEBUG|INFO|WARN|WARNING|ERROR|ERR|FATAL)\b
^\s*\[(TRACE|DEBUG|INFO|WARN|WARNING|ERROR|ERR|FATAL)\]
^\s*(E|W|I|D|T)\d{4}\s
^\s*error:
^\s*warning:
```

Mark `error:` and `warning:` as `parser` confidence for compilers; use `heuristic` elsewhere.

## Tree Format (Canonical)

Compact, self-contained, good for partial context:

```
@ctx v=1 query="build failed" render=tree-log order="level,tree,rank"
@source id=exec:7 cmd="simple build" level_detected=true raw_available=true

@group level=ERROR count=2
@parent d=0 kind=command text="simple build"
@parent d=1 kind=dir path="src/app/mcp"
@parent d=2 kind=file path="src/app/mcp/main.spl"
@node id=n912 d=3 kind=log level=ERROR level_raw="[ERROR]" conf=exact lines=441-443 raw=raw:exec:7#L441-L443
| [ERROR] src/app/mcp/main.spl:441: undefined symbol dispatch_tool
|   response = dispatch_tool(id, tool_name, args_raw)

@group level=WARN count=1
@parent d=0 kind=command text="simple build"
@parent d=1 kind=dir path="src/lib/nogc_sync_mut/spipe"
@node id=n913 d=2 kind=log level=WARN level_raw="warning:" conf=parser lines=88-88 raw=raw:exec:7#L88-L88
| warning: parser fallback used for command output

@more raw=raw:exec:7 lines=all
```

**Design rationale:**
- Tabs: readable but token-wasteful and fragile
- `> / <` open-close: compact but bad when retrieval starts mid-tree
- Depth-numbered `@parent/@node`: compact, self-contained, reconstructible, good for partial context

The model sees severity first, then parent chain, then exact lines with raw pointers.

## Core Data Model

### TreeNode

Single tree node model for logs, file trees, RepoMix output, diffs, CLI output, Markdown, and code symbols:

```
TreeNode
  id: text
  source_id: text
  parent_id: text
  kind: repo | dir | file | heading | symbol | function | class |
        log | diagnostic | command | section | test | diff | hunk | line
  name: text
  path: text
  depth: i64
  start_line: i64
  end_line: i64
  start_byte: i64
  end_byte: i64
  level_norm: text
  level_raw: text
  level_present: bool
  level_confidence: text
  text: text
  summary: text
  attrs_sdn: text  # SDN-encoded attributes
```

### SourceBlob

Store original text separately, with full provenance:

```
SourceBlob
  id: text
  kind: command_output | file | repomix | diff | markdown | log
  uri: text
  command: text
  cwd: text
  created_at: text
  sha256: text
  raw_text: text
```

### Indexing

- Node text (full-text search)
- Node path (trie/prefix)
- Node summary (semantic)
- Parent chain text (hierarchical)
- Raw line ranges (exact retrieval)
- Severity fields (filtering)

## Parser Registry

Do not hand-write parsers for every Ubuntu CLI tool first. Use a registry with safe fallback.

```
Parser
  name: text
  accepts(source_kind, command, text) -> score: f64
  parse(source: SourceBlob) -> TreeDoc
```

### Initial Parsers

Generic:
- `generic_text`: fallback, preserves all raw
- `generic_log_level`: conservative level detection
- `file_tree`: directory/file hierarchies

CLI tools:
- `find`, `ls`, `tree`, `rg`, `grep`
- `git_status`, `git_diff`, `git_log`
- `gcc_clang`, `ld_linker`, `cmake`, `ninja`, `make`
- `pytest`, `ctest`, `cargo`, `npm`
- `journalctl`, `systemctl`
- `repomix_markdown`, `repomix_xml`
- `markdown_headings`

### Fallback Behavior

`generic_text`:
- Split into sections
- Detect paths if obvious
- Detect explicit log levels only with conservative regex
- Preserve all raw line pointers

## Original Text Retrieval

Every rendered node includes a raw pointer:

```
raw=raw:<source_id>#L<start>-L<end>
```

Add MCP tool `spipe_context_raw`:

**Input:**
```json
{
  "raw": "raw:exec:9#L98-L105",
  "contextBefore": 3,
  "contextAfter": 3,
  "mode": "exact"
}
```

**Output:**
```
@raw id=exec:9 range=L95-L108 mode=exact
| [39/55] Compiling ...
| [42/55] Linking simple_mcp_server
| collect2: ld returned 1 exit status
| error: undefined reference to `spipe_context_search`
| ...
```

**Modes:**
- `mode=exact`: original lines only, no reformatting, preserve whitespace
- `mode=parsed`: parsed node plus parent chain
- `mode=both`: parent chain + exact original text

This is the **safety valve** for parser mistakes. If spipe-mcp parsed incorrectly, the LLM calls `spipe_context_raw` and inspects the source.

## Common API Surface

### Core Tools

**Context:**
- `spipe_context_put` — store context blob
- `spipe_context_search` — BM25/vector search
- `spipe_context_get` — retrieve by ID
- `spipe_context_raw` — original text with context

**Tree:**
- `spipe_tree_parse` — parse source into tree
- `spipe_tree_render` — render tree to compact format
- `spipe_tree_match_parser` — scorer for best parser
- `spipe_tree_parser_list` — list available parsers

**Execution:**
- `spipe_exec_capture` — capture command output
- `spipe_exec_parse` — parse execution result
- `spipe_exec_search` — search across executions

**Codebase:**
- `spipe_codebase_pack_local` — local RepoMix equivalent
- `spipe_codebase_pack_remote` — remote GitHub RepoMix
- `spipe_codebase_ingest` — parse packed output into context
- `spipe_codebase_search` — search indexed codebase
- `spipe_codebase_get` — retrieve file/section
- `spipe_codebase_save` — save packed output

**Hooks:**
- `spipe_hook_event` — normalize hook event
- `spipe_hook_rules` — list active hook rules
- `spipe_hook_render` — render hook audit trail

**Minimality:**
- `spipe_minimality_check` — run Ponytail gate
- `spipe_minimality_review` — detailed review
- `spipe_minimality_debt` — accumulated debt tracking

MCP clients discover tools via `tools/list` and invoke via `tools/call` (standard MCP protocol).

## Context Retrieval Algorithm

1. Store raw source exactly
2. Match parser by source kind + command + text prefix
3. Parse into TreeDoc
4. Detect log levels conservatively
5. Index node text + parent chain + raw line pointer
6. Search by BM25/vector/keyword as available
7. Expand ancestors
8. Add nearby siblings only under token budget
9. Render selected nodes with parent chain
10. Include raw pointers for LLM original-text requests

### Default Ordering

**If levels detected:**
- FATAL, ERROR, WARN, INFO, DEBUG, TRACE, NONE/unlevelled

**If no levels:**
- Tree/path order

**Within each group:**
1. Direct query match score
2. Exact file/path match
3. Parent relevance
4. Line proximity

## Codebase-MCP Integration

codebase-mcp is useful but narrow. It wraps RepoMix, which packs a repo into AI-friendly format with file summaries, directory structure, include/exclude customization, token counting, and security checks.

**For spipe-mcp, do NOT return full RepoMix dumps to the model by default.** Instead:

1. Run RepoMix/codebase-mcp with focused include patterns
2. Store full packed output as SourceBlob
3. Parse RepoMix directory/file sections into TreeDoc
4. Index file summaries, file paths, symbols if available
5. Return only tree-aware retrieved slices
6. Allow raw retrieval by raw pointer

### Recommended Compatibility Tools

- `spipe_codebase_pack_remote` — equivalent of getRemoteCodebase (but safe)
- `spipe_codebase_pack_local` — equivalent of getCodebase
- `spipe_codebase_save` — equivalent of saveCodebase
- `spipe_codebase_ingest` — parse existing RepoMix/codebase-mcp output into context store

### Security Requirement

**Do not build shell command strings from untrusted MCP arguments.** codebase-mcp uses `execSync` with command strings and has known command-injection issues (NVD/GitHub Advisory).

In Simple, prefer argv-style process execution if available; otherwise strictly validate `repo`, `includePatterns`, `ignorePatterns`, and output paths before execution.

### Focused Simple Repo Ingest Profile

For Simple MCP work, use focused includes:

**Include:**
```
MCP.md, .mcp.json, config/mcp/**, src/app/mcp/**, src/app/simple_lsp_mcp/**,
src/lib/nogc_sync_mut/mcp_sdk/**, examples/10_tooling/minimal_mcp/**,
tools/mcp-registry/**, tools/lsp-mcp-registry/**, .codex/**, .claude/**,
.gemini/**
```

**Ignore:**
```
.git/**, .cache/**, target/**, release/**, var/**, gh-cli-cache/**, build/**
```

**Reason:** Simple is broad and large. A full dump is the wrong first move. For MCP integration, focus on MCP infrastructure only.

## Ponytail Minimality Gate

Implement as a real gate, **not just prompt copy**.

Ponytail's public rule ladder:
1. Does this task need to exist? (YAGNI)
2. Does stdlib do it?
3. Does the native platform feature cover it?
4. Does an installed dependency solve it?
5. Can it be one line?
6. Only then: minimal custom code

**Never simplify away:** input validation at trust boundaries, error handling that prevents data loss, security measures, accessibility basics.

Add these MCP tools:

- `spipe_minimality_check` — run gate, return decision
- `spipe_minimality_review` — detailed review with tagging
- `spipe_minimality_debt` — accumulated complexity tracking

Example output:

```
@minimality v=1 mode=full task="add date picker"
@decision rung=native
@reason browser has native date input
@replace
- custom DatePicker component
- date-picker dependency
+ <input type="date">
@guards keep
- form validation
- accessibility label
- server-side date parsing
@raw_context raw:diff:12#L40-L88
```

Review output mirrors Ponytail-review style with tags: `delete`, `stdlib`, `native`, `yagni`, `shrink`.

## Hook Normalization

Normalize hook events from different clients into one model:

```
HookEvent
  id: text
  client: claude | codex | gemini | cursor | generic
  phase: pre_prompt | pre_tool | post_tool | pre_edit | post_edit | pre_commit
  tool_name: text
  cwd: text
  repo: text
  files: [text]
  diff: text
  prompt_excerpt: text
  raw_payload: text
```

**Shared features:**

- `pre_prompt`: inject minimality/context policy
- `pre_tool`: validate command/output capture policy
- `post_tool`: parse output into TreeDoc, store raw, index context
- `post_edit`: run minimality_review, store diff tree
- `pre_commit`: render concise review tree

## Implementation Shape

### File Structure

```
bin/spipe_mcp_server              (compiled binary)
src/app/spipe_mcp/main.spl        (MCP entry point)

src/lib/nogc_sync_mut/spipe/
  tree_doc.spl                    (TreeNode + TreeDoc types)
  tree_parse.spl                  (parse SourceBlob into TreeDoc)
  tree_render.spl                 (render TreeDoc to compact format)
  context_store.spl               (storage + BM25/vector index)
  source_blob.spl                 (SourceBlob type + accessors)
  parser_registry.spl             (Parser type + registry)
  minimality.spl                  (Ponytail minimality gate)
  hook_event.spl                  (hook normalization)
  codebase_ingest.spl             (RepoMix/codebase-mcp integration)
  
  parsers/
    generic_text.spl
    generic_log_level.spl
    file_tree.spl
    cli_tools.spl                 (find, ls, tree, rg, grep, etc.)
    compiler_tools.spl            (gcc, clang, ld, cmake, ninja, make)
    vcs_tools.spl                 (git status, diff, log)
    test_tools.spl                (pytest, ctest)
    build_tools.spl               (cargo, npm)
    system_tools.spl              (journalctl, systemctl)
    repomix_parsers.spl           (markdown, xml formats)
```

### Entry Point Pattern

Follow existing Simple MCP server structure (simple-mcp at src/app/mcp/main.spl):

```spl
fn main() {
  let server = mcp_server_init("spipe-mcp")
  
  // Register tools
  mcp_server_tool(server, "spipe_context_put", spipe_context_put_schema, spipe_context_put_handler)
  mcp_server_tool(server, "spipe_context_search", spipe_context_search_schema, spipe_context_search_handler)
  // ... more tools
  
  // Register resources (optional)
  // Register logging level handler
  
  mcp_serve(server)  // stdio loop
}
```

## MCP Configuration

Final practical setup for `.mcp.json`:

```json
{
  "mcpServers": {
    "codebase-mcp": {
      "command": "node",
      "args": ["/absolute/path/to/codebase-mcp/dist/tools/codebase.js"]
    },
    "simple-mcp": {
      "command": "/bin/sh",
      "args": [
        "-lc",
        "cd '/absolute/path/to/simple' && exec node 'bin/mcp_stdio_bridge.js' -- 'bin/simple' run 'src/app/mcp/main.spl'"
      ],
      "env": {
        "SIMPLE_LOG": "error",
        "RUST_LOG": "error",
        "SIMPLE_LIB": "/absolute/path/to/simple/src"
      }
    },
    "simple-lsp-mcp": {
      "command": "/bin/sh",
      "args": [
        "-lc",
        "cd '/absolute/path/to/simple' && exec node 'bin/mcp_stdio_bridge.js' -- 'bin/simple' run 'src/app/simple_lsp_mcp/main.spl'"
      ],
      "env": {
        "SIMPLE_LOG": "error",
        "RUST_LOG": "error",
        "SIMPLE_LIB": "/absolute/path/to/simple/src"
      }
    },
    "spipe-mcp": {
      "command": "/bin/sh",
      "args": [
        "-lc",
        "cd '/absolute/path/to/simple' && exec node 'bin/mcp_stdio_bridge.js' -- 'bin/simple' run 'src/app/spipe_mcp/main.spl'"
      ],
      "env": {
        "SIMPLE_LOG": "error",
        "RUST_LOG": "error",
        "SIMPLE_LIB": "/absolute/path/to/simple/src"
      }
    }
  }
}
```

**Note:** Current Simple install script uses source-mode workaround (`bin/simple run ...`) because native MCP binaries documented as failing real `tools/call`. Mirror that for spipe-mcp until native MCP execution is verified.

## Acceptance Tests

Minimum tests before declaring done:

1. `initialize` succeeds
2. `tools/list` returns spipe tools
3. `tools/call` `spipe_context_put` succeeds
4. `tools/call` `spipe_context_search` succeeds
5. No stdout banner or non-MCP stdout output
6. Stderr logging works
7. Explicit log-level output groups by level
8. No-level output skips level grouping
9. Mixed output has `level=none` group
10. Every rendered node has `raw` pointer
11. `spipe_context_raw` returns exact original lines
12. RepoMix/codebase-mcp output can be ingested
13. Focused Simple MCP include profile works
14. Unsafe repo/include/ignore shell characters rejected or argv-safe
15. Minimality check returns delete/stdlib/native/yagni/shrink findings

**Most important oracle:** `initialize` → `tools/list` → `tools/call`

A server merely appearing in MCP list is not enough. The real test is a successful `tools/call`, because native MCP launchers have historically failed here. The Simple install script's use of source-mode exists precisely because of this.

## MCP Stdio Contract

**Critical:** MCP stdio servers must keep stdout clean. Stdin/stdout carry MCP JSON-RPC messages; logs belong on stderr.

The MCP transport spec explicitly says:
- Stdio servers read JSON-RPC from stdin
- Write only valid MCP messages to stdout
- Use stderr for logs

**This applies to both codebase-mcp and spipe-mcp.** Banners like `"Starting server..."` must go to stderr or be removed. Strict MCP clients will fail on non-MCP stdout output.

## Security & Reliability

1. **Shell injection:** Do not build shell command strings from untrusted arguments. Use argv-style execution or strict validation.
2. **MCP verification:** Initialize + tools/list + at least one tools/call is the oracle, not server presence.
3. **Source vs. native:** Prefer source-mode launch until native binary stability is verified.
4. **Fallback parsers:** Conservative log regex only for known tools; fallback to generic_text with raw preservation.
5. **Raw text access:** Always expose original text via raw pointers so LLM can audit parser mistakes.

## Future Directions

- Native spipe_mcp_server stability: fix any core dumps on real tools/call
- Distributed context store: support multi-session indexing
- Parser auto-discovery: train scorer on tool output patterns
- Minimality debt tracking: historical complexity trends
- Hook telemetry: cross-client hook analytics
