# VSCode Extension with LSP & Semantic Tokens - Implementation Plan

**Date:** 2025-12-26
**Goal:** Implement full-featured VSCode extension with Language Server Protocol (LSP) and Tree-sitter-powered semantic tokens

## Executive Summary

This plan implements a production-ready VSCode extension for the Simple language featuring:

1. **Language Server Protocol (LSP)** - Full LSP server with all standard features
2. **Semantic Tokens** - Tree-sitter-powered syntax highlighting
3. **Tree-sitter Integration** - Fast, incremental parsing with highlight queries
4. **VSCode Extension** - TypeScript extension with LSP client

**Status:** LSP server ~85% complete (handlers implemented), missing highlight queries and VSCode client
**Effort:** ~800 lines (queries + VSCode extension + tests)
**Timeline:** 3-4 days

## Current State

### ✅ Already Implemented

**LSP Server** (`simple/app/lsp/`):
- ✅ Server core with state management (`server.spl`)
- ✅ JSON-RPC transport (`transport.spl`, `protocol.spl`)
- ✅ Document caching with incremental parsing
- ✅ Query optimization and result caching
- ✅ Debouncing for performance
- ✅ All main handlers:
  - `semantic_tokens.spl` - Semantic highlighting (needs queries)
  - `diagnostics.spl` - Parse errors
  - `hover.spl` - Documentation popups
  - `definition.spl` - Go-to-definition
  - `references.spl` - Find references
  - `completion.spl` - Code completion

**Tree-sitter Infrastructure** (`simple/std_lib/src/parser/treesitter/`):
- ✅ Parser implementation (`parser.spl`)
- ✅ Query engine (`query.spl`)
- ✅ Incremental parsing with edits (`edits.spl`)
- ✅ Grammar definitions (simple, rust, python)
- ✅ Optimization utilities

### ❌ Missing Components

1. **Tree-sitter Highlight Queries** - Empty `queries/highlights.scm`
2. **VSCode Extension Client** - TypeScript LSP client
3. **Extension Package** - package.json, activation, configuration
4. **Integration Tests** - End-to-end LSP tests
5. **Documentation** - Usage guide

## Architecture

### LSP Server Flow

```
VSCode Extension (TypeScript)
       │
       │ JSON-RPC over stdio
       ▼
LSP Server (Simple) - simple/app/lsp/server.spl
       │
       ├─ Document opened → Parse with Tree-sitter → Cache
       │
       ├─ textDocument/semanticTokens/full
       │    └─> Query tree → Capture tokens → Encode as deltas
       │
       ├─ textDocument/hover
       │    └─> Query tree → Find symbol → Return docs
       │
       ├─ textDocument/definition
       │    └─> Query tree → Find definition → Return location
       │
       ├─ textDocument/completion
       │    └─> Query tree → Find context → Return completions
       │
       └─ textDocument/didChange
            └─> Incremental parse → Update tree → Re-query
```

### Semantic Tokens with Tree-sitter

```
Source Code (.spl)
       │
       ▼
Tree-sitter Parser
       │
       ▼
Syntax Tree (Tree)
       │
       ▼
Tree-sitter Query (highlights.scm)
       │ Captures:
       │  @keyword, @function, @type, @variable, etc.
       ▼
Semantic Tokens (line, column, length, type, modifiers)
       │
       ▼
Encode as LSP Delta Format (5-tuple arrays)
       │ [deltaLine, deltaCol, length, tokenType, tokenModifiers]
       ▼
VSCode applies highlighting
```

### Tree-sitter Query Example

**highlights.scm**:
```scheme
; Keywords
["fn" "let" "if" "else" "match" "class"] @keyword

; Function definitions
(function_declaration name: (identifier) @function.definition)

; Function calls
(call_expression function: (identifier) @function.call)

; Types
(type_identifier) @type
(primitive_type) @type.builtin

; Variables
(identifier) @variable
(parameter (identifier) @parameter)
```

## Implementation Plan

### Phase 1: Tree-sitter Highlight Queries (Day 1, ~300 LOC)

**Goal:** Create comprehensive highlight queries for Simple language

**Files to Create:**

1. **`simple/std_lib/src/parser/treesitter/queries/highlights.scm`** (~250 lines)
   - Keywords (fn, let, if, else, match, class, pub, async, etc.)
   - Types (primitive types, user types, generics)
   - Functions (definitions, calls, methods)
   - Variables (identifiers, parameters, fields)
   - Literals (strings, numbers, booleans)
   - Operators (+, -, *, /, ==, etc.)
   - Comments (line, block, doc comments)
   - Punctuation (brackets, parens, braces)

2. **`simple/std_lib/src/parser/treesitter/queries/locals.scm`** (~50 lines)
   - Scope definitions
   - Variable bindings
   - References

**Implementation Steps:**

1. Map Simple AST node types to capture names
2. Define precedence for overlapping patterns
3. Test queries on sample code
4. Validate all token types are covered

**Example Query Structure:**

```scheme
; Keywords - highest priority
["fn" "let" "if" "else" "elif" "for" "while" "return" "import" "export"
 "class" "pub" "match" "async" "await" "actor" "effect"] @keyword

; Control flow
["break" "continue" "yield"] @keyword.control

; Storage modifiers
["mut" "iso" "ref"] @keyword.modifier

; Function definitions
(function_declaration
  name: (identifier) @function.definition
  (#set! "priority" 100))

; Method definitions
(method_declaration
  name: (identifier) @function.method.definition)

; Function calls
(call_expression
  function: (identifier) @function.call)

; Types
(type_identifier) @type
["i32" "i64" "f32" "f64" "bool" "String"] @type.builtin

; Class names
(class_declaration
  name: (type_identifier) @type.class.definition)

; Generics
(type_parameters
  (type_identifier) @type.parameter)

; Variables
(identifier) @variable

; Parameters have higher priority than variables
(parameter
  (identifier) @parameter
  (#set! "priority" 101))

; Fields
(field_access
  field: (identifier) @property)

; Numbers
(integer_literal) @number
(float_literal) @number

; Strings
(string_literal) @string
(fstring_literal) @string.special

; Booleans
["true" "false"] @boolean

; None/nil
["none" "nil"] @constant.builtin

; Comments
(comment) @comment
(doc_comment) @comment.documentation

; Operators
["+" "-" "*" "/" "%" "==" "!=" "<" ">" "<=" ">=" "and" "or" "not"] @operator

; Punctuation
["(" ")" "[" "]" "{" "}"] @punctuation.bracket
["," ";" ":" "."] @punctuation.delimiter
["=" "+=" "-=" "*=" "/="] @operator.assignment

; Special
(escape_sequence) @string.escape
```

---

### Phase 2: VSCode Extension Client (Day 2, ~350 LOC)

**Goal:** Create TypeScript VSCode extension that launches LSP server

**Files to Create:**

1. **`vscode-extension/package.json`** (~100 lines)
   - Extension metadata (name, publisher, version)
   - Contributes: language, grammars, configuration
   - Dependencies: vscode-languageclient
   - Activation events

2. **`vscode-extension/src/extension.ts`** (~150 lines)
   - Extension activation
   - LSP client setup
   - Server launch configuration
   - Status bar integration

3. **`vscode-extension/tsconfig.json`** (~20 lines)
   - TypeScript configuration

4. **`vscode-extension/syntaxes/simple.tmLanguage.json`** (~80 lines)
   - TextMate grammar (fallback for LSP)
   - Basic syntax highlighting patterns

**Implementation Steps:**

**Step 1: package.json**

```json
{
  "name": "simple-language",
  "displayName": "Simple Language",
  "description": "Language support for Simple programming language",
  "version": "0.1.0",
  "publisher": "simple-lang",
  "engines": {
    "vscode": "^1.80.0"
  },
  "categories": ["Programming Languages"],
  "activationEvents": ["onLanguage:simple"],
  "main": "./out/extension.js",
  "contributes": {
    "languages": [{
      "id": "simple",
      "extensions": [".spl"],
      "aliases": ["Simple", "simple"],
      "configuration": "./language-configuration.json"
    }],
    "grammars": [{
      "language": "simple",
      "scopeName": "source.simple",
      "path": "./syntaxes/simple.tmLanguage.json"
    }],
    "configuration": {
      "title": "Simple",
      "properties": {
        "simple.lsp.serverPath": {
          "type": "string",
          "default": "simple-lsp",
          "description": "Path to Simple LSP server executable"
        },
        "simple.lsp.trace.server": {
          "type": "string",
          "enum": ["off", "messages", "verbose"],
          "default": "off",
          "description": "Trace communication between VSCode and LSP server"
        }
      }
    },
    "semanticTokenTypes": [
      {"id": "keyword", "description": "Keywords"},
      {"id": "function", "description": "Functions"},
      {"id": "type", "description": "Types"},
      {"id": "variable", "description": "Variables"},
      {"id": "parameter", "description": "Parameters"},
      {"id": "property", "description": "Properties"},
      {"id": "number", "description": "Numbers"},
      {"id": "string", "description": "Strings"},
      {"id": "comment", "description": "Comments"},
      {"id": "operator", "description": "Operators"},
      {"id": "namespace", "description": "Namespaces"}
    ],
    "semanticTokenModifiers": [
      {"id": "declaration", "description": "Declaration"},
      {"id": "definition", "description": "Definition"},
      {"id": "readonly", "description": "Readonly"},
      {"id": "static", "description": "Static"},
      {"id": "deprecated", "description": "Deprecated"},
      {"id": "abstract", "description": "Abstract"},
      {"id": "async", "description": "Async"},
      {"id": "modification", "description": "Modification"},
      {"id": "documentation", "description": "Documentation"}
    ]
  },
  "scripts": {
    "vscode:prepublish": "npm run compile",
    "compile": "tsc -p ./",
    "watch": "tsc -watch -p ./",
    "package": "vsce package"
  },
  "devDependencies": {
    "@types/node": "^20.10.0",
    "@types/vscode": "^1.80.0",
    "@vscode/vsce": "^2.22.0",
    "typescript": "^5.3.3"
  },
  "dependencies": {
    "vscode-languageclient": "^9.0.1"
  }
}
```

**Step 2: extension.ts**

```typescript
import * as path from 'path';
import * as vscode from 'vscode';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

export function activate(context: vscode.ExtensionContext) {
    console.log('Simple Language extension activating...');

    // Get LSP server path from configuration
    const config = vscode.workspace.getConfiguration('simple');
    const serverPath = config.get<string>('lsp.serverPath', 'simple-lsp');

    // Server launch options
    const serverOptions: ServerOptions = {
        command: serverPath,
        args: [],
        transport: TransportKind.stdio
    };

    // Client options
    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'simple' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.spl')
        }
    };

    // Create LSP client
    client = new LanguageClient(
        'simple-lsp',
        'Simple Language Server',
        serverOptions,
        clientOptions
    );

    // Start client
    client.start();

    // Status bar item
    const statusBarItem = vscode.window.createStatusBarItem(
        vscode.StatusBarAlignment.Right,
        100
    );
    statusBarItem.text = '$(check) Simple';
    statusBarItem.tooltip = 'Simple Language Server';
    statusBarItem.show();
    context.subscriptions.push(statusBarItem);

    console.log('Simple Language extension activated');
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
```

**Step 3: TextMate Grammar (Fallback)**

Create `syntaxes/simple.tmLanguage.json` for basic syntax highlighting when LSP is unavailable.

---

### Phase 3: Integration & Testing (Day 3, ~150 LOC)

**Goal:** Test end-to-end LSP functionality

**Files to Create:**

1. **`simple/std_lib/test/unit/lsp/integration_spec.spl`** (~100 lines)
   - Test LSP server initialization
   - Test semantic tokens response
   - Test hover, definition, completion

2. **`vscode-extension/test/suite/extension.test.ts`** (~50 lines)
   - Test extension activation
   - Test LSP client connection
   - Test semantic tokens applied

**Test Cases:**

**LSP Server Tests:**

```simple
import spec.{describe, it, expect}
import lsp.server as server
import lsp.transport as transport

describe("LSP Server"):
    it("initializes successfully"):
        let srv = server.LspServer.new()
        let result = srv.handle_initialize(1, none)
        expect(result).to_be_ok()

    it("provides semantic tokens"):
        let srv = server.LspServer.new()
        srv.handle_initialize(1, none)

        # Open document
        let uri = "file:///test.spl"
        let code = "fn main(): i32 = 42"
        srv.handle_did_open(uri, 1, code)

        # Request semantic tokens
        let result = srv.handle_semantic_tokens_full(uri)
        expect(result).to_be_ok()
        expect(result.unwrap()["data"]).to_have_length_greater_than(0)

    it("parses incrementally on didChange"):
        let srv = server.LspServer.new()
        srv.handle_initialize(1, none)

        let uri = "file:///test.spl"
        srv.handle_did_open(uri, 1, "fn main():")

        # Change document
        srv.handle_did_change(uri, 2, "fn main(): i32 = 42")

        # Verify tree updated
        let doc = srv.documents[uri].unwrap()
        expect(doc.version).to_equal(2)
        expect(doc.tree).to_be_some()
```

**VSCode Extension Tests:**

```typescript
suite('Extension Tests', () => {
    test('Extension activates', async () => {
        const ext = vscode.extensions.getExtension('simple-lang.simple-language');
        await ext!.activate();
        assert.ok(ext!.isActive);
    });

    test('LSP client starts', async () => {
        // Wait for LSP to initialize
        await new Promise(resolve => setTimeout(resolve, 2000));

        // Open Simple file
        const doc = await vscode.workspace.openTextDocument({
            language: 'simple',
            content: 'fn main(): i32 = 42'
        });

        // Verify semantic tokens
        const legend = vscode.languages.getSemanticTokensLegend();
        assert.ok(legend);
        assert.ok(legend.tokenTypes.includes('keyword'));
    });
});
```

---

### Phase 4: Documentation (Day 4, ~100 LOC)

**Goal:** Create user-facing documentation

**Files to Create:**

1. **`vscode-extension/README.md`** (~80 lines)
   - Features overview
   - Installation instructions
   - Configuration options
   - Troubleshooting

2. **`doc/guides/VSCODE_EXTENSION_GUIDE.md`** (~20 lines)
   - Developer guide for extension

**README.md Content:**

```markdown
# Simple Language Extension for VSCode

Rich language support for the Simple programming language.

## Features

- **Semantic Syntax Highlighting** - Tree-sitter-powered, accurate highlighting
- **Code Completion** - Intelligent completions for keywords, types, functions
- **Go to Definition** - Jump to symbol definitions (F12)
- **Hover Information** - View documentation on hover
- **Find References** - Find all references to a symbol (Shift+F12)
- **Diagnostics** - Real-time parse error reporting

## Installation

### From VSIX
1. Download `simple-language-0.1.0.vsix`
2. Run: `code --install-extension simple-language-0.1.0.vsix`

### Build from Source
```bash
cd vscode-extension
npm install
npm run compile
vsce package
code --install-extension simple-language-0.1.0.vsix
```

## Requirements

- VSCode 1.80.0+
- Simple LSP server (`simple-lsp`) in PATH

## Configuration

Set LSP server path:
```json
{
    "simple.lsp.serverPath": "/path/to/simple-lsp"
}
```

## Troubleshooting

### LSP server not starting

Check output panel: View → Output → Simple Language Server

### Semantic highlighting not working

Verify: Editor: Semantic Highlighting is enabled in settings
```

---

## File Structure

```
simple/
├── app/lsp/                           # LSP server (Simple)
│   ├── main.spl                       # ✅ Entry point
│   ├── server.spl                     # ✅ Server core
│   ├── protocol.spl                   # ✅ LSP protocol types
│   ├── transport.spl                  # ✅ JSON-RPC stdio
│   └── handlers/
│       ├── semantic_tokens.spl        # ✅ Semantic highlighting
│       ├── diagnostics.spl            # ✅ Parse errors
│       ├── hover.spl                  # ✅ Documentation
│       ├── definition.spl             # ✅ Go-to-definition
│       ├── references.spl             # ✅ Find references
│       └── completion.spl             # ✅ Code completion
│
├── std_lib/src/parser/treesitter/    # Tree-sitter infrastructure
│   ├── parser.spl                     # ✅ Parser core
│   ├── query.spl                      # ✅ Query engine
│   ├── grammar_simple.spl             # ✅ Simple grammar
│   └── queries/
│       ├── highlights.scm             # ❌ TODO: Highlight queries
│       └── locals.scm                 # ❌ TODO: Scope queries
│
└── vscode-extension/                  # VSCode extension (TypeScript)
    ├── package.json                   # ❌ TODO: Extension manifest
    ├── tsconfig.json                  # ❌ TODO: TypeScript config
    ├── src/
    │   └── extension.ts               # ❌ TODO: LSP client
    ├── syntaxes/
    │   └── simple.tmLanguage.json     # ❌ TODO: TextMate grammar
    └── test/
        └── suite/
            └── extension.test.ts      # ❌ TODO: Extension tests
```

## Implementation Checklist

### Phase 1: Highlight Queries ✅
- [ ] Create `highlights.scm` with all token types
- [ ] Create `locals.scm` for scope tracking
- [ ] Test queries on sample code
- [ ] Validate token coverage

### Phase 2: VSCode Extension ✅
- [ ] Create package.json with LSP client dependency
- [ ] Implement extension.ts with LanguageClient
- [ ] Create TextMate grammar fallback
- [ ] Add language configuration (brackets, comments)

### Phase 3: Integration Tests ✅
- [ ] LSP server initialization test
- [ ] Semantic tokens test
- [ ] Incremental parsing test
- [ ] VSCode extension activation test

### Phase 4: Documentation ✅
- [ ] VSCode extension README
- [ ] Configuration guide
- [ ] Troubleshooting section

## Success Criteria

✅ **Semantic Tokens Work:** Accurate, fast syntax highlighting in VSCode
✅ **LSP Features Work:** Hover, go-to-definition, completion, diagnostics
✅ **Performance:** <100ms latency for semantic tokens on 1000 LOC file
✅ **Incremental:** Edits trigger incremental re-parse, not full re-parse
✅ **Tested:** All features have integration tests

## Timeline

| Phase | Days | LOC | Deliverable |
|-------|------|-----|-------------|
| 1. Highlight Queries | 1 | 300 | highlights.scm, locals.scm |
| 2. VSCode Extension | 1 | 350 | extension.ts, package.json |
| 3. Testing | 1 | 150 | Integration tests |
| 4. Documentation | 0.5 | 100 | README, guides |
| **Total** | **3.5** | **900** | **Production extension** |

## Future Enhancements

**Phase 5: Advanced Features**
- Code actions (refactoring, quick fixes)
- Formatting provider
- Rename symbol
- Document symbols (outline view)
- Workspace symbols (fuzzy search)

**Phase 6: Performance**
- Multi-threaded query execution
- Cached query compilation
- Background re-parsing

**Phase 7: Debugging**
- Debug Adapter Protocol (DAP)
- Breakpoints, step execution
- Variable inspection

---

**Plan Status:** Ready for implementation
**Dependencies:** Tree-sitter parser (✅), LSP handlers (✅), VSCode (✅)
**Effort:** ~900 lines over 3.5 days
