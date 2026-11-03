# Query code-action edit roundtrip

Requirement: REQ-LSP-CODEACTION-EDIT-001 — query-derived workspace edits preserve empty deletion text, nonempty insertion text, the edit range and the request URI. Missing or null replacement text must not fabricate a deletion.

Executable source: `test/01_unit/app/lsp/code_action_edit_roundtrip_spec.spl`.

The six scenarios call the same pure query-output conversion used by `lsp_handle_code_action`. They compare the complete serialized action array, including document changes, request URI, null document version, range and replacement text. Scenarios cover nested deletion, escaped insertion, missing and null nested text, legacy deletion with one-based line conversion, and missing legacy text.

Execution status: **UNRUN**. This is an authored manual, not generated execution evidence. The available `bin/simple.exe` is a Rust bootstrap seed, and no admitted self-hosted `bin/release` runtime was identified. Source review and `git diff --check` do not establish runtime correctness. Core/compiler/library/MCP checks and native smoke gates remain pending a qualified self-hosted producer.

The fixture deliberately avoids launching an external query process; it verifies the protocol conversion owner. It does not establish that every CLI code-action producer emits valid JSON, nor that a real LSP client applies the resulting edit.
