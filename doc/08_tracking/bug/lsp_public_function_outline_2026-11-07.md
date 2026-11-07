# Public functions must appear in LSP outline metadata

Status: focused native purpose checks passed; full pure-runtime gates pending.

Symbols recognized public functions while the separate outline parser used by hover and definition recognized only bare fn declarations. Public function hover fell back to generic metadata and local definition missed. Reusing the existing visibility-prefix helper for recognition and name parsing retains authored signatures, documentation and token ranges.

The authored SSpec checks public and scoped-public metadata and ordinary/invalid-prefix controls. Two source fixtures preserve the public and documented-public cases. The changed native worker 9cb3d279a62e3ff544f8a5d5821e1706a23deabae1cc44a18e3520471138385d passed sixteen actual purpose checks including symbols, hover, definition and negative controls. Evidence: build/review/lsp-public-function-native-v4-attempt1/RESULT.md and purpose/RESULT.sdn.

Observed warm requests were 18-61 ms; cold startup was 5.33 s and its NFR remains open. Unit SSpec execution, full pure compiler/lib/MCP/LSP checks, MCP stdio integration and complete native LSP parity remain pending. No hardware or deployment qualification is claimed, and no native binary is distributed here.
