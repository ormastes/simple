# JS Engine + snpm — Known Limitations

## JS Engine

### Interpreter-Mode Lexer Issue
- **Status**: Open
- **Impact**: `simple js -e "code"` and `simple js file.js` don't execute correctly
- **Root cause**: The JS lexer's `char_at()` method returns nil for some positions when run through the Simple interpreter. The lexer was originally written for the browser's compiled context.
- **Workaround**: JS engine works correctly in compiled/test mode (103/103 conformance tests pass)
- **Fix needed**: Add nil guards to all `char_at()` calls in lexer.spl

### Missing ES Features
- **async/await**: Keywords parsed but not executed
- **Generators**: yield keyword recognized but not implemented  
- **RegExp**: Basic engine implemented but not wired to String.prototype.match/replace in interpreter
- **BigInt**: Not in type system
- **Proxy/Reflect**: Not implemented
- **Intl API**: Not implemented
- **eval()**: Not supported (by design — security)

### Incomplete Built-ins
- **Array.prototype.sort**: Custom comparator via callback works, but default string sort not implemented
- **Array.prototype.flatMap**: Not yet implemented
- **String.prototype.match/search**: Requires RegExp wiring
- **Math.random()**: Returns fixed 0.5 (no PRNG)
- **Date.now()**: Requires runtime FFI for system clock

## snpm Package Manager

### Registry Not Connected
- **Status**: Stub
- **Impact**: `snpm install <pkg>` resolves from manifest but can't download from remote registry
- **Workaround**: Use git/path dependencies in package.sdn
- **Fix needed**: Wire HTTP client to registry_client.spl

### Workspace Support
- **Status**: Stub  
- **Impact**: `workspaces` section in package.sdn is parsed but not acted upon
- **Fix needed**: Implement workspace discovery and cross-linking

### Interactive Login
- **Status**: Stub
- **Impact**: `snpm login` shows instructions but can't do interactive auth
- **Workaround**: Set SNPM_TOKEN environment variable

## Test Status
- ES5 conformance: 54/54 pass
- ES2015 conformance: 38/38 pass  
- Node.js API: 11/11 pass
- Browser tests: 438/438 pass (after import migration)
- Total: 103 JS + 438 browser = 541 tests passing
