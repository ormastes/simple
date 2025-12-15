# Lexer.rs Splitting Plan (1343 lines)

## Challenge

The lexer is highly coupled - most methods depend on mutable lexer state (current_pos, line, column, chars iterator, etc.). This makes clean extraction difficult.

## Recommended Approach

### Option 1: Keep as Single File (RECOMMENDED)
**Why:**
- State machine with tight coupling
- Methods share mutable state
- Splitting would require extensive refactoring
- Current organization is actually reasonable
- 1343 lines is manageable for a single-purpose module

### Option 2: Minimal Extraction (Low Value)
Extract only truly independent utilities:
```
lexer/
├── mod.rs (main Lexer struct) - 1200 lines
└── escape.rs (escape processing) - 35 lines ✅ DONE
```
**Impact:** Minimal (97% still in one file)

### Option 3: Major Refactoring (High Effort)
Convert to builder pattern with separate scanner:
```
lexer/
├── mod.rs          - Public API (~100 lines)
├── scanner.rs      - CharScanner trait + impl (~200 lines)
├── state.rs        - LexerState struct (~100 lines)
├── tokens.rs       - Token generation methods (~400 lines)
├── indentation.rs  - INDENT/DEDENT tracking (~300 lines)
├── comments.rs     - Comment handling (~200 lines)
└── escape.rs       - Escape sequences (~40 lines)
```
**Effort:** 8-12 hours
**Risk:** High (major refactoring, easy to introduce bugs)
**Value:** Moderate (cleaner separation, but not critical)

## Recommendation: DEFER

**Reasons:**
1. **Not a priority** - 1343 lines is borderline acceptable
2. **High coupling** - Methods share extensive mutable state
3. **Better targets exist** - Focus on easier wins:
   - monomorphize.rs (Phase 2)
   - pipeline.rs (continue)
   - llvm_tests.rs (test file, easy)
   - instr.rs (clearer boundaries)

## Alternative: Document Structure

Instead of splitting, add clear section markers:
```rust
// ========== Character Scanning ==========
fn advance() { ... }
fn peek() { ... }

// ========== Indentation Tracking ==========
fn handle_indentation() { ... }

// ========== String/Number Scanning ==========
fn scan_string() { ... }
fn scan_number() { ... }

// ========== Comment Handling ==========
fn skip_comment() { ... }
```

## Decision

✅ **KEEP AS SINGLE FILE**
- Add documentation headers for sections
- Focus on higher-value splitting targets
- Revisit only if lexer grows beyond 2000 lines

## Files Created
- ✅ escape.rs (35 lines) - Minimal extraction

## Status
- Decision: Keep as single file
- Alternative targets prioritized
- May revisit in future if complexity increases
