# Cross-module text result boxing

**AUTHORED_UNRUN.** This is an authored manual, not docgen output. Native and interpreter RED/GREEN are unmeasured; loading is not execution. No coverage or zero-stub claim.

Executable: `test/02_integration/compiler/llm_caret_option_i64_owner_spec.spl`; SHA-256 `057d8bbafdf2a23908dbca17c9c0b0764bc199e085e1b6c08f584ae4875b4a1d`.
Fixture: `test/02_integration/compiler/fixtures/llm_caret_option_i64_owner.spl`; SHA-256 `b20fa2b0ed09c83b492d75439b0864f6481441816d6af8d63cd8e3fd9b7608f3`.

## Scenarios and oracle

1. Search `abc:def` through an imported function: start 0, colon 3, miss -1.
2. Coalesce the same raw search results inside that imported function: all values survive, including 0/3; even a miss is the raw scalar -1.
3. Convert `7` and `42` with the actual imported `to_int` method: exact integers and sum 49.
4. Exercise genuine optional `parse_int`: valid zero/three survive; invalid input selects explicit -99 fallback.

Requirements REQ-CARET-TEXT-BOX-001/002/003 are defined in the linked bug audit. The oracle is literal byte indexing/decimal arithmetic and documented method contracts, not another implementation or app workaround. Binary capture comments declare intended evidence; no capture artifacts exist yet.

Run each required engine with an admitted source-matched producer; then run `simple spipe-docgen test/02_integration/compiler/llm_caret_option_i64_owner_spec.spl --output doc/06_spec --no-index` and require genuine zero-stub output. The historical report stays open until qualified evidence also covers its distinct char-conversion and Caret composite-extraction residuals.

<details><summary>Executable SSpec</summary>

```simple
"""
## Purpose and audience
Compiler maintainers qualify the cross-module text scalar return channel that
historically corrupted Caret search positions and token counts.
## Operator workflow
Run with an admitted source-matched native runner, --native-backend=llvm
--assert-ran --no-cache; separately qualify Cranelift and self-hosted interpreter.
## Compatibility and limitations
AUTHORED_UNRUN. No admitted producer was available. No bootstrap or seed fallback.
index_of and to_int return raw i64; parse_int is the actual optional operation.
The historical filename identifies the report, not the current index_of type.
## Verification guidance and troubleshooting
A result of -99 for index 3 signals sentinel collision; 7/42 must remain integers.
The fixture is imported to force a module boundary and calls real text methods.
Do not substitute the app's manual substring/digit scans or count loading as execution.
"""
# codex-system-test
# Lifecycle: doc/08_tracking/bug/llm_caret_index_of_optioni64_tagbox_2026-07-07.md
# @manual_section: cross-module scalar return contract
# @evidence-display: links
use std.spec.*
use .fixtures.llm_caret_option_i64_owner.{caret_owner_find, caret_owner_find_coalesced, caret_owner_to_int, caret_owner_parse_int}

describe "Caret text result boxing across a module boundary":
    it "should preserve a present index three and the negative miss sentinel":
        # @req REQ-CARET-TEXT-BOX-001
        # @capture(binary): imported raw i64 return values, exact arithmetic oracles
        step("Load the reported search input")
        val source = "abc:def"
        step("Call the real text search in another module")
        val start = caret_owner_find(source, "abc")
        val middle = caret_owner_find(source, ":")
        val missing = caret_owner_find(source, "zzz")
        step("Compare raw positions with the source bytes")
        expect(start).to_equal(0) # oracle: abc begins at byte zero
        expect(middle).to_equal(3) # oracle: colon follows three ASCII bytes
        expect(missing).to_equal(-1) # oracle: current index_of miss contract

    it "should never treat non-optional zero or three as absence during coalescing":
        # @req REQ-CARET-TEXT-BOX-001
        # @capture(binary): imported coalesced search values, fallback -99 must not replace raw i64
        step("Load the reported search input")
        val source = "abc:def"
        step("Coalesce real text search results inside the imported module")
        val start = caret_owner_find_coalesced(source, "abc")
        val middle = caret_owner_find_coalesced(source, ":")
        val missing = caret_owner_find_coalesced(source, "zzz")
        step("Compare values with the non-optional method contract")
        expect(start).to_equal(0) # oracle: raw zero is a present scalar
        expect(middle).to_equal(3) # oracle: raw three is a present scalar, not nil
        expect(missing).to_equal(-1) # oracle: a search miss remains raw minus one

    it "should return the reported decimal values as integers across modules":
        # @req REQ-CARET-TEXT-BOX-002
        # @capture(binary): imported to_int values must retain numeric payloads
        step("Load the reported decimal strings")
        val seven = "7"
        val forty_two = "42"
        step("Call the real numeric conversion in another module")
        val first = caret_owner_to_int(seven)
        val second = caret_owner_to_int(forty_two)
        step("Compare numeric values and arithmetic use")
        expect(first).to_equal(7) # oracle: decimal seven
        expect(second).to_equal(42) # oracle: decimal forty-two
        expect(first + second).to_equal(49) # oracle: 7 + 42, not boxed-handle rendering

    it "should distinguish a genuine optional parse failure from zero and three":
        # @req REQ-CARET-TEXT-BOX-003
        # @capture(binary): imported strict parse_int presence and absence
        step("Load valid and invalid decimal strings")
        val zero = "0"
        val three = "3"
        val invalid = "not-an-integer"
        step("Parse through the genuine optional API in another module")
        val first = caret_owner_parse_int(zero)
        val second = caret_owner_parse_int(three)
        val absent = caret_owner_parse_int(invalid)
        step("Compare optional payloads and explicit fallback")
        expect(first).to_equal(0) # oracle: Some(0) must preserve zero
        expect(second).to_equal(3) # oracle: Some(3) must preserve three
        expect(absent).to_equal(-99) # oracle: None selects the fixture's explicit fallback
```
</details>
