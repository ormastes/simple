# bug-add uses the wrong checked text parser API

Canonical bug ID: bug_add_wrong_checked_parser_api_2026_10_27

Status: OPEN; source corrected to use the existing checked optional parse_int
API at all four call sites. Standalone native parser contract passed. The
bug-add database roundtrip and canonical DB registration remain pending.

## Evidence

The admitted Phase 2 producer SHA-256 is
1ad6ea53c67f3e01efc5c1b0ac8aa4dcef184a0987b4d3c806c59e14e96be584. Its native
build of src/app/bug_add/main.spl reported four MIR errors for parse_i64.

The source called parse_i64 as an optional method. The actual common.text
parse_i64 is a free function with -1 fallback, while text.parse_int() is the
checked optional method used by the existing call sites. The source now calls
parse_int() for the three date components and line number, preserving date nil
rejection and the line parser's ?? 0 behavior. No new parser or range
restriction was introduced.

The admitted Phase 2 producer compiled
build/object-campaign/bugdb/parse_int_contract.spl. The executable
build/object-repair/parse_int_contract.exe printed PARSER_CONTRACT_PASS and
exited 0. Compiler evidence is
build/object-repair/parser-contract/compiler.log. The fixture covers signed
i64 endpoints, a positive value above 2^60, signs, whitespace, empty and
sign-only input, malformed suffixes, overflow, nil, and the existing fallback.

## Source correction and closure evidence

The permanent correction uses the existing checked optional parse_int API.
There is no workaround tag and no planned restoration to parse_i64.

The checked-in integration spec at
test/02_integration/app/bug_add_native_parse_int_contract_spec.spl is not yet
run. The bug-add date and line values still need a roundtrip through the
canonical database API. No canonical database mutation has occurred.
