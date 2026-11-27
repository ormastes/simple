# Flat-Bridge String Scan Specification

Ordinary non-raw string literals without braces bypass interpolation parsing and
brace decoding, returning the parser-owned text unchanged. Brace-bearing text
still follows the existing interpolation parser, while plain doubled braces are
decoded left-to-right with exact historical output.

The executable fixture pins empty and ordinary strings, `{{`, `}}`, odd/mixed
and consecutive escape runs, and unmatched braces. It directly inspects two
identifier placeholders in order, a valid nested-brace binary string expression,
invalid fragment fallback, and an unclosed region. Static source boundaries require the
ordinary-literal and no-escape identity paths, one final decoder join, and one
interpolation-fragment join. They reject the former growing immutable prefixes.

For literal bytes S and interpolation payload K, ordinary no-brace conversion
now performs bounded membership scans without output allocation; escaped plain
text is O(S) scan/copy work with O(number of escape runs) fragments; an actual
interpolation payload is assembled in O(K) copied bytes rather than O(K²)
cumulative prefix copying. The existing parser, expression order, raw-string
bypass, invalid-fragment fallback, and MIR ownership are unchanged.

No compiler, test, optimizer, timing, allocation, or RSS execution was performed
under the user override.

## Authored coverage annotation — 2026-11-07

Status: **AUTHORED — AWAITING_VERIFICATION**. The original manual above is
preserved as historical documentation. This appended source review is not
generated output or evidence of executed tests, complexity measurements, or
allocation/RSS results. No runtime test or docgen command was run for it.

Reviewed source: `test/01_unit/compiler/frontend/flat_bridge_string_scan_spec.spl`
at commit `b7b3845d2e0a6e0811638965be9b2ca902a9791d`;
SHA-256 `ec91b38788e19fddcba7fc4bacc485fdeecd552ec205b9141460faa5b92c787f`.
The executable source now contains six examples:

| Executable example | Assertion scope |
| --- | --- |
| Doubled braces and unmatched text | Empty/plain input, escape pairs, mixed and odd escape runs, unmatched braces. |
| Interpolation payload order and fallback | Ordered `alpha`/`beta` nodes, nested binary expression, rejected and unclosed fragments, and a valid neighbour retained beside an invalid region. |
| Ordinary literals | Identity for brace-free text; escaped braces decode without interpolation. |
| Long input | Exact decoding of 400 escape pairs and exact text/order count for 400 interpolation regions. This is a correctness assertion, not a timing benchmark. |
| Nested invalid regions through actual conversion | `parse_and_build_module` produces the independently constructed nested SDN literal unchanged: 37 bytes, with bytes 35 and 36 both equal to 125. |
| Intentional escapes through actual conversion | Doubled outer braces still decode to one brace pair around `literal`. |

The last two examples inspect the actual flat-AST string conversion rather
than only scanner helpers. Their character-code-built oracle prevents the
outer test parser from silently consuming the braces under investigation.
Rejected expression regions must retain adjacent closing braces while
intentional doubled escapes and valid interpolation keep their own behavior.

The source assertions do not establish the static source-boundary or
performance claims described in the older prose. Runtime execution, exact
executed/skipped counts, and generated-manual provenance remain pending on a
qualified pure-Simple full CLI and runner. The separate native `fill_span`
extern diagnostic does not execute this spec or qualify that toolchain.

See the published scoped prerequisites in
[Orchestrator verification wait](../../../../03_plan/sys_test/orchestrator_verification_wait_20261107.md). The retained defect evidence is
[Native nested SDN integer truncation](../../../../08_tracking/bug/native_nested_sdn_integer_truncation_2026_11_07.md).
The aggregate limit is five CPU cores across all build/test tasks. This
annotation authorizes no bridge, provider build, or test launch.
