# Native SSpec framework wrapper

Status: source candidate; **NOT_RUN**. This repair enables the existing
configured framework path; it does not qualify a compiler or runner.

The canonical explicit-AOT executor formerly used its legacy SMF preprocessor.
That removed std.spec imports and rewrote matcher calls to rt_bdd helpers while
leaving describe/it/hooks as calls. The Pure-Simple frontend lowers colon blocks
to ordinary closures; removing their callable owners caused unresolved symbols.

The executor now selects complete-framework wrapping for explicit native AOT
and coverage's AOT path. Plain legacy SMF wrapping keeps its previous matcher
rewrites, import filtering, helper injection and entrypoint behavior.

`std.common.test_runner.native_framework_wrapper` is a pure shared owner. It
contains the extracted source partitioner used by both paths, plus the native
source constructor. It imports no compiler, host or memory-family module.
The existing executor computes lexical code/string-continuation facts and
native-only canonical string byte ranges, then
passes them in, preventing a common-to-compiler dependency and repeated lexing.
All application-facing framework/result imports remain generic `std.spec`.
Actual memory/concurrency family selection belongs to configuration and is not
inferred from this executor's physical implementation directory.

Native wrapping preserves wildcard/named/multiline imports, method matchers,
hooks, nested closures and declaration bodies. Only column-zero imports are
hoisted; helper and sibling-local aliases keep their original scope. Legacy
SMF retains its historical import-hoisting behavior. It normalizes legacy infix
assertions only on lines identified as executable code, locating matcher
tokens through canonical string byte ranges rather than phrases inside quoted
operands. Raw UTF-8 operands and quoted hashes remain intact, and generated
closing parentheses precede preserved trailing comments. Native-only struct and
public declarations remain at module scope; legacy classification is unchanged.
An existing top-level main or inconsistent lexical mapping is refused. Methods
named main and main-like text inside strings remain ordinary source.

Generated main calls the real configured print_summary, executed-example count
and exit-code owners. Zero executed examples returns2; otherwise the framework
exit status is returned, including genuine assertion failure. Bounded alias
selection avoids shadowing caller declarations. No assertion, hook, step or
verdict implementation is synthesized. Coverage's original source marker and
existing private generated-source ownership/cleanup remain with the executor.

The structural unit spec is not native execution proof. Qualification requires
both real compiled fixtures through the production runner: hooks_and_siblings
must execute3/pass3/exit0; failure_continuation must execute3/pass2/fail1/exit1.
The negative result must be an actual matcher failure after body execution,
with later bodies and after hooks observed, not a compile or ownership error.
No tests were run while preparing this source candidate.
