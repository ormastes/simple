# Native CLI phase split for the retained producer

Status: OPEN workaround for `ssa_write_count_quadratic_scan_2026_10_25`.
Base: exact frozen source `93d2d24fc57`; this is a new writable candidate.

The current native first-object attempt reached module
`app.io._CliCompile.compile_targets`. Its 250-stack sample contained 244
`local_count_increment` stacks (sample SHA256
`71737c6bd5cf7dc2a1c596ca959ad582ddf8f30d1508e317d27f6fc3bba3b68f`).
That establishes a module and compiler hotspot, not a particular project
function. `_cli_native_build` was the module's largest source function at
1018 lines. The retained producer's quadratic SSA write counter cannot receive
the independent indexed-counter source repair without rebuilding that producer.
No supported flag bypasses its counting pass.

This candidate mechanically moves the second option-parse phase into a named
helper with an explicit nonoptional record carrying its existing 33 fields plus
success/status. Invalid-record construction occurs once in its own helper.
The original defaults, evaluation order, diagnostics, parse-side effects and
failure status stay at the same call position. The help body moves into a
named helper. Six identical complete-result environment restorations call a
scalar-parameter helper retaining the exact writes and conditions. The distinct
partial early-failure restorations remain literal unchanged source.

A source-level roundtrip reinserted the moved parser/help/restoration bodies
and reproduced the original caller bytes exactly. That is evidence of the
mechanical extraction, not compiled behavior. The largest caller is now
628 lines; its lexical local-declaration count is 104 versus 112, and its
`env_set` call sites are 41 versus 126. The parse helper is 363 lines with
42 local declarations. These source counts are not MIR instruction counts,
peak-RSS predictions, or a native performance result.

Focused parser/conditional-restoration regressions are authored UNEXECUTED.
No heavy compile, P2/Rust/runtime rebuild, frozen-source mutation or live-cache
change ran for this candidate. Public entrypoint signatures and logical module
identity stay unchanged; no lambda or generic new-record carrier is introduced.
A nominal type/helper addition can still affect compilation encounter order.
A mixed-source recovery must rebuild all failed owner-0 modules and join actual
mono/name/type/signature/initializer evidence before linking with old objects.
A one-object replacement is not qualified by this source audit.

Removal requires a producer containing the reviewed indexed SSA counter to
compile the original unsplit CLI through native object emission under the same
source/runtime/provenance and resource guards. Source/interpreter checks alone
cannot establish that gate.
