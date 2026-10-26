# SOURCE field-default replay performs unaccounted artifact work

Status: OPEN callable API gap; no executed driver failure claimed. Private
archive invocation activation is still absent. The account-aware codec
prerequisite below does not close the complete field-default path.

At caller base06903799e18 (also b1f33e5808c),
`replay_source_region_preflight_function_v1` and
`lower_source_region_function_installed_v1` can call `lower_function` with the
SOURCE compile account installed. An omitted declared provider field reaches
`lower_struct_construct` in `_MirLoweringExpr/switch_operators_calls.spl:6179`,
then `resolve_struct_field_default_expr_v1`,
`load_declaration_field_default_v1`, `load_declaration_expression_v1`, and
`load_declaration_raw_expression_v1` in `declaration_providers_v1`. The raw
loader invokes `mir_hir_expression_load_in_owned_scope_v1` without that account:
cache read, envelope/hash processing, decode and stable reencode occur before
later SOURCE instruction classification can refuse the original.

This is separate from direct-call parameter defaults: verification replay uses
retained HIR parameter defaults instead of the ordinary cache default loader.
That corrected direct-call path is not evidence of this field-default bug.

The existing budget-reporting expression sibling takes an allocation limit and
reports spent bytes. Its common blob loader requires the maximum file read
window up front. Neither a local limit nor returned spent bytes debit the
actual SOURCE account before work. Passing all remaining budget would not fix
the bug or admit realistic large-module inputs honestly.

The first implementation checkpoint adds same-account codec constructors and
pre-operation work/allocation hooks, plus a filesystem-free retained-blob
consumer sharing the ordinary decode/stability implementation. It does not
change the raw declaration loader or activate replay through this route.
The second checkpoint repairs the generated encoder's continued traversal after
account failure. Actual entry/loop visits are charged before heap/child work;
poison stops propagation immediately and depth is limited by the actual account.
Source generator and checked-in artifact are updated together. This does not
close the remaining loader ownership, relocation and invocation boundaries.

Remaining necessary repairs before closure:

- Retain authenticated raw default artifacts during actual selected-target
  ordinary lowering within the admitted archive owner's synchronous scope.
  Cache data is not an admission witness. Do not retain on every ordinary
  compiler invocation or permit SOURCE fallback to I/O.
- Bind current repository/target/record identity, exact omitted and transitive
  defaults, and error/reset lifetime before promotion or transient scope end.
  Completed MIR alone does not prove retention completeness.
- Account for `declaration_links_v1` and recursive cross-module default remapping
  after decode, or prove equivalent already-bound immutable inputs. Codec
  accounting alone leaves those variable scans/allocations open.
- Wire both replay activation paths and actual private orchestration; preserve
  valid omitted defaults through this real setup rather than replacing support
  with permanent missing-cache refusal.
- Run real positive/default/mutation/budget controls once execution is admitted.

All tests in this checkpoint are authored UNRUN. Existing ordinary admission
and loading remain an explicit compiler resource domain outside the SOURCE
invocation account; there is no globally bounded compiler or native/RSS claim.
