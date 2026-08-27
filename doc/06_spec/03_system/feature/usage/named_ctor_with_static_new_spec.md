# Named-argument construction is not hijacked by `static fn new`

> `doc/08_tracking/bug/interp_static_fn_new_hijacks_named_ctor_2026-07-02.md`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Named-argument construction is not hijacked by `static fn new`

`doc/08_tracking/bug/interp_static_fn_new_hijacks_named_ctor_2026-07-02.md`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/03_system/feature/usage/named_ctor_with_static_new_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Regression gate for:**
`doc/08_tracking/bug/interp_static_fn_new_hijacks_named_ctor_2026-07-02.md`

A class that declares `static fn new(...)` with parameters that are NOT its
fields used to make the named-argument constructor form `Class(field: value)`
bind against `new`'s parameter list instead of the class fields — either
failing with `unknown argument`, or (worse) silently producing nil fields when
the names partially overlapped.

These examples pin the correct behaviour: `Class(field: value)` always binds
against the CLASS FIELDS, and `Class.new(...)` still reaches the static.

**Lane coverage — read before trusting a green run here.** `bin/simple test`
runs the tree-walk interpreter and has no JIT mode, so this file gates the
INTERPRETER lane only. The seed JIT was verified by hand at the same time (a
reversed-order call `Widget(size: 4, id: 3)` still yields `id=3 size=4`, so it
honours names rather than binding positionally), but nothing in the spec corpus
can observe that lane. A separate, still-open JIT defect in the same area —
an unknown field name being silently absorbed instead of rejected — is tracked
in `doc/08_tracking/bug/jit_named_ctor_accepts_unknown_field_name_2026-08-08.md`
and is deliberately NOT asserted here, because this suite could not fail on it.

**Known gap, deliberately not asserted (it would land RED).** The original
report's *worst* case used an argument name taken from `new`'s parameter list
rather than from the fields — `Font(path: "x", size: 8)`. That form STILL
reaches `static fn new` on both seed lanes instead of erroring, so the hijack is
only partly gone. Tracked in the reopened
`doc/08_tracking/bug/interp_static_fn_new_hijacks_named_ctor_2026-07-02.md`;
add the assertion here when that lands.

## Scenarios

### Named constructor with a static fn new present

#### binds named args against class fields, not new's params

- binds named args against class fields, not new's params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds named args against class fields, not new's params")
val w = Widget(id: 3, size: 4)
expect w.id == 3
expect w.size == 4
```

</details>

#### honours names in reversed order, so binding is not positional

- honours names in reversed order, so binding is not positional


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("honours names in reversed order, so binding is not positional")
# Discriminator: every other example passes arguments in FIELD order, so
# a binder that ignored names and bound positionally would still go
# green. This one would give id=4 size=3 under positional binding.
val w = Widget(size: 4, id: 3)
expect w.id == 3
expect w.size == 4
```

</details>

#### does not nil out fields whose names overlap new's params

- does not nil out fields whose names overlap new's params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not nil out fields whose names overlap new's params")
val f = FontLike(id: 1, size: 8)
expect f.id == 1
expect f.size == 8
```

</details>

#### still dispatches the static when called as .new

- still dispatches the static when called as .new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("still dispatches the static when called as .new")
val g = FontLike.new("x", 9)
expect g.id == 7
expect g.size == 9
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b8f400585594173c0fc6880389579785bf16718e7638bf436f8765764409776e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8f400585594173c0fc6880389579785bf16718e7638bf436f8765764409776e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8f400585594173c0fc6880389579785bf16718e7638bf436f8765764409776e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/named_ctor_with_static_new_spec.spl
mirror: doc/06_spec/03_system/feature/usage/named_ctor_with_static_new_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/named_ctor_with_static_new_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/named_ctor_with_static_new_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/named_ctor_with_static_new_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds named args against class fields, not new's params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/named_ctor_with_static_new_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'honours names in reversed order, so binding is not positional' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/named_ctor_with_static_new_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not nil out fields whose names overlap new's params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
