# scv_structural_roots_diff_spec

> Gap D (scv_v2_wrapper_architecture_report_2026-08-25): the working-copy

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_structural_roots_diff_spec

Gap D (scv_v2_wrapper_architecture_report_2026-08-25): the working-copy

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_structural_roots_diff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Gap D (scv_v2_wrapper_architecture_report_2026-08-25): the working-copy
    `diff --structural` path used only simplified top-level text blocks and
    never fed the GumTree-style matcher real stored syntax roots. These
    examples pin the honest-provenance contract: when the object store holds
    a parse root for BOTH sides of a file comparison (base chunk id and
    current content id), the diff must route through the real matcher over
    those stored nodes and label the result `structural_source=syntax-roots`;
    when either root is missing it must keep the text-block path and label it
    `structural_source=text-blocks`, so callers and specs can discriminate.

    Deliverable variant note: the fallback-line parser embeds the line number
    in each line node's syntax hash ("line:{line_no}:{line}"), so its nodes
    are too coarse for the matcher to out-discriminate the text-block path on
    move/rename cases. These examples therefore prove ACTIVATION and
    AGREEMENT (both paths classify the file as structurally changed);
    move/rename discrimination waits on the real tree-sitter (WS-A) parse
    roots.

## Scenarios

### scv structural diff over stored parse roots

#### routes through stored syntax roots and labels the provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-roots-diff.XXXXXX)\nprintf 'fn alpha():\\n    pass\\nfn beta():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate code.spl >/dev/null\nprintf 'fn beta():\\n    pass\\nfn alpha():\\n    pass\\n' > code.spl\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate code.spl >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'structural_source=text-blocks code.spl'*) printf 'FAIL: fell back to text blocks despite stored roots\\n'; exit 9;; esac\n"
val out = _run_roots_script(script)
expect(out).to_contain("structural_source=syntax-roots code.spl")
expect(out).to_contain("syntax-ops code.spl:")
```

</details>

#### agrees with the text-block path that the file changed structurally

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-roots-agree.XXXXXX)\nprintf 'fn alpha():\\n    pass\\nfn beta():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate code.spl >/dev/null\nprintf 'fn beta():\\n    pass\\nfn alpha():\\n    pass\\n' > code.spl\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate code.spl >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf 'ROOTS:%s\\n' \"$OUT\"\ncase \"$OUT\" in *'no changes'*) printf 'FAIL: syntax path missed the change\\n'; exit 9;; esac\n"
val out = _run_roots_script(script)
expect(out).to_contain("structural_source=syntax-roots code.spl")
```

</details>

#### keeps the labeled text-block fallback when no parse roots exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-roots-fallback.XXXXXX)\nprintf 'fn alpha():\\n    pass\\nfn beta():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn beta():\\n    pass\\nfn alpha():\\n    pass\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'structural_source=syntax-roots'*) printf 'FAIL: claimed syntax roots without any stored parse\\n'; exit 9;; esac\n"
val out = _run_roots_script(script)
expect(out).to_contain("structural_source=text-blocks code.spl")
expect(out).to_contain("moved alpha")
```

</details>

#### loads REAL P-05 CST roots keyed by revision+ContentId and discriminates a move

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-roots-cst.XXXXXX)\nprintf 'fn alpha():\\n    pass\\nfn beta():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nR=\"$REPO/bin/simple run $REPO/src/app/scv/main.spl\"\nexport SIMPLE_LIB=\"$REPO/src\"\n$R init >/dev/null\n$R cst-store code.spl | grep -q 'cst-root ' || { printf 'FAIL: cst-store v1\\n'; exit 9; }\n$R parse-gate code.spl >/dev/null\n$R snapshot >/dev/null\nprintf 'fn beta():\\n    pass\\nfn alpha():\\n    pass\\n    x = 1\\n' > code.spl\n$R cst-store code.spl >/dev/null\n$R parse-gate code.spl >/dev/null\nOUT=$($R diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'structural_source=syntax-roots'*|*'structural_source=text-blocks'*) printf 'FAIL: stored CST roots were not preferred\\n'; exit 9;; esac\n"
val out = _run_roots_script(script)
expect(out).to_contain("structural_source=cst-roots code.spl")
expect(out).to_contain("cst-roots code.spl: base=op_")
expect(out).to_contain(" head=op_")
expect(out).to_contain("moved fn beta")
expect(out).to_contain("moved fn alpha")
expect(out).to_contain("updated fn alpha")
```

</details>

#### reports a rename over CST roots and never silently accepts an ambiguous one

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nR=\"$REPO/bin/simple run $REPO/src/app/scv/main.spl\"\nexport SIMPLE_LIB=\"$REPO/src\"\nTMP=$(mktemp -d /tmp/scv-roots-rename.XXXXXX)\nprintf 'fn alpha():\\n    a = 1\\nfn beta():\\n    b = 2\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\n$R init >/dev/null\n$R cst-store code.spl >/dev/null\n$R snapshot >/dev/null\nprintf 'fn alpha():\\n    a = 1\\nfn gamma():\\n    b = 2\\n' > code.spl\n$R cst-store code.spl >/dev/null\nOUT1=$($R diff --structural)\nprintf 'ONE:%s\\n' \"$OUT1\"\nTMP2=$(mktemp -d /tmp/scv-roots-ambig.XXXXXX)\nprintf 'fn alpha():\\n    a = 1\\nfn beta():\\n    b = 2\\n' > \"$TMP2/code.spl\"\ncd \"$TMP2\"\n$R init >/dev/null\n$R cst-store code.spl >/dev/null\n$R snapshot >/dev/null\nprintf 'fn alpha():\\n    a = 1\\nfn gamma():\\n    b = 2\\nfn delta():\\n    b = 2\\n' > code.spl\n$R cst-store code.spl >/dev/null\nOUT2=$($R diff --structural)\nprintf 'TWO:%s\\n' \"$OUT2\"\ncase \"$OUT2\" in *'renamed fn beta'*) printf 'FAIL: ambiguous rename was accepted\\n'; exit 9;; esac\n"
val out = _run_roots_script(script)
expect(out).to_contain("renamed fn beta -> fn gamma")
expect(out).to_contain("ambiguous fn beta")
expect(out).to_contain("added fn gamma")
expect(out).to_contain("added fn delta")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e87c58c27d9276995d967854c7f5c5ed97343df092273f6a6f34bd0eaf8a407`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e87c58c27d9276995d967854c7f5c5ed97343df092273f6a6f34bd0eaf8a407`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e87c58c27d9276995d967854c7f5c5ed97343df092273f6a6f34bd0eaf8a407`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/integration/app/scv_structural_roots_diff_spec.spl
mirror: doc/06_spec/integration/app/scv_structural_roots_diff_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_structural_roots_diff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_structural_roots_diff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_structural_roots_diff_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/integration/app/scv_structural_roots_diff_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/integration/app/scv_structural_roots_diff_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/integration/app/scv_structural_roots_diff_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/integration/app/scv_structural_roots_diff_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'routes through stored syntax roots and labels the provenance' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_structural_roots_diff_spec.spl:56:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'agrees with the text-block path that the file changed structurally' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_structural_roots_diff_spec.spl:70:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps the labeled text-block fallback when no parse roots exist' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_structural_roots_diff_spec.spl:84:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'loads REAL P-05 CST roots keyed by revision+ContentId and discriminates a move' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
