# Generic substitution model: laws, checked exhaustively over a bounded universe

> Contract of the one generic substitution implementation of the compiler:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic substitution model: laws, checked exhaustively over a bounded universe

Contract of the one generic substitution implementation of the compiler:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/30.types/generic_subst/generic_subst_model_laws_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Contract of the one generic substitution implementation of the compiler:
substituting type arguments into a type, matching evidence against a declared
type, resolving a call site, and writing the specialization key. Compiler
engineers changing instance creation, the TLDR generic view or the template
projector read this to learn which laws they may rely on and how each is
checked. Every law is swept over a finite universe whose sizes are asserted,
so an empty sweep fails instead of passing.

## Operator workflow
Run `bin/simple test test/01_unit/compiler/30.types/generic_subst/generic_subst_model_laws_spec.spl`
after any edit to `src/compiler/30.types/generic_subst/`. A failure message
names the law (S1..S3, U1..U3, I1, K1..K3) and the first offending type.

## Compatibility and limitations
Bounded exhaustive checking, not a proof for arbitrary terms; the Lean model
covers substitution only (see the correspondence table in the model header).
Key framing and decoding count bytes (UTF-8), the same unit as the template
projector; the Lean model does not cover keys.

## Verification guidance and troubleshooting
A S-law failure points at `ms_apply`/`ms_compose`; a U-law failure at
`mm_match`; I1 at `mi_infer`; K-laws at `mt_key_type`/`mt_from_key`. Universe
size mismatches mean `generic_subst_universe.spl` changed.
# Generic substitution model: laws, checked exhaustively over a bounded universe

`src/compiler/30.types/generic_subst/generic_subst_model.spl` is the one substitution implementation; it models
what generic instances do with a type variable: substitution, one-way matching, call-site inference and
the specialization key. This spec checks its algebraic laws on EVERY element
of the finite universes of `generic_subst_universe.spl` (sizes are printed and
asserted, so an empty sweep fails).

This is bounded exhaustive checking plus explicit adversarial key examples,
not a proof for arbitrary terms. The separate Lean proof lane covers model
substitution laws; it does not discharge executable key-encoding correctness.

| Law | Statement | Universe |
|-----|-----------|----------|
| S1 | s(s(t)) = s(t) for a closed-range s | 365 types x 81 substitutions |
| S3 | free(s(t)) = free(t) minus dom(s); closed when that is empty | same |
| S2 | (s2 o s1)(t) = s2(s1(t)) | 95 types x 64 open x 25 closed substitutions |
| U1 | match(p, s(p)) = b implies b(p) = s(p) | 95 patterns x 64 total substitutions |
| U2 | b binds exactly free(p) and agrees with s there | same |
| U3 | conflicting or mis-shaped evidence is Conflict / Shape, open evidence binds nothing | enumerated |
| I1 | a variable with no evidence makes the call Unresolved, never a default | 36 signatures x 16 substitutions x 4 masks |
| K1 | the key is a function of its inputs | 147 closed types |
| K2 | equal keys imply structurally equal type-argument lists | 147 singles + 1521 pairs |
| K3 | decoding a type key (`mt_from_key`) returns the same type; garbage is rejected | 365 types |

## Scenarios

### generic substitution model: universes

#### has the stated sizes and no duplicate

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Build the type, substitution and closed-range universes and count them
   - Expected: mu_depth1(mu_atoms()).len() equals `95)  # oracle: 5 atoms + 3 unary constructors x 5 atoms + 3 binary constructo... (full value in folded executable source)`
   - Expected: types.len() equals `365)  # oracle: the 95 depth-1 types + 3 unary constructors x the 90 non-atom... (full value in folded executable source)`
   - Expected: mu_closed_types().len() equals `147)  # oracle: closed types of the universe: the closed members of the 365 (... (full value in folded executable source)`
   - Expected: mu_substs(mu_closed_range(), false).len() equals `81)  # oracle: two variables, each unbound or bound to one of 8 closed types:... (full value in folded executable source)`
   - Expected: mu_substs(mu_closed_range(), true).len() equals `64)  # oracle: two variables, each bound to one of 8 closed types: 8 x 8`
   - Expected: seen.keys().len() equals `365)  # oracle: the 95 depth-1 types + 3 unary constructors x the 90 non-atom... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Build the type, substitution and closed-range universes and count them")
val types = mu_types()
expect(mu_depth1(mu_atoms()).len()).to_equal(95)  # oracle: 5 atoms + 3 unary constructors x 5 atoms + 3 binary constructors x 25 atom pairs = 5 + 15 + 75
expect(types.len()).to_equal(365)  # oracle: the 95 depth-1 types + 3 unary constructors x the 90 non-atom depth-1 types = 95 + 270
expect(mu_closed_types().len()).to_equal(147)  # oracle: closed types of the universe: the closed members of the 365 (no variable T or U anywhere)
expect(mu_substs(mu_closed_range(), false).len()).to_equal(81)  # oracle: two variables, each unbound or bound to one of 8 closed types: 9 x 9
expect(mu_substs(mu_closed_range(), true).len()).to_equal(64)  # oracle: two variables, each bound to one of 8 closed types: 8 x 8
var seen: Dict<text, bool> = {}
for t in types:
    val tt: MType = t
    seen[mt_render(tt)] = true
expect(seen.keys().len()).to_equal(365)  # oracle: the 95 depth-1 types + 3 unary constructors x the 90 non-atom depth-1 types = 95 + 270
```

</details>

### generic substitution model: substitution laws

#### S1 idempotence and S3 closedness on every type and closed substitution

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Apply every closed substitution to every type, twice, and compare free variables and closedness
   - Expected: bad equals ``
   - Expected: checked equals `29565)  # oracle: 365 types x 81 closed substitutions, one check per pair`
   - Expected: closed_results > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Apply every closed substitution to every type, twice, and compare free variables and closedness")
val types = mu_types()
val substs = mu_substs(mu_closed_range(), false)
var checked = 0
var closed_results = 0
var bad = ""
for s in substs:
    val st: MSubst = s
    val dom = ms_domain(st)
    for t in types:
        val tt: MType = t
        val once = ms_apply(st, tt)
        checked = checked + 1
        if not mt_struct_eq(ms_apply(st, once), once):
            bad = "S1 {ms_render(st)} {mt_render(tt)}"
        val expected_free = minus(mt_free_vars(tt), dom)
        if not same_set(mt_free_vars(once), expected_free):
            bad = "S3 free {ms_render(st)} {mt_render(tt)}"
        if expected_free.len() == 0:
            closed_results = closed_results + 1
            if not mt_is_closed(once):
                bad = "S3 closed {ms_render(st)} {mt_render(tt)}"
print "S1/S3 checked={checked} closed_results={closed_results}"
expect(bad).to_equal("")
expect(checked).to_equal(29565)  # oracle: 365 types x 81 closed substitutions, one check per pair
expect(closed_results > 0).to_equal(true)
```

</details>

#### S2 composition on every depth<=1 type, open substitution and closed substitution

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Compose each open substitution with each closed one and compare with applying them in sequence
   - Expected: bad equals ``
   - Expected: inner.len() equals `64)  # oracle: two variables, each bound to one of 8 closed types: 8 x 8`
   - Expected: outer.len() equals `25)  # oracle: two variables, each bound to one of the 5 atoms: 5 x 5`
   - Expected: checked equals `152000)  # oracle: 95 types x 64 inner x 25 outer substitutions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-001
step("Compose each open substitution with each closed one and compare with applying them in sequence")
val types = mu_depth1(mu_atoms())
val inner = mu_substs(mu_open_range(), false)
val outer = mu_substs(mu_small_closed_range(), false)
var checked = 0
var bad = ""
for s1 in inner:
    val a: MSubst = s1
    for s2 in outer:
        val b: MSubst = s2
        val composed = ms_compose(b, a)
        for t in types:
            val tt: MType = t
            checked = checked + 1
            if not mt_struct_eq(ms_apply(composed, tt), ms_apply(b, ms_apply(a, tt))):
                bad = "S2 outer={ms_render(b)} inner={ms_render(a)} {mt_render(tt)}"
print "S2 checked={checked} inner={inner.len()} outer={outer.len()}"
expect(bad).to_equal("")
expect(inner.len()).to_equal(64)  # oracle: two variables, each bound to one of 8 closed types: 8 x 8
expect(outer.len()).to_equal(25)  # oracle: two variables, each bound to one of the 5 atoms: 5 x 5
expect(checked).to_equal(152000)  # oracle: 95 types x 64 inner x 25 outer substitutions
```

</details>

### generic substitution model: matching laws

#### U1 soundness and U2 most-general on every pattern and total closed substitution

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Match every pattern against its own substituted instance and compare the binding with the substitution
   - Expected: bad equals ``
   - Expected: checked equals `6080)  # oracle: 95 patterns x 64 total substitutions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Match every pattern against its own substituted instance and compare the binding with the substitution")
val patterns = mu_depth1(mu_atoms())
val substs = mu_substs(mu_closed_range(), true)
var checked = 0
var bad = ""
for s in substs:
    val st: MSubst = s
    for p in patterns:
        val pt: MType = p
        val evidence = ms_apply(st, pt)
        val m = mm_match(pt, evidence, ms_empty())
        checked = checked + 1
        if not mm_is_bound(m):
            bad = "U1 not bound {ms_render(st)} {mt_render(pt)}"
            continue
        val b = mm_subst(m)
        if not mt_struct_eq(ms_apply(b, pt), evidence):
            bad = "U1 {ms_render(st)} {mt_render(pt)}"
        val free = mt_free_vars(pt)
        if not same_set(ms_domain(b), free):
            bad = "U2 domain {ms_render(st)} {mt_render(pt)} got {ms_render(b)}"
        for v in free:
            val vn: text = v
            if not mt_struct_eq(ms_get(b, vn), ms_get(st, vn)):
                bad = "U2 agree {ms_render(st)} {mt_render(pt)}"
print "U1/U2 checked={checked}"
expect(bad).to_equal("")
expect(checked).to_equal(6080)  # oracle: 95 patterns x 64 total substitutions
```

</details>

#### U3 a repeated variable with two different witnesses is a Conflict

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Match a repeated variable against every pair of closed witnesses
   - Expected: bad equals ``
   - Expected: agreements equals `8)  # oracle: the diagonal of the 8 x 8 closed-witness grid: both witnesses e... (full value in folded executable source)`
   - Expected: conflicts equals `56)  # oracle: the off-diagonal of the 8 x 8 grid: 64 - 8 pairs with differen... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Match a repeated variable against every pair of closed witnesses")
val range = mu_closed_range()
val pattern = mt_app(MT_TUPLE, [mt_var("T"), mt_var("T")])
var conflicts = 0
var agreements = 0
var bad = ""
for a in range:
    val x: MType = a
    for b in range:
        val y: MType = b
        val m = mm_match(pattern, mt_app(MT_TUPLE, [x, y]), ms_empty())
        if mt_struct_eq(x, y):
            agreements = agreements + 1
            if mm_render(m) != "Bound\{T:=" + mt_render(x) + "\}":
                bad = "agree {mt_render(x)}: {mm_render(m)}"
        else:
            conflicts = conflicts + 1
            if mm_render(m) != "Conflict(T)":
                bad = "conflict {mt_render(x)} {mt_render(y)}: {mm_render(m)}"
expect(bad).to_equal("")
expect(agreements).to_equal(8)  # oracle: the diagonal of the 8 x 8 closed-witness grid: both witnesses equal, so no conflict
expect(conflicts).to_equal(56)  # oracle: the off-diagonal of the 8 x 8 grid: 64 - 8 pairs with different witnesses conflict
```

</details>

#### U3 a different constructor or arity is a Shape mismatch

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Match patterns against evidence with another constructor or another arity
   - Expected: bad equals ``
   - Expected: checked equals `9)  # oracle: 3 constructors x 3 arity or constructor mismatches enumerated i... (full value in folded executable source)`
   - Expected: mm_render(mm_match(mt_app(MT_SLICE, [mt_var("T")]), mt_app(MT_ARRAY, [mt_con("text")]), ms_empty())) equals `Bound\{T:=text\}`
   - Expected: mm_render(mm_match(mt_app(MT_ARRAY, [mt_var("T")]), mt_app(MT_SLICE, [mt_con("text")]), ms_empty())) equals `Shape`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Match patterns against evidence with another constructor or another arity")
var checked = 0
var bad = ""
for pc in mu_unary_ctors():
    val pctor: text = pc
    val pattern = mt_app(pctor, [mt_var("T")])
    for ec in mu_unary_ctors():
        val ector: text = ec
        val m = mm_match(pattern, mt_app(ector, [mt_con("i64")]), ms_empty())
        checked = checked + 1
        if pctor == ector:
            if mm_render(m) != "Bound\{T:=i64\}":
                bad = "same ctor {pctor}: {mm_render(m)}"
        elif mm_render(m) != "Shape":
            bad = "{pctor} vs {ector}: {mm_render(m)}"
    val against_atom = mm_match(pattern, mt_con("i64"), ms_empty())
    if mm_render(against_atom) != "Shape":
        bad = "{pctor} vs atom: {mm_render(against_atom)}"
    val against_binary = mm_match(pattern, mt_app(MT_TUPLE, [mt_con("i64"), mt_con("i64")]), ms_empty())
    if mm_render(against_binary) != "Shape":
        bad = "{pctor} vs tuple: {mm_render(against_binary)}"
expect(bad).to_equal("")
expect(checked).to_equal(9)  # oracle: 3 constructors x 3 arity or constructor mismatches enumerated in this scenario
# The one sanctioned widening: a Slice parameter accepts an Array.
expect(mm_render(mm_match(mt_app(MT_SLICE, [mt_var("T")]), mt_app(MT_ARRAY, [mt_con("text")]), ms_empty()))).to_equal("Bound\{T:=text\}")
expect(mm_render(mm_match(mt_app(MT_ARRAY, [mt_var("T")]), mt_app(MT_SLICE, [mt_con("text")]), ms_empty()))).to_equal("Shape")
```

</details>

#### U3 evidence that is not closed binds nothing

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Match a variable against evidence that still holds a variable
   - Expected: mm_render(unknown) equals `Bound\{\}`
   - Expected: bad equals ``
   - Expected: checked equals `218)  # oracle: enumerated open-evidence cases of this scenario (patterns x o... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Match a variable against evidence that still holds a variable")
var checked = 0
var bad = ""
for t in mu_types():
    val tt: MType = t
    if mt_is_closed(tt):
        continue
    checked = checked + 1
    val m = mm_match(mt_var("T"), tt, ms_empty())
    if mm_render(m) != "Bound\{\}":
        bad = "{mt_render(tt)}: {mm_render(m)}"
val unknown = mm_match(mt_var("T"), mt_unknown(), ms_empty())
expect(mm_render(unknown)).to_equal("Bound\{\}")
expect(bad).to_equal("")
expect(checked).to_equal(218)  # oracle: enumerated open-evidence cases of this scenario (patterns x open evidence shapes)
```

</details>

### generic substitution model: call-site inference

#### I1 resolves exactly when every variable has evidence, and then to the witness

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Infer every signature under every substitution and every evidence mask
   - Expected: bad equals ``
   - Expected: checked equals `2304)  # oracle: 36 signatures x 16 substitutions x 4 evidence masks`
   - Expected: resolved > 0 is true
   - Expected: unresolved > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Infer every signature under every substitution and every evidence mask")
val gamma = ["T", "U"]
val shapes = [mt_var("T"), mt_var("U"), mt_con("i64"),
              mt_app(MT_ARRAY, [mt_var("T")]),
              mt_app(MT_TUPLE, [mt_var("T"), mt_var("U")]),
              mt_app(MT_OPTIONAL, [mt_var("U")])]
val substs = mu_substs(mu_small_closed_range(), true)
var checked = 0
var resolved = 0
var unresolved = 0
var bad = ""
for p1 in shapes:
    val a: MType = p1
    for p2 in shapes:
        val b: MType = p2
        for s in substs:
            val st: MSubst = s
            var mask = 0
            while mask < 4:
                val known_a = mask % 2 == 1
                val known_b = mask >= 2
                var evidenced: [text] = []
                var arg_a = mt_unknown()
                var arg_b = mt_unknown()
                if known_a:
                    arg_a = ms_apply(st, a)
                    evidenced = mt_free_vars_into(a, evidenced)
                if known_b:
                    arg_b = ms_apply(st, b)
                    evidenced = mt_free_vars_into(b, evidenced)
                val r = mi_infer(gamma, [a, b], mt_con("bool"), [], [arg_a, arg_b], mt_unknown(), false)
                checked = checked + 1
                if subset(gamma, evidenced):
                    resolved = resolved + 1
                    val want = "Resolved" + mt_render_list([ms_get(st, "T"), ms_get(st, "U")])
                    if mi_render(r) != want:
                        bad = "want {want} got {mi_render(r)}"
                else:
                    unresolved = unresolved + 1
                    if mi_render(r) != "Unresolved(no_evidence)":
                        bad = "no evidence, got {mi_render(r)} for {mt_render(a)},{mt_render(b)} mask={mask}"
                mask = mask + 1
print "I1 checked={checked} resolved={resolved} unresolved={unresolved}"
expect(bad).to_equal("")
expect(checked).to_equal(2304)  # oracle: 36 signatures x 16 substitutions x 4 evidence masks
expect(resolved > 0).to_equal(true)
expect(unresolved > 0).to_equal(true)
```

</details>

#### uses the expected type as evidence for a return-only variable

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Infer a return-only variable from the expected type
   - Expected: mi_render(none) equals `Unresolved(no_evidence)`
   - Expected: mi_render(with_expected) equals `Resolved[i64,text]`
   - Expected: mi_render(disagreeing) equals `Unresolved(conflict)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Infer a return-only variable from the expected type")
val i64t = mt_con("i64")
val textt = mt_con("text")
val none = mi_infer(["T", "U"], [mt_var("T")], mt_var("U"), [], [i64t], mt_unknown(), false)
expect(mi_render(none)).to_equal("Unresolved(no_evidence)")
val with_expected = mi_infer(["T", "U"], [mt_var("T")], mt_var("U"), [], [i64t], textt, false)
expect(mi_render(with_expected)).to_equal("Resolved[i64,text]")
val disagreeing = mi_infer(["T"], [mt_var("T")], mt_var("T"), [], [i64t], textt, false)
expect(mi_render(disagreeing)).to_equal("Unresolved(conflict)")
```

</details>

#### takes written type arguments as the instantiation and never overrides them

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Infer with written type arguments, then with evidence that disagrees
   - Expected: mi_render(written) equals `Resolved[text]`
   - Expected: mi_render(contradicted) equals `Unresolved(conflict)`
   - Expected: mi_render(wrong_count) equals `Unresolved(explicit_arity)`
   - Expected: mi_render(open) equals `Unresolved(explicit_not_closed)`
   - Expected: mi_render(named) equals `Unresolved(named_args)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-002
step("Infer with written type arguments, then with evidence that disagrees")
val i64t = mt_con("i64")
val textt = mt_con("text")
val written = mi_infer(["T"], [mt_var("T")], mt_var("T"), [textt], [mt_unknown()], mt_unknown(), false)
expect(mi_render(written)).to_equal("Resolved[text]")
val contradicted = mi_infer(["T"], [mt_var("T")], mt_var("T"), [textt], [i64t], mt_unknown(), false)
expect(mi_render(contradicted)).to_equal("Unresolved(conflict)")
val wrong_count = mi_infer(["T", "U"], [mt_var("T")], mt_var("T"), [textt], [i64t], mt_unknown(), false)
expect(mi_render(wrong_count)).to_equal("Unresolved(explicit_arity)")
val open = mi_infer(["T"], [mt_var("T")], mt_var("T"), [mt_var("U")], [i64t], mt_unknown(), false)
expect(mi_render(open)).to_equal("Unresolved(explicit_not_closed)")
val named = mi_infer(["T"], [mt_var("T")], mt_var("T"), [], [i64t], mt_unknown(), true)
expect(mi_render(named)).to_equal("Unresolved(named_args)")
```

</details>

### generic substitution model: specialization key

#### K1 is deterministic

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Encode every closed type twice and compare the key texts
   - Expected: bad equals ``
   - Expected: mk_key("m", "f", [mt_con("i64")]) equals `m1:mf1:fl1:c3:i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Encode every closed type twice and compare the key texts")
var bad = ""
for t in mu_closed_types():
    val tt: MType = t
    if mk_key("m", "f", [tt]) != mk_key("m", "f", [tt]):
        bad = mt_render(tt)
expect(bad).to_equal("")
expect(mk_key("m", "f", [mt_con("i64")])).to_equal("m1:mf1:fl1:c3:i64")
```

</details>

#### K2 the structural key separates types in the bounded universe

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Encode every pair of closed types and compare key equality with structural equality
   - Expected: bad equals ``
   - Expected: checked equals `21609)  # oracle: 147 closed types squared: every ordered pair`
   - Expected: equal_pairs equals `147)  # oracle: closed types of the universe: the closed members of the 365 (... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Encode every pair of closed types and compare key equality with structural equality")
val types = mu_closed_types()
var renders: [text] = []
for t in types:
    val tt: MType = t
    renders = renders.push(mt_key_type(tt))
var checked = 0
var equal_pairs = 0
var bad = ""
var i = 0
while i < types.len():
    val a: MType = types[i]
    var j = 0
    while j < types.len():
        val b: MType = types[j]
        val same_text = renders[i] == renders[j]
        val same_term = mt_struct_eq(a, b)
        checked = checked + 1
        if same_term:
            equal_pairs = equal_pairs + 1
        if same_text != same_term:
            bad = "{renders[i]} vs {renders[j]}"
        j = j + 1
    i = i + 1
print "K2 pairs={checked} equal={equal_pairs}"
expect(bad).to_equal("")
expect(checked).to_equal(21609)  # oracle: 147 closed types squared: every ordered pair
expect(equal_pairs).to_equal(147)  # oracle: closed types of the universe: the closed members of the 365 (no variable T or U anywhere)
```

</details>

#### K2 distinct type-argument lists, of either length, never share a key

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Encode every argument list of length one and two and look for a shared key
   - Expected: parts.len() equals `39)  # oracle: 3 closed atoms plus the closed applications used as list elements`
   - Expected: lists equals `1668)  # oracle: 147 single-argument lists + 39 x 39 = 1521 two-argument lists`
   - Expected: keys.keys().len() equals `1668)  # oracle: 147 single-argument lists + 39 x 39 = 1521 two-argument lists`
   - Expected: mk_key("a", "f", [mt_con("i64")]) == mk_key("b", "f", [mt_con("i64")]) is false
   - Expected: mk_key("a", "f", [mt_con("i64")]) == mk_key("a", "g", [mt_con("i64")]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Encode every argument list of length one and two and look for a shared key")
val singles = mu_closed_types()
val parts = mu_depth1(mu_closed_atoms())
var keys: Dict<text, bool> = {}
var lists = 0
for t in singles:
    val tt: MType = t
    keys[mk_key("m", "f", [tt])] = true
    lists = lists + 1
for a in parts:
    val x: MType = a
    for b in parts:
        val y: MType = b
        keys[mk_key("m", "f", [x, y])] = true
        lists = lists + 1
print "K2 lists={lists} keys={keys.keys().len()}"
expect(parts.len()).to_equal(39)  # oracle: 3 closed atoms plus the closed applications used as list elements
expect(lists).to_equal(1668)  # oracle: 147 single-argument lists + 39 x 39 = 1521 two-argument lists
expect(keys.keys().len()).to_equal(1668)  # oracle: 147 single-argument lists + 39 x 39 = 1521 two-argument lists
# Owner module and template name are part of the identity.
expect(mk_key("a", "f", [mt_con("i64")]) == mk_key("b", "f", [mt_con("i64")])).to_equal(false)
expect(mk_key("a", "f", [mt_con("i64")]) == mk_key("a", "g", [mt_con("i64")])).to_equal(false)
```

</details>

#### K2 constant spellings cannot alias application structure

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Encode constants spelled like application syntax next to real applications
   - Expected: mt_is_closed(literal) is true
   - Expected: mt_is_closed(applied) is true
   - Expected: mt_render(literal) equals `mt_render(applied)`
   - Expected: mt_struct_eq(literal, applied) is false
   - Expected: mk_key("m", "f", [literal]) == mk_key("m", "f", [applied]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Encode constants spelled like application syntax next to real applications")
val literal = mt_con("Box<i64>")
val applied = mt_app("Box", [mt_con("i64")])
expect(mt_is_closed(literal)).to_equal(true)
expect(mt_is_closed(applied)).to_equal(true)
expect(mt_render(literal)).to_equal(mt_render(applied))
expect(mt_struct_eq(literal, applied)).to_equal(false)
expect(mk_key("m", "f", [literal]) == mk_key("m", "f", [applied])).to_equal(false)
```

</details>

#### K2 argument boundaries and application arity are distinct

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Encode argument lists that differ only in element boundaries or arity
   - Expected: mt_render(single) equals `mt_render(pair)`
   - Expected: mt_key_type(single) == mt_key_type(pair) is false
   - Expected: mt_key_types([mt_con("i64,bool")]) == mt_key_types([mt_con("i64"), mt_con("bool")]) is false
   - Expected: mt_key_type(mt_con("Zero<>")) == mt_key_type(mt_app("Zero", [])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Encode argument lists that differ only in element boundaries or arity")
val single = mt_app("Pair", [mt_con("i64,bool")])
val pair = mt_app("Pair", [mt_con("i64"), mt_con("bool")])
expect(mt_render(single)).to_equal(mt_render(pair))
expect(mt_key_type(single) == mt_key_type(pair)).to_equal(false)
expect(mt_key_types([mt_con("i64,bool")]) == mt_key_types([mt_con("i64"), mt_con("bool")])).to_equal(false)
expect(mt_key_type(mt_con("Zero<>")) == mt_key_type(mt_app("Zero", []))).to_equal(false)
```

</details>

#### K2 owner and function delimiters cannot alias another identity

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Encode owner and function names that contain the key delimiters
   - Expected: mk_key("a::b", "c", []) == mk_key("a", "b::c", []) is false
   - Expected: mk_key("a", "f$[i64]", []) == mk_key("a", "f", [mt_con("i64")]) is false
   - Expected: mk_key("", "a", []) == mk_key("a", "", []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Encode owner and function names that contain the key delimiters")
expect(mk_key("a::b", "c", []) == mk_key("a", "b::c", [])).to_equal(false)
expect(mk_key("a", "f$[i64]", []) == mk_key("a", "f", [mt_con("i64")])).to_equal(false)
expect(mk_key("", "a", []) == mk_key("a", "", [])).to_equal(false)
```

</details>

#### K2 tags preserve variable constant and application distinctions

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Encode a variable, a constant and an application with the same name
   - Expected: mt_key_type(mt_var("T")) == mt_key_type(mt_con("'T")) is false
   - Expected: mt_key_type(mt_con("")) == mt_key_type(mt_app("", [])) is false
   - Expected: mt_key_type(mt_con("c3:i64")) == mt_key_type(mt_con("i64")) is false
   - Expected: mt_key_type(mt_app("名:<>", [mt_con("值,:$")])) == mt_key_type(mt_app("名", [mt_con("<>值,:$")])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Encode a variable, a constant and an application with the same name")
expect(mt_key_type(mt_var("T")) == mt_key_type(mt_con("'T"))).to_equal(false)
expect(mt_key_type(mt_con("")) == mt_key_type(mt_app("", []))).to_equal(false)
expect(mt_key_type(mt_con("c3:i64")) == mt_key_type(mt_con("i64"))).to_equal(false)
expect(mt_key_type(mt_app("名:<>", [mt_con("值,:$")])) == mt_key_type(mt_app("名", [mt_con("<>值,:$")]))).to_equal(false)
```

</details>

### generic substitution model: key decoding (TLDR template fields)

#### K3 decodes every type key back to the same type

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Encode every type, decode the key and compare with the original
   - Expected: back.ok is true
   - Expected: mt_struct_eq(back.t, tt) is true
   - Expected: n equals `365)  # oracle: the 95 depth-1 types + 3 unary constructors x the 90 non-atom... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Encode every type, decode the key and compare with the original")
var n = 0
for t in mu_types():
    val tt: MType = t
    val back = mt_from_key(mt_key_type(tt))
    expect(back.ok).to_equal(true)
    expect(mt_struct_eq(back.t, tt)).to_equal(true)
    n = n + 1
expect(n).to_equal(365)  # oracle: the 95 depth-1 types + 3 unary constructors x the 90 non-atom depth-1 types = 95 + 270
```

</details>

#### K3 rejects malformed and trailing key text

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Decode truncated, mistyped and trailing key text
   - Expected: mt_from_key("").ok is false
   - Expected: mt_from_key("c3:i6").ok is false
   - Expected: mt_from_key("c3:i64x").ok is false
   - Expected: mt_from_key("a5:Arrayl2:c3:i64").ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GSUBST-003
step("Decode truncated, mistyped and trailing key text")
expect(mt_from_key("").ok).to_equal(false)
expect(mt_from_key("c3:i6").ok).to_equal(false)
expect(mt_from_key("c3:i64x").ok).to_equal(false)
expect(mt_from_key("a5:Arrayl2:c3:i64").ok).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GSUBST-001`
- `REQ-GSUBST-002`
- `REQ-GSUBST-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `538bfe04dbfe3be43cf6e4a058cd197b90d1a42ab7dde0f4296fd01878d186a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `538bfe04dbfe3be43cf6e4a058cd197b90d1a42ab7dde0f4296fd01878d186a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `538bfe04dbfe3be43cf6e4a058cd197b90d1a42ab7dde0f4296fd01878d186a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: 01_unit/compiler/30.types/generic_subst/generic_subst_model_laws_spec.spl
mirror: doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_laws_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/30.types/generic_subst/generic_subst_model_laws_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
