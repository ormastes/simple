# clean_spec

> Purpose: Prove that clean: normalize_path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# clean_spec

Purpose: Prove that clean: normalize_path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/clean/clean_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that clean: normalize_path.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### clean: normalize_path

#### resolves dot-dot and double slashes lexically

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves dot-dot and double slashes lexically
- Verify: resolves dot-dot and double slashes lexically
   - Expected: r equals `/repo/build/sub/x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resolves dot-dot and double slashes lexically")
step("Verify: resolves dot-dot and double slashes lexically")
# @req: REQ-APP-CLEAN-001
val r = normalize_path("/repo", "build/../build//sub/./x")
expect(r).to_equal("/repo/build/sub/x")
```

</details>

#### keeps absolute paths absolute

- keeps absolute paths absolute
- Verify: keeps absolute paths absolute
   - Expected: normalize_path("/repo", "/tmp/simple_x") equals `/tmp/simple_x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps absolute paths absolute")
step("Verify: keeps absolute paths absolute")
expect(normalize_path("/repo", "/tmp/simple_x")).to_equal("/tmp/simple_x")
```

</details>

#### cannot escape above root via dot-dot

- cannot escape above root via dot-dot
- Verify: cannot escape above root via dot-dot
   - Expected: normalize_path("/repo", "../../..") equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("cannot escape above root via dot-dot")
step("Verify: cannot escape above root via dot-dot")
expect(normalize_path("/repo", "../../..")).to_equal("/")
```

</details>

### clean: never-touch list

#### rejects .spipe, bin/release, doc, .git, .jj

- rejects .spipe, bin/release, doc, .git, .jj
- Verify: rejects .spipe, bin/release, doc, .git, .jj
   - Expected: is_never_touch(".spipe/lane.md") is true
   - Expected: is_never_touch("bin/release/x86_64-unknown-linux-gnu/simple") is true
   - Expected: is_never_touch("doc/08_tracking/test/test_db.sdn") is true
   - Expected: is_never_touch(".git/objects/aa/bb") is true
   - Expected: is_never_touch(".jj/repo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects .spipe, bin/release, doc, .git, .jj")
step("Verify: rejects .spipe, bin/release, doc, .git, .jj")
expect(is_never_touch(".spipe/lane.md")).to_equal(true)
expect(is_never_touch("bin/release/x86_64-unknown-linux-gnu/simple")).to_equal(true)
expect(is_never_touch("doc/08_tracking/test/test_db.sdn")).to_equal(true)
expect(is_never_touch(".git/objects/aa/bb")).to_equal(true)
expect(is_never_touch(".jj/repo")).to_equal(true)
```

</details>

#### rejects src except the cargo target carve-out

- rejects src except the cargo target carve-out
- Verify: rejects src except the cargo target carve-out
   - Expected: is_never_touch("src/lib/common/text.spl") is true
   - Expected: is_never_touch("src/compiler_rust/target/debug") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects src except the cargo target carve-out")
step("Verify: rejects src except the cargo target carve-out")
expect(is_never_touch("src/lib/common/text.spl")).to_equal(true)
expect(is_never_touch("src/compiler_rust/target/debug")).to_equal(false)
```

</details>

#### does not confuse doc with a doc-prefixed sibling

- does not confuse doc with a doc-prefixed sibling
- Verify: does not confuse doc with a doc-prefixed sibling
   - Expected: is_never_touch("dockerfiles/x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not confuse doc with a doc-prefixed sibling")
step("Verify: does not confuse doc with a doc-prefixed sibling")
expect(is_never_touch("dockerfiles/x")).to_equal(false)
```

</details>

#### allows build entries

- allows build entries
- Verify: allows build entries
   - Expected: is_never_touch("build/bootstrap") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allows build entries")
step("Verify: allows build entries")
expect(is_never_touch("build/bootstrap")).to_equal(false)
```

</details>

### clean: containment gate

#### refuses a never-touch path even when inside an allowed root

- refuses a never-touch path even when inside an allowed root
- Verify: refuses a never-touch path even when inside an allowed root
   - Expected: can_delete_with_roots(".spipe/lane.md", FIXTURE_ROOT, roots) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses a never-touch path even when inside an allowed root")
step("Verify: refuses a never-touch path even when inside an allowed root")
var roots: [text] = []
roots.push(FIXTURE_ROOT)
expect(can_delete_with_roots(".spipe/lane.md", FIXTURE_ROOT, roots)).to_equal(false)
```

</details>

#### refuses paths outside every allowed root

- refuses paths outside every allowed root
- Verify: refuses paths outside every allowed root
   - Expected: can_delete_with_roots("/etc/passwd", FIXTURE_ROOT, roots) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses paths outside every allowed root")
step("Verify: refuses paths outside every allowed root")
var roots: [text] = []
roots.push(FIXTURE_ROOT + "/build")
expect(can_delete_with_roots("/etc/passwd", FIXTURE_ROOT, roots)).to_equal(false)
```

</details>

#### refuses dot-dot escape out of an allowed root

- refuses dot-dot escape out of an allowed root
- Verify: refuses dot-dot escape out of an allowed root
   - Expected: can_delete_with_roots("build/../.spipe/lane.md", FIXTURE_ROOT, roots) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses dot-dot escape out of an allowed root")
step("Verify: refuses dot-dot escape out of an allowed root")
var roots: [text] = []
roots.push(FIXTURE_ROOT + "/build")
expect(can_delete_with_roots("build/../.spipe/lane.md", FIXTURE_ROOT, roots)).to_equal(false)
```

</details>

#### accepts a path inside an allowed root

- accepts a path inside an allowed root
- Verify: accepts a path inside an allowed root
   - Expected: can_delete_with_roots("build/old_campaign", FIXTURE_ROOT, roots) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts a path inside an allowed root")
step("Verify: accepts a path inside an allowed root")
var roots: [text] = []
roots.push(FIXTURE_ROOT + "/build")
expect(can_delete_with_roots("build/old_campaign", FIXTURE_ROOT, roots)).to_equal(true)
```

</details>

### clean: dry-run

#### lists but deletes nothing

- lists but deletes nothing
- Verify: lists but deletes nothing
   - Expected: _setup_fixture() is true
   - Expected: n equals `0`
   - Expected: file_exists(FIXTURE_ROOT + "/build/old_campaign/artifact.bin") is true
   - Expected: file_exists(FIXTURE_ROOT + "/build/loose.log") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lists but deletes nothing")
step("Verify: lists but deletes nothing")
expect(_setup_fixture()).to_equal(true)
var roots: [text] = []
roots.push(FIXTURE_ROOT + "/build")
var paths: [text] = []
paths.push("build/old_campaign")
paths.push("build/loose.log")
val n = delete_paths(paths, FIXTURE_ROOT, roots, true)
expect(n).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(file_exists(FIXTURE_ROOT + "/build/old_campaign/artifact.bin")).to_equal(true)
expect(file_exists(FIXTURE_ROOT + "/build/loose.log")).to_equal(true)
```

</details>

### clean: real delete honors never-touch

#### deletes allowed entries but never the explicitly-passed never-touch path

- deletes allowed entries but never the explicitly-passed never-touch path
- Verify: deletes allowed entries but never the explicitly-passed never-touch path
   - Expected: _setup_fixture() is true
   - Expected: n equals `1`
   - Expected: file_exists(FIXTURE_ROOT + "/build/loose.log") is false
   - Expected: file_exists(FIXTURE_ROOT + "/.spipe/lane.md") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("deletes allowed entries but never the explicitly-passed never-touch path")
step("Verify: deletes allowed entries but never the explicitly-passed never-touch path")
expect(_setup_fixture()).to_equal(true)
var roots: [text] = []
roots.push(FIXTURE_ROOT + "/build")
roots.push(FIXTURE_ROOT + "/.spipe")
var paths: [text] = []
paths.push("build/loose.log")
paths.push(".spipe/lane.md")
val n = delete_paths(paths, FIXTURE_ROOT, roots, false)
expect(n).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(file_exists(FIXTURE_ROOT + "/build/loose.log")).to_equal(false)
expect(file_exists(FIXTURE_ROOT + "/.spipe/lane.md")).to_equal(true)
```

</details>

### clean: LRU selection

#### deletes oldest first until at or under target

- deletes oldest first until at or under target
- Verify: deletes oldest first until at or under target
   - Expected: picked.len() equals `2`
   - Expected: picked[0] equals `1`
   - Expected: picked[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("deletes oldest first until at or under target")
step("Verify: deletes oldest first until at or under target")
var mtimes: [i64] = []
mtimes.push(30)
mtimes.push(10)
mtimes.push(20)
var sizes: [i64] = []
sizes.push(100)
sizes.push(100)
sizes.push(100)
val picked = lru_delete_set(mtimes, sizes, 300, 150)
expect(picked.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(picked[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(picked[1]).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### picks nothing when already under target

- picks nothing when already under target
- Verify: picks nothing when already under target
   - Expected: picked.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("picks nothing when already under target")
step("Verify: picks nothing when already under target")
var mtimes: [i64] = []
mtimes.push(10)
var sizes: [i64] = []
sizes.push(100)
val picked = lru_delete_set(mtimes, sizes, 100, 200)
expect(picked.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### stops when entries run out

- stops when entries run out
- Verify: stops when entries run out
   - Expected: picked.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("stops when entries run out")
step("Verify: stops when entries run out")
var mtimes: [i64] = []
mtimes.push(10)
var sizes: [i64] = []
sizes.push(1)
val picked = lru_delete_set(mtimes, sizes, 1000, 10)
expect(picked.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### clean: threshold math

#### defaults to 20 GB cap and rejects garbage

- defaults to 20 GB cap and rejects garbage
- Verify: defaults to 20 GB cap and rejects garbage
   - Expected: parse_cap_gb("") equals `20`
   - Expected: parse_cap_gb("banana") equals `20`
   - Expected: parse_cap_gb("-3") equals `20`
   - Expected: parse_cap_gb("5") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults to 20 GB cap and rejects garbage")
step("Verify: defaults to 20 GB cap and rejects garbage")
expect(parse_cap_gb("")).to_equal(20)
expect(parse_cap_gb("banana")).to_equal(20)
expect(parse_cap_gb("-3")).to_equal(20)
expect(parse_cap_gb("5")).to_equal(5)
```

</details>

#### cleans down to 80 percent of the cap

- cleans down to 80 percent of the cap
- Verify: cleans down to 80 percent of the cap
   - Expected: auto_clean_target_bytes(10737418240) equals `8589934592`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("cleans down to 80 percent of the cap")
step("Verify: cleans down to 80 percent of the cap")
expect(auto_clean_target_bytes(10737418240)).to_equal(8589934592)  # oracle: 8589934592 — named expected value from the requirement
```

</details>

### clean: auto mode env opt-in

#### is enabled ONLY by SIMPLE_AUTO_CLEAN=1

- is enabled ONLY by SIMPLE_AUTO_CLEAN=1
- Verify: is enabled ONLY by SIMPLE_AUTO_CLEAN=1
   - Expected: auto_clean_enabled("0") is false
   - Expected: auto_clean_enabled("") is false
   - Expected: auto_clean_enabled("1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is enabled ONLY by SIMPLE_AUTO_CLEAN=1")
step("Verify: is enabled ONLY by SIMPLE_AUTO_CLEAN=1")
# Opt-in: the SAFE class holds high-rebuild-cost state (bootstrap
# artifacts), so an on-by-default sweep is a foot-gun; unset/""/0
# all disable.
expect(auto_clean_enabled("0")).to_equal(false)
expect(auto_clean_enabled("")).to_equal(false)
expect(auto_clean_enabled("1")).to_equal(true)
```

</details>

#### returns immediately when not opted in

- returns immediately when not opted in
- Verify: returns immediately when not opted in
   - Expected: auto_clean_on_build_start() equals `0`
   - Expected: auto_clean_enabled("0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns immediately when not opted in")
step("Verify: returns immediately when not opted in")
env_set("SIMPLE_AUTO_CLEAN", "0")
# Only call the real entry point when the env write verifiably took
# effect — otherwise it could sweep the real repo caches from a test.
if env_get("SIMPLE_AUTO_CLEAN") == "0":
    expect(auto_clean_on_build_start()).to_equal(0)  # oracle: 0 — named expected value from the requirement
else:
    expect(auto_clean_enabled("0")).to_equal(false)
```

</details>

### clean: fixture teardown

#### removes its own fixture

- removes its own fixture
- Verify: removes its own fixture
   - Expected: file_exists(FIXTURE_ROOT + "/build/loose.log") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("removes its own fixture")
step("Verify: removes its own fixture")
dir_remove(FIXTURE_ROOT, true)
expect(file_exists(FIXTURE_ROOT + "/build/loose.log")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-CLEAN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a82c2107ce838a433cc51ba52223e48babf359364c17a05db5a95b2c320774b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a82c2107ce838a433cc51ba52223e48babf359364c17a05db5a95b2c320774b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a82c2107ce838a433cc51ba52223e48babf359364c17a05db5a95b2c320774b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/clean/clean_spec.spl
mirror: doc/06_spec/01_unit/app/clean/clean_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/clean/clean_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/clean/clean_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/clean/clean_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/clean/clean_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves dot-dot and double slashes lexically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/clean/clean_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps absolute paths absolute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/clean/clean_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cannot escape above root via dot-dot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
