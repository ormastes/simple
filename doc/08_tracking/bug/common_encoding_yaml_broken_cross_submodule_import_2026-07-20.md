# `src/lib/common/encoding/yaml.spl` has a broken cross-submodule import — repo-wide, reproduces under both `run` and `test`

**Date:** 2026-07-20
**Severity:** medium (product source bug, not test-only — affects every real
caller of `std.common.encoding.yaml`, not just this spec)
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
one-line change, not inside the assigned test-cluster dir)
**Found by:** whole-suite `test/unit/` triage campaign, `lib/common` cluster

## Symptom

`test/unit/lib/common/encoding/yaml_spec.spl` fails 22 of 27 examples (after
fixing an unrelated dead import in the spec itself, see below) with:

```
semantic: function `yaml_parse_block` not found
```

## Root cause

`src/lib/common/encoding/yaml.spl` line 34 imports:

```simple
use std.common.yaml.{yaml_parse_flow_sequence, yaml_parse_flow_mapping,
    yaml_parse_block, yaml_parse_scalar,
    yaml_get_scalar_content, yaml_get_sequence_items, yaml_get_mapping_pairs,
    yaml_null, yaml_needs_quotes}
```

`std.common.yaml` (i.e. a file/`__init__.spl` directly at
`src/lib/common/yaml/`) does not exist — there is no barrel/mod file at that
level. The nine imported symbols are actually split across three sibling
submodules:
- `std.common.yaml.parse` (`src/lib/common/yaml/parse.spl`):
  `yaml_parse_flow_sequence`, `yaml_parse_flow_mapping`, `yaml_parse_block`,
  `yaml_parse_scalar`
- `std.common.yaml.types` (`src/lib/common/yaml/types.spl`):
  `yaml_get_scalar_content`, `yaml_get_sequence_items`,
  `yaml_get_mapping_pairs`, `yaml_null`
- `std.common.yaml.utilities` (`src/lib/common/yaml/utilities.spl`):
  `yaml_needs_quotes`

**Confirmed NOT a test-evaluator-only landmine** (the known
`bin/simple test` vs `bin/simple run` cross-module free-symbol divergence,
see `generic_class_static_method_unresolved_under_test_2026-07-20.md`):
reproduces identically under `bin/simple run` on a minimal repro:

```simple
use std.common.encoding.yaml.{yaml_parse_mapping, yaml_get}

fn main():
    val content = "name: Alice\nage: 30\n"
    val entries = yaml_parse_mapping(content)
    print "count={entries.length()}"
    print "name={yaml_get(entries, \"name\")}"
```

```
error[E1002]: function `yaml_null` not found
  = help: check the function name or import the module that defines it
```

(`run` fails one step earlier than `test` did, on `yaml_null` instead of
`yaml_parse_block`, because `yaml_parse` calls `yaml_null()` before reaching
the `yaml_parse_block` branch — same root cause, same broken import line.)

This means `std.common.encoding.yaml`'s public API (`yaml_parse`,
`yaml_parse_mapping`, `yaml_get`, `yaml_get_list`, `yaml_encode_mapping`,
`yaml_encode_scalar`) is currently non-functional for **any** caller, not
just this test.

## Fix needed (not attempted — out of scope)

Split the single broken `use std.common.yaml.{...}` import in
`src/lib/common/encoding/yaml.spl` into three correctly-scoped imports
(`std.common.yaml.parse`, `std.common.yaml.types`,
`std.common.yaml.utilities`, per the symbol mapping above). Pure import-path
correction, no logic change — but it touches product source outside the
test-triage cluster dir and is not literally one line, so left for whoever
owns `src/lib/common/**`.

## Secondary, separate stale-test finding (not kept — see below): spec's own dead import

`test/unit/lib/common/encoding/yaml_spec.spl` separately has its own dead
import: `use std.common.yaml.{yaml_get_scalar_content, is_yaml_null, ...}` —
missing the `.types` segment; the correct path is `std.common.yaml.types`.
Verified in isolation that fixing just this line (pure STALE-TEST
import-path rename) unblocks the spec from "no examples executed" /
module-resolution error to 27 examples actually running (5 pass, 22 fail —
all 22 via the `yaml_parse_block`/source-level blocker documented above).
Since the file cannot reach green either way (blocked by the source bug),
this one-line spec fix was **reverted** rather than left half-applied, to
keep the working tree clean of non-green edits per triage convention —
whoever fixes the source-level import above should also apply this
companion one-liner in the spec (`std.common.yaml` →
`std.common.yaml.types` on the `is_yaml_null`/`is_yaml_boolean`/
`is_yaml_sequence`/`is_yaml_mapping`/`yaml_get_sequence_items`/
`yaml_get_mapping_pairs`/`yaml_get_scalar_content` import line) to reach
green.

## Affected

- `test/unit/lib/common/encoding/yaml_spec.spl` — currently fails at import
  resolution (dead `std.common.yaml` path, see above); after that companion
  fix, 22 of 27 examples would still fail via this source-level blocker.

## ALREADY_FIXED (the documented import) 2026-08-17 — but a SECOND defect kept the API dead

The documented root cause is gone. `src/lib/common/encoding/yaml.spl:34-38`
now reads three correctly-scoped imports, exactly the split this doc asked for:

```simple
use std.common.yaml.parse.{yaml_parse_flow_sequence, yaml_parse_flow_mapping,
    yaml_parse_block, yaml_parse_scalar}
use std.common.yaml.types.{yaml_get_scalar_content, yaml_get_sequence_items,
    yaml_get_mapping_pairs, yaml_null, is_yaml_scalar}
use std.common.yaml.utilities.{yaml_needs_quotes}
```

The doc's own minimal repro no longer raises `E1002 function 'yaml_null' not
found`. The companion spec one-liner (`std.common.yaml` ->
`std.common.yaml.types`) is likewise already applied in
`test/01_unit/lib/common/encoding/yaml_spec.spl`.

### But the symptom this doc opened on ("non-functional for ANY caller") still reproduced

Same repro, after the import fix:

```
count=0
name=
```

i.e. `yaml_parse_mapping("name: Alice\nage: 30\n")` returned **0** entries.
Narrowed with `bin/simple run`:

```
yaml_parse(content).0            -> nil     (expected "mapping")
yaml_parse_block(content.trim()).0 -> nil   (expected "mapping")
```

Minimal, yaml-free reduction:

```simple
fn mk()  -> any:          ("mapping", 7)   # caller reads .0 -> "mapping"
fn mk2():                 ("mapping", 7)   # caller reads .0 -> nil   <-- BUG
fn mk3() -> (text, any):  ("mapping", 7)   # caller reads .0 -> "mapping"
```

A function that returns a tuple but carries **no return-type annotation**
loses its tuple shape at the call site; the caller's `.0` reads back `nil`.
All six yaml node constructors in `src/lib/common/yaml/types.spl:9-25`
(`yaml_null`, `yaml_boolean`, `yaml_number`, `yaml_string`, `yaml_sequence`,
`yaml_mapping`) were unannotated, and every yaml value is a tagged
`("tag", payload)` tuple — so the tag was erased for every consumer downstream.

### Fix applied

`src/lib/common/yaml/types.spl:9-25` — annotated all six constructors
`-> (text, any)`. No logic change. After the fix, the doc's repro prints
`count=2 / name=Alice`, and `yaml_parse(...).0` / `yaml_parse_block(...).0`
both return `"mapping"`.

Specs added:
- `test/01_unit/lib/common/encoding/yaml_public_api_functional_spec.spl`
  (reproducing — `Results: 5 total, 5 passed, 0 failed`)
- `test/01_unit/lib/common/yaml_node_constructor_tag_spec.spl`
  (detection, generalizes to every constructor + every parser that forwards one)

### Still open, separate, NOT this bug

- `yaml_parse` has two co-compiled definitions with differing signatures
  (`std.common.encoding.yaml` `-> (text, any)` vs `std.common.yaml.parse`
  `-> any`); the compiler emits
  `compiler_cross_module_private_symbol_collision`. Harmless today (both
  return the same tagged tuple) but it is a real ambiguity.
- `yaml_parse_block` sends an inline flow value (`tags: [a, b, c]`) to
  `yaml_parse_scalar`, so an inline flow sequence as a mapping VALUE parses as
  a string. Block-style nested sequences work. Pre-existing feature gap.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**NOT-REPRODUCED — the missing-barrel theory is wrong.** Probe
(`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`, rc=0) importing
`std.common.encoding.yaml.{yaml_parse_mapping, yaml_get}` and parsing
`"a: 1\nb: hello\n"`:

```
count=2
b=hello
```

No `use-warning` for any `std.common.yaml.*` name appeared in the run output.
`src/lib/common/yaml/__init__.spl` is indeed absent — but so is
`src/lib/common/encoding/__init__.spl`, and that package resolves fine: naming a
submodule directly (`use std.common.yaml.parse.{...}` at
`src/lib/common/encoding/yaml.spl:35-39`) does not require a barrel in this
resolver. The absence of `__init__.spl` is therefore not a defect. Recommend
CLOSED.
