# `src/lib/common/encoding/yaml.spl` has a broken cross-submodule import — repo-wide, reproduces under both `run` and `test`

**Date:** 2026-07-20
**Severity:** medium (product source bug, not test-only — affects every real
caller of `std.common.encoding.yaml`, not just this spec)
**Status:** open — needs a source fix, out of test-triage scope (not a
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
