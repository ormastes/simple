# Vacuous-spec census: 905 specs and ~14,500 test cases are disabled behind fake-green placeholders

**Lane PLACEHOLDER1**, run inline by the orchestrator after the subagent was
halted on an API quota. Method is shell counting over `test/01_unit/**` and
`test/unit/**`; every number below is reproducible with the commands recorded
here.

## The pattern

Lane QSK1 needed specs to validate a 31-file rename and found all five of its
"relevant" specs looked like this:

```
describe "Builder Api":
    it "skipped":
        val pending_reason = "pre-existing test failures - functions/imports not available"
        expect(pending_reason.len()).to_be_greater_than(0)

# # Builder API Tests - Fluent Block Building
# use compiler.blocks.builder.{BlockBuilder}
# describe "BlockBuilder - Construction":
#     it "builds an empty block":
# ...470 more commented-out lines
```

The real test file is **commented out wholesale** and replaced by one assertion
that cannot fail — `expect(pending_reason.len()).to_be_greater_than(0)` is true
by construction. The suite reports `1 total, 1 passed, 0 failed` and goes green.

## Counts

| Shape | Count |
|---|---|
| Spec files scanned (`test/01_unit` + `test/unit`) | 16,253 |
| Files containing `pending_reason` | 1,154 (**7.1%**) |
| Files containing `it "skipped"` | 1,141 |
| **Unique specs after mirror-dedup** | **905** |
| Files with commented-out `describe` blocks | 699 |
| **Commented-out `it "..."` test cases** | **14,535** |
| Files with zero `expect` anywhere | 238 |

`test/unit/` is a known 884-file-diverged mirror of `test/01_unit/`, so the
deduped **905 specs / ~14,500 cases** is the honest figure.

By area (deduped): lib 317, compiler 240, app 225, compiler_core 91, std 18,
compiler_shared 8, os/memleak/bugs 6.  **331 of the 905 guard compiler internals.**

## The reasons are hidden failures, not pending features

This is the finding. Distribution of `pending_reason` strings:

| n | reason |
|---|---|
| 459 | `pre-existing test failures - functions/imports not available` |
| 103 | `imports compiler modules - causes OOM via numbered directory resolution` |
| 98 | `assertion failures - runtime behavior differs in interpreter mode` |
| 31 | `function 'tensor_from_data' not found in interpreter runtime` |
| 24 | `method 'randn_1d' not found on 'dict'` |
| 16 | `module 'compiler_shared.diagnostics' not resolvable` |
| 12 | `variable 'indent_level' not found - struct field access or scope issue` |
| 12 | `std.exp.* path unresolvable from nogc_sync_mut/src/` |
| 12 | `function 'tensor_randn' not found in interpreter runtime` |
| 11 each | `Conv2d__create` / `MaxPool2d__create` not found in interpreter runtime |
| 10 | `timeout - module loading exceeds 60s` |

Not one of the top reasons is "this feature isn't built yet." Every one is a
**symptom of a real defect** — and several name defects this repo has already
documented separately: interpreter-vs-native divergence, dict method dispatch,
module-resolution OOM, the 60s timeout.

The repo rule is *"NEVER skip failing tests without approval."* 905 specs were
skipped, and the failure reason was preserved in a string as the only trace.

## Verification attempted

Re-enabled `builder_api_spec.spl` by uncommenting its body into a scratch spec
and running it: `Results: 1 total, 0 passed, 1 failed`. The underlying breakage
is still present, so these are not stale placeholders guarding already-fixed
code. **Caveat, stated because it matters:** the uncomment was a crude `sed`, and
only 1 of the file's many `describe` blocks registered — so this shows the spec
does not trivially pass, not that all 14,535 cases still fail. A rigorous
re-enable pass is a separate lane.

## Why no bulk repair was done

Re-enabling 905 specs would surface an unknown but large number of real failures
at once. That is the honest state of the tree, but flipping it in one change is a
call for the repo owner, not a lane — and this repo explicitly forbids both
skipping failing tests *and* mass-changing test state without approval.

## Recommendation

1. **Stop the bleeding:** treat `pending_reason` as a lint-detectable anti-pattern
   so no new ones land silently.
2. **Re-enable by cluster, not by file.** The 459 + 98 + 103 groups share root
   causes; fixing one defect likely revives dozens of specs at once. Start with
   the 103 OOM-on-numbered-directory-resolution group, which is one bug.
3. **Report the real number.** Any statement of suite health that counts these
   905 as passing is overstated by ~14,500 cases.
