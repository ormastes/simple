# native-build of an entry whose directory path contains a dot links without `__simple_main`

- Status: FIX IMPLEMENTED, VERIFICATION PENDING (source fix + spec landed in PR #4033, merge ab7088bc82c; workaround in scripts/check/check-stage-binaries-runnable.shs stays until a stage3 rebuild verifies native-build under a dotted dir)
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P2

## Observation

Pure-Simple bootstrap CLI (diagnostic Stage 2 relink `s2diag17`, sha256
61f1f47a37bc..., `--version` = `simple-bootstrap 1.0.0-rc.1`), run from a
repo root, on the three-line hello world used by the stage-binary runnable
gate (`fn main() -> i64: print "hi"; 0`):

| source path | native-build rc |
|---|---|
| `<tmp>/nodot1/hello.spl` | 0 (binary prints `hi`) |
| `<tmp>/a-b/hello.spl` | 0 |
| `<tmp>/dot.1/hello.spl` | 1 |
| `<tmp>/g.1/sub/hello.spl` | 1 (dot in a grandparent) |

The failing runs end with

```
error: in-process native-build: LLVM native linking failed: Linking failed:
cc linking failed: ld.lld: error: undefined symbol: __simple_main
>>> referenced by simple_entry.c
```

So the entry module's `main` is not emitted as `__simple_main` when any
directory component of the source path contains a `.`. The likely cause is a
module name derived from the path and split on `.`, but this has not been
traced in the source.

## Impact

`check-stage-binaries-runnable.shs` probed from `$TMPROOT/probe.N` under a
`mktemp` directory named `<name>.XXXXXX`, so every pure-Simple bootstrap
binary FAILed its `native-build` probe even when it works.

## Workaround

The gate's probe and temp directories now use `_` instead of `.`
(`# @workaround bug=native_build_entry_main_undefined_when_source_path_has_dot_2026_10_20`).
A `TMPDIR` that itself contains a dot still reproduces it.

## Root-aware source-only repair proposal (2026-10-21, cycle 2)

Status remains OPEN pending qualified-producer execution and higher review.
At source revision `471ccc083397fb17812ba43459b233e7cd3dfde2`, entry-closure
alias loading puts `_driver_canonical_module_name(physical)` first. That
canonicalizer drops all-digit dotted segments, including the `1` in external
`dot.1` and `g.1` paths, while LLVM's requested entry derivation preserves it.
The primary source then fails the actual `llvm_module_is_native_entry`
comparison, and neighboring `dot.1` / `dot.2` identities collide. This is a
source-level mismatch for numeric-dot paths; no every-nonnumeric-dot claim
is established.

Independent cycle-1 review rejected lexical `/src/` or `/examples/` substring
classification: an external `/tmp/foreign/src/dot.1/hello.spl` is still
external, even though shared logical naming strips its host prefix. The
cycle-2 proposal returns physical name and repository-membership proof
together from `_driver_physical_module_identity`, using the existing resolved
path, admitted/current root, root-boundary and repository-relative source
checks. Alias folding consumes that same proof, retaining repository tier
aliases while preserving external shared identities. No lexical substring
is newly treated as evidence of physical repository membership.

The tests were authored before the source change and call actual production
alias APIs and LLVM's entry predicate with negative neighbors. New fixtures
cover real external nested `src` and `examples` paths, distinct `dot.1` and
`dot.2`, and actual existing repository sources in relative/absolute forms.
Every compiler, test, docgen, link and runtime check remains UNRUN under the
source-only protocol. Both existing stage-binary gate workaround tags and
consumer spellings remain unchanged. This proposal requires higher review;
it is not production, bootstrap or Phase3 PASS.

## Resolution (2026-11-05)

PR #4033 (`fix(compiler): preserve external dotted source entry identity`,
merge ab7088bc82c) changed `src/compiler/80.driver/driver_source_loading.spl`
and landed `test/01_unit/compiler/driver/dotted_source_entry_identity_spec.spl`.
Current `driver_entry_closure_core.spl` `_driver_physical_module_identity`
returns (name, repository_member) and only repository sources are
canonicalized (digit-tier dropping), so external `dot.1` paths keep their
identity. Verification pending: native-build of the repro under `<tmp>/dot.1/`
with a rebuilt stage3; then remove the two `@workaround` tags in
`check-stage-binaries-runnable.shs`.

## Fix (2026-11-13) — Windows membership + neighbour-safe entry predicate

On Windows, `dotted_source_entry_identity_spec` passed only 5 of 9 scenarios on the seed. There were two causes:

1. `_driver_physical_module_identity` (`driver_entry_closure_core.spl`) tested
   `resolved.starts_with(root + "/")` on raw `rt_path_absolute` output, which
   uses `\` separators on Windows. No repository source was ever proven a member,
   so `compiler.10.frontend...` was never folded. Paths are now compared on `/`
   separators: the `\?\` prefix is stripped, the root is matched
   case-insensitively, and the case of the relative remainder is kept.
2. `llvm_module_is_native_entry` folded BOTH sides, so `dot.1/hello.spl` and
   `dot.2/hello.spl` became the same native entry. This was not specific to
   Windows. It now matches when the names are equal or when one side is the
   canonical fold of the other.

Seed: 9/9 passed. Neighbour specs `driver_source_loading_spec` (5 failures) and
`entry_closure_authored_path_spec` (1 failure) fail identically with and without
this change. `module_path_naming_scv_root_snapshot_spec` passed 7/7. The native-build
repro under `<tmp>/dot.1/` still needs a rebuilt producer.
