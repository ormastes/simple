# Four `treesitter_*_real_spec.spl` files report 151/151 green while 150 of 151 examples are the literal statement `expect true`

- **Date:** 2026-08-06
- **Status:** OPEN
- **Severity:** High — a `_real_`-named spec cluster over the compiler lexer/parser API contributes
  151 "passing" examples and cannot fail.
- **Area:** spec vacuity (compiler / parser)
- **Evidence binary:** `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap
  **seed**; emits the "this Rust-built Simple binary is a bootstrap seed only" banner). Engine:
  default `simple test` path. Each spec run individually, sequentially — no directory sweeps.

## The vacuity (fully proven)

Four specs import `std.parser.treesitter`. Their headers state they "use the real Lexer struct,
not mocks". Measured verdict lines, one file per `bin/simple test` invocation:

| Spec | verdict line | `expect true` / total `expect` |
|------|--------------|-------------------------------|
| `test/01_unit/compiler/parser/treesitter_lexer_real_spec.spl` | `declared>=39 executed=39 passed=39 failed=0 dropped=0` | 38 / 39 |
| `test/01_unit/compiler/parser/treesitter_parser_real_spec.spl` | `declared>=41 executed=41 passed=41 failed=0 dropped=0` | 41 / 41 |
| `test/01_unit/compiler/parser/treesitter_tokenkind_real_spec.spl` | `declared>=38 executed=38 passed=38 failed=0 dropped=0` | 38 / 38 |
| `test/01_unit/compiler/parser/treesitter_tree_real_spec.spl` | `declared>=33 executed=33 passed=33 failed=0 dropped=0` | 33 / 33 |

**150 of 151 reported-passing examples are the literal statement `expect true`.** Two of the four
files are 100% tautology — they contain no other assertion of any kind. The real bodies are present
but commented out:

```
    it "tokenizes fn keyword":
        # var lexer = Lexer.new("fn")
        # val result = lexer.tokenize()
        # expect tokens[0].kind == TokenKind.Fn
        expect true
```

None of these examples carry `tag: ["skip"]`, so they are counted as *passing coverage* of the
lexer / parser / tokenkind / tree API rather than as declared scaffolding. A tautology cannot fail,
so no sabotage of the subject is required to establish vacuity — the assertion is independent of
the subject by construction.

The single non-tautological example is `treesitter_lexer_real_spec.spl` :: "creates lexer with
empty source" (`Lexer(source: "")` → `tokenize()` → `expect result.ok.?`).

## Secondary finding: `PythonTrue` recovery lint false-positives on legitimate enum variants

`src/compiler_rust/lib/std/src/parser/treesitter/__init__.spl` declares a `TokenKind` enum whose
variants include `True` and `False` — necessary names for a lexer that tokenizes the Simple
literals `true`/`false` (see lines 286-287: `case "true": TokenKind.True`).

Compiling any spec that imports this module prints, at **`error:` level**:

```
error: Common mistake detected: Replace 'True' with 'true'
  --> src/compiler_rust/lib/std/src/parser/treesitter/__init__.spl:37:5
   |
 37 |     True
   |     ^
```

The `PythonTrue` recovery lint does not distinguish an enum-variant *declaration* from a bare
identifier in expression position.

### What was and was not established

- The diagnostic is **a false positive**: `True`/`False` at
  `src/compiler_rust/lib/std/src/parser/treesitter/__init__.spl:37-38` are enum variant
  declarations, not Python-isms.
- The diagnostic is emitted at `error:` level but is **non-fatal on this path**. A probe spec that
  constructed `Lexer` with a bogus field name (`Lexer(no_such_field_anywhere: "x")`) **failed**,
  which proves `Lexer` resolves to a real struct that validates its fields. So the module is not
  simply "unloadable", and the claim that resolution is fail-open here is **not** supported —
  a companion probe using an entirely nonexistent symbol also failed, as it should.
- **Not established:** whether the enum variants `TokenKind.True` / `TokenKind.False` are usable
  from a spec after recovery, i.e. whether the lexer can actually tokenize `true`/`false`. That is
  the natural next probe and is exactly what the 150 tautologies would have covered had they been
  real.

An `error:`-level diagnostic that does not fail the build is itself worth a look — it means a genuine
error in this module class would also be survivable and invisible.

### Emitter locations (not patched — Rust seed parser, hot path, Stage-3 lanes in flight)

| File | Role |
|------|------|
| `src/compiler_rust/parser/src/error_recovery.rs:249` | `PythonTrue => "Replace 'True' with 'true'"` |
| `src/compiler_rust/parser/src/parser_impl/core.rs:157` | wraps as `Common mistake detected: {}` |
| `src/compiler_rust/parser/src/parser_helpers.rs:73` | second emission site |
| `src/compiler/10.frontend/parser/recovery.spl:116` | pure-Simple mirror of the message |
| `src/compiler_rust/lib/std/src/parser/error_recovery.spl:93` | seed-std mirror |

Suggested direction: suppress `PythonTrue`/`PythonFalse`/`PythonNone` recovery when the identifier
is in enum-variant declaration position or is the trailing segment of a qualified path (`X.True`).
Neither is ambiguous.

## Disposition proposed (NOT taken — needs approval)

1. Fix the `PythonTrue` lint exemption above.
2. Probe whether `TokenKind.True` is reachable from a spec; if so, uncomment the real bodies in the
   four specs so they assert against the live module.
3. Until (1)/(2) land, the four specs should not keep claiming green coverage. Marking them
   `tag: ["skip"]` with a pointer to this bug **requires approval** — repo policy forbids skipping
   tests unilaterally, so it was not done here.

## Enumerated vacuity backlog (context for the above)

Census over the live spec trees only — excluding the `test/{unit,system,integration,perf,feature}/`
legacy duplicate trees and `.spipe_*` generated files. 19,074 non-generated `*_spec.spl` files
in `test/`.

| Shape | Count |
|-------|-------|
| Tautology-only examples, **not** skip-tagged (whole example body is `expect true`) | **513 examples in 45 files** |
| Tautology-only examples that **are** skip-tagged (declared scaffolding, not vacuity) | 286 examples in 6 files |
| Examples whose entire body is `nil` | 20 examples in 3 files |
| Files containing a bare `assert <expr>` statement form | 12 files (not examined) |

Top remaining tautology files after the treesitter cluster:
`test/03_system/feature/usage/parser_error_recovery_spec.spl` (36),
`test/01_unit/app/ui/vulkan_window_spec.spl` (31),
`test/01_unit/compiler/blocks/utils_basic_spec.spl` (28),
`test/01_unit/compiler/blocks/builder_api_basic_spec.spl` (26),
`test/03_system/feature/usage/parser_deprecation_warnings_spec.spl` (26),
`test/01_unit/lib/std/testing/mock_spec.spl` (26).

`nil`-body files: `test/01_unit/spec/dsl_spec.spl` (10),
`test/01_unit/compiler/parser/cli_spec.spl` (5),
`test/01_unit/compiler/parser/optimize_spec.spl` (5).

### Two prior-baseline claims that did NOT reproduce

- **"A spec containing `fn main` makes the runner DROP every describe/it block."** Not reproduced
  for the `simple test` path. All 8 specs containing both `fn main` and `describe` were run
  individually; every one reported `dropped=0` with `executed` equal to `declared`. The claim may
  still hold for `simple run`, which is a different code path and was not exercised here.
- **"~15% of spec examples are vacuous."** Not supported by the tautology/`nil` shapes: 533
  vacuous examples across 48 files is far below 15% of the corpus. An earlier pass of this census
  produced a "55,511 examples with no assertion" figure; that number is a **classifier artifact**
  (helper wrappers such as `fn check(c: bool): expect(c).to_equal(true)`, and the spipe
  `step`/`given`/`then` DSL) and is discarded — it should not be quoted.

### Duplicate spec trees

`test/unit/` is a 5,097-file subset of `test/01_unit/` with byte-identical contents on the files
sampled (only 1 file is unique to `test/unit/`; 6,751 are unique to `test/01_unit/`). The same
pattern holds for `test/system/` vs `test/03_system/` and `test/integration/` vs
`test/02_integration/`. Fixing a spec in one tree therefore leaves a live sibling unfixed.

### Superseded vacuous crypto spec

`test/03_system/os/os_crypto_spec.spl` (794 lines, titled "**RFC Test Vectors**") contains
essentially **no test vectors**. Across SHA-256, HMAC-SHA-256, AES-256-GCM, ChaCha20, Poly1305,
ChaCha20-Poly1305, X25519 and Ed25519 it asserts only output lengths, determinism,
"different inputs differ", encrypt/decrypt round-trips and tamper rejection. The full expected
digests appear **in comments** and are never compared; only 2 bytes of the 32-byte SHA-256 digest
are checked. It loads the RFC 8032 TEST 1 Ed25519 seed and the RFC 4231 case-1 HMAC key/data and
then asserts only `len() == 32`. An internally-consistent but wholly incorrect implementation
passes every check.

It is **superseded**: `test/03_system/os/os_crypto_ref_primitives_spec.spl` (544 lines) covers the
same `os.crypto.*` entry points with real RFC 7748 / RFC 8439 known-answer vectors, including the
X25519 Alice/Bob vectors that would catch a missing RFC 7748 scalar clamp.

Its only live consumer is `examples/09_embedded/simple_os/arch/x86_64/crypto_unit_entry.spl`, which
imports `test.system.os_crypto_spec` — the **legacy duplicate tree**, not `test/03_system/`.
Proposed (not done): retarget that entry point at `os_crypto_ref_primitives_spec` and delete both
copies of `os_crypto_spec.spl`.

## Genuine failing specs surfaced while establishing the oracle

Reported, not fixed — these land in source directories owned by an active Stage-3 lane.

| Spec | verdict |
|------|---------|
| `test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl` | `executed=3 passed=1 failed=2` |
| `test/03_system/compiler/trait_default_cross_module_codegen_regression_spec.spl` | `executed=3 passed=2 failed=1` |
| `test/03_system/compiler/native_same_name_has_dispatch_regression_spec.spl` | `executed=1 passed=0 failed=1` |
| `test/01_unit/os/posix/signal_compat_spec.spl` | `executed=9 passed=8 failed=1` ("signal_deliver returns an i32") |

## Method note — the runner's own vacuity oracle

`bin/simple test <one spec>` emits a machine-readable line that should be the primary signal for
this class of work, because the human-readable verdict is otherwise buried under hundreds of lines
of unrelated lint and `[gc-warning]` noise:

```
SPEC FILE VERDICT: <path> declared>=N executed=N passed=N failed=N dropped=N
```

`declared` vs `executed` vs `dropped` directly detects the dead-entry-point and dropped-block
shapes. Grep it with `/usr/bin/grep -a` (ugrep is the default `grep` here, and log output contains
control bytes).
