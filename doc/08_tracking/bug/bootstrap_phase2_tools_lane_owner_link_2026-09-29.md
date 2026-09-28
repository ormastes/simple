# Phase2 tool runtime ownership and strict linker failures

## Observed failure

Frozen main `d9281560d8f3d84687cbc50ea25eeff4d62c3c33` completed all four
canonical Rust phases and linked the Linux Stage2 compiler. After an interrupted
matrix was resumed with the canonical verifier, the full CLI compiled 1005
modules and reused 1484, then failed to link with 167 unique unresolved symbols.
The canonical matrix exited 1; downstream tasks were blocked. No complete
Stage2 matrix or Stage3/4 admission is claimed.

The verifier selected `host-gpu`, whose implementation intentionally selects
the narrow core-C loader. Its retained archive omitted providers needed by
the CLI closure. The admitted native-all archive already supplied the GPU,
array, font, pixel transfer, and text-layout owners. SQLite and SDL were absent.
The separately linked hosted rlib also needed matching Rust std on Linux; the
existing std shim was attached only on Windows.

A Windows strict Stage2 run exposed an independent inverted condition: the
MSVC retry generated 22 trap stubs when `SIMPLE_NO_STUB_FALLBACK=1`. That
artifact was rejected and preserved for diagnosis. Ordinary Simple function
names and optional-struct callable fields account for part of the unresolved
set; legacy networking declarations require separate reachability evidence.

## Scoped correction

`bootstrap-tools` is an explicit lane for the canonical CLI, test runner, MCP,
and LSP entry paths. It requires an explicit frozen phase2 capsule binding the
current compiler SHA, native-all SHA, hosted receipt SHA, and that receipt's
selected rlib SHA. It never discovers another rlib by modification time or
builds a substitute Cargo archive. Canonical Phase2 verification selects this
lane. Higher phases retain their existing lane until their own producer-bound
authority publication is reviewed; the Phase2 capsule cannot authorize a
different compiler.

The new lane links native-all and its matching hosted std closure. It compiles
the existing SQLite provider only when objects actually require SQLite. The
provider precedes the runtime archive so its string dependencies participate
in ordinary archive extraction. Strict MSVC failure no longer creates parity
stubs.

On Windows MSVC, SQLite uses a complete installed MSYS2 SDK: its header, real
COFF import archive, and matching DLL must all exist. Only `sqlite3.h` enters
the private include directory; copying the whole MinGW include tree would
mix incompatible standard headers with MSVC. The linker uses the exact copied
library and stages a byte-verified DLL beside its output, recording its SHA.
The canonical matrix builds tools directly in that output directory. No new
compiler admission field or global SDK environment setting is introduced.

## Provider ownership

| Boundary | Public owner | C engine input/output | Conversion and lifetime |
|---|---|---|---|
| SDL window title and clipboard input | Rust runtime | NUL-terminated C bytes | Registered owner string only; bounded bytes, established embedded-NUL prefix, temporary CString kept through the call; no fixed-size truncation |
| SDL event, error, clipboard, display text | Rust runtime | Engine-owned C string | Copy into a runtime-owned string before returning |
| SDL `[i64]` pixels | Rust runtime | Borrowed raw i64 pointer and count | Registered ordinary array, validated len/cap/data, decode each signed runtime integer; reject packed/wrong heap kinds; vector stays alive through presentation |
| SDL scalar status, dimensions, events and handles | Existing C engine | Machine scalars | Preserve existing engine validation, dynamic SDL loading, and thread ownership |
| Existing C SDL array frontend | Existing C owner | SplArray and getter callback | Preserve legacy getter semantics and the existing single RGBA-buffer allocation |
| SQLite text | Selected runtime owner | `rt_string_new/data/len` ABI | Existing provider copies bounded input bytes into temporary NUL-terminated storage; output uses the same owner constructor |
| SQLite connection/statement and integer ABI | Existing SQLite provider | Opaque heap-tagged handles and raw i64 | Preserve existing handle and raw integer contract; link the actual target SQLite library |

The Rust SDL provider privately renames C text entry points and excludes C
array frontends. It does not cast a Rust heap header to SplArray. Its gated
translation unit is empty in an ordinary pure-C inventory.

## Regression evidence

Executed C owner checks:

- Linux fresh core-C SDL adapter/raw-view parity: compile and execution exit 0;
  both real dummy-driver surfaces contain the same distinct nontrivial pixels.
  The first diagnostic omitted the actual `runtime.c` getter and is preserved;
  the corrected fixture links that existing owner rather than substituting one.
- Linux SQLite owner ABI: compile, link, and execution exit 0 against the retained
  actual d928 native-all archive, real SQLite library, and matching LLVM closure.
- Windows SQLite owner ABI: compile and execution exit 0 with the retained
  actual run5 native-all archive and real x86-64 SQLite COFF import library/DLL.
  The first diagnostic link omitted LLVM; the successful second diagnostic
  reuses the unchanged C objects and supplies pinned LLVM-C.lib/DLL.

Linux evidence is under
`/mnt/simple-bootstrap-6b2/bootstrap-tools-lane-review-20260929/`
(`core-sdl-cycle2`, `sqlite-owner-cycle1`). Windows SQLite evidence is under
`build/mini_builds/bootstrap-tools-lane-review/windows-sqlite-owner-cycle2/`.
Each directory records actual native exits and exact archive/provider inputs.

The first Rust SDL unit build stopped before test execution: its fixture used
a private-module-only constructor import. The fixture now uses the equivalent
public `rt_array_new`; this does not alter the production representation or ABI.
The failed compile log remains in `cargo-cycle1`. Fresh `cargo-cycle2` passed:

- SDL owner units: 2 passed, 0 failed, 0 ignored. Nontrivial signed/unboxed pixels,
  registered wrong kinds, packed array rejection, bounded UTF-8/NUL text, and
  10,000-byte text without truncation.
- Real SDL dummy-driver Rust-owner integration: 1 passed, 0 failed, 0 ignored.
- Exact lane/parser/entry allowlist and receipt authority tests: 5 passed,
  0 failed, 0 ignored; changed compiler/archive/receipt/rlib, traversal,
  duplicate fields, and absent/nonfrozen authority are rejected.
- Real hosted rlib/std regression: 1 passed, 0 failed, 0 ignored. The rlib fails
  to link without std, then links and executes with the matching std closure.
- Actual native-all archive build exited 0. The final input hashes were unchanged.

A separate C executable linked the updated actual native-all archive without
any core-C value constructor/header/object. It constructed registered text and
arrays through the Rust owner and presented nontrivial pixels through real SDL.
Compilation, link, and execution exited 0. All 12 public Rust-owned SDL exports
have exactly one definition in the archive. Evidence:
`sdl-nativeall-owner-cycle1`; archive SHA
`f162dc14b727c20be328a4ff02e79ced56bfac25410f2e801f8d0e5d2ca8b5d0`.
This is a dirty-source diagnostic artifact, not an admitted generation.

A separate pinned LLVM COFF reproduction preserves strong module-qualified
function linkage and an unreachable wrapper calling absent `rt_net_init`.
`/OPT:REF` still reports that reference with either distinct function sections
or valid per-function COMDAT. COMDAT-only codegen is therefore not a fix for
the Windows legacy networking failures. The baseline and final negative
diagnostics are preserved under `windows-coff-gc-cycle1` and
`windows-coff-gc-cycle3`; no runtime provider or backend change follows from
that rejected hypothesis.

These checks do not certify the full compiler matrix, MCP/LSP smoke, release,
or Stage4. The separate native symbol-owner regression now links but fails its
first runtime callback assertion (`supports_fn("emit-gpu")` is false). That
failure remains open; no further naming retry is claimed here.

The new Windows SDK resolver/restricted-PATH DLL execution test and actual
strict Windows unresolved-link/no-stub test are prepared but unexecuted. The
hardware/TRACE32 helper changes require their own native execution evidence.
Phase3/4 must publish authority bound to their actual producer compiler; the
Phase2 capsule cannot authorize another producer. Full matrix, core/MCP/LSP
smoke, higher-phase admission, and release applicability remain pending. This
patch is suitable for draft review only, with no merge or release certification.
