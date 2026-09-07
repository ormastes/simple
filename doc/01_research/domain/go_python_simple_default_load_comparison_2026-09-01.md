<!-- codex-research -->

# Go, Python, and Simple default-load comparison

## Default closure

| Surface | Go | CPython | Current Simple | Recommended Simple |
|---|---|---|---|---|
| Command router | `go` orchestration binary; selected tools are subprocesses | interpreter bootstrap plus selected entry module | CLI imports most product commands before argv dispatch | minimal argv/metadata dispatcher, then one typed command capsule |
| Imported code | compiler consumes indexed export data; dependency source is not reparsed | imports resolve and execute modules on demand, with observable side effects | compiler parses much of the transitive source closure | load validated public summaries; fetch exceptional bodies by digest |
| Current compilation unit | all selected `.go` files in package fully parsed | selected module source compiles to bytecode | requested module plus broad closure parsed/surfaced | fully parse changed/local unit; reuse immutable AST/summary for unchanged units |
| Backends | compiler binary contains all architectures but initializes selected target | native extension loaders exist; modules load when imported | concrete backends/codegen enter broad compiler closure | backend interfaces/manifests eager; selected provider body native-build-only |
| Linker/assembler | separate actions, absent on irrelevant/cache-hit paths | not part of ordinary Python import | reachable through eager driver orchestration | attach only for object/archive/binary-producing actions |
| Runtime initialization | every linked package `init` runs before `main`; unreachable code stripped except init roots | builtins/sys/import machinery/encoding essential; `site` and `.pth` policy add eager work | module globals and broad library/tool imports can enter default closure | tiny semantic/runtime capsule; explicit admitted activation for observable initialization |
| Lazy safety | indexed export data lazily decodes declarations and exceptional bodies | explicit lazy imports change error and side-effect timing | named lazy imports exist, but globals/dynamic imports have known hazards | freeze identity at snapshot time; typed local/nonrecursive capsule activation |

## Go lessons

Go compiles a package as a unit and fully parses that package. When valid compiled archives/export artifacts exist, imported dependency source is not reparsed. Unified export data includes declarations plus exceptional cross-package bodies for generics and inlining and decodes the object graph lazily. Type-check-only readers do not decode function bodies. This is the closest model for binary public summaries plus virtual `_tldr.spl`.

Go's build cache separates ActionID from OutputID, is globally shared and concurrency-safe, explains/verifies keys, and uses stable trimmed paths. It still has holes Simple should close: cgo library changes are not intrinsically detected; compiler binaries contain all target backends; cleanup is coarse; and export data is not a general persistent AST/LLM resource.

Sources: [compiler overview](https://go.dev/src/cmd/compile/README), [toolchain](https://go.dev/doc/toolchain), [build cache](https://go.dev/src/cmd/go/internal/cache/cache.go), [build IDs](https://go.dev/src/cmd/go/internal/work/buildid.go), [linker](https://go.dev/cmd/link/), [initialization](https://go.dev/ref/spec).

## Python lessons

CPython eagerly needs runtime/GC, builtins, `sys`, exception machinery, import finders/loaders and startup encodings. Most standard-library and application modules load only when imported, but import execution is semantically observable. `site`, `.pth` executable lines and customization can add policy-driven eager imports. PEP 810's explicit lazy-import design, accepted for Python 3.15 but not evidence about older deployed interpreters, deliberately avoids lazy-by-default because first use changes error, side-effect, path-hook and `sys.modules` timing.

Python persists bytecode rather than public signatures or reusable ASTs. Default timestamp/size `.pyc` invalidation and optional unchecked hashes are insufficient for Simple's authoritative compiler cache. Simple should freeze provider/module identity by digest at snapshot creation so delayed activation cannot resolve against mutated paths or environment.

Sources: [import system](https://docs.python.org/3/reference/import.html), [site initialization](https://docs.python.org/3/library/site.html), [path initialization](https://docs.python.org/3/library/sys_path_init.html), [PEP 810 lazy imports](https://peps.python.org/pep-0810/), [LazyLoader](https://docs.python.org/3/library/importlib.html#importlib.util.LazyLoader), [PEP 552 hash pycs](https://peps.python.org/pep-0552/), [PEP 3147 cache layout](https://peps.python.org/pep-3147/).

## Concrete Simple delayed-load boundary

Eager startup should contain only argv/configuration, encoding, diagnostics, path/hash/snapshot admission, loader manifest/header verification, public signature/import scanning, resolver/type/trait/AOP summary identities, and typed capsule/provider interfaces.

Delay by task:

- semantic body: full parser bodies, HIR lowering, trait solver bodies, inference/checking, semantics, generic/inline/CTFE bodies;
- interpreter: `95.interp/**` and required execution types only for run/REPL/interpreter mode;
- native producer: mono, MIR, borrow, optimizer, concrete backend, object/archive/link/runtime discovery and header generation;
- AOP: pipeline AOP, aspect semantics/index/cache/weaving and aspect packs, after an eager candidate digest proves use;
- loader: object mapping, JIT instantiation, resource lifecycle and generation sweeping after admitted SMF/dynload use;
- tools: test, MCP/LSP, fmt/lint/query/stats, Office/IDE/browser/UI/T32/jj/devhub/OS commands as independent entry closures;
- libraries: database, network, UI/web/GPU/audio and reporting only when the selected capsule requires them.

Never delay blindly: module globals/registries, public layouts/constants, trait coherence declarations/defaults, macros/CTFE, AOP selectors that alter code/layout, security policy, diagnostic source maps, cache schemas, provider ABI/capability manifests, and loader hash/signature/relocation validation. These require an explicit effect summary and admission contract before their implementation bodies can be delayed.

## Verification slices

Measure and closure-audit `--help`, cache-hit query, frontend-only check, interpreted run, SMF load, native compile and native link separately. Static and delayed modes must produce identical bytes, diagnostics and side-effect order. A forbidden-closure test should reject AOP, concrete backends, linker/archive, MCP/LSP/test/UI and unrelated product commands from minimal startup.
