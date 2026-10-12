# System test plan: profile-switchable containers

## Item 7 acceptance contract (2026-10-03)

This list is the completion gate, not a claim that the existing narrow probes
prove every requirement. Each acceptance ID maps to the equally numbered
REQ-PSC requirement. A scenario is green only with a source-matched pure-Simple
runtime, real assertions, and saved execution receipts. An unavailable backend
or compiler is BLOCKED, never an implied PASS. Run the failing scenario before
its implementation change, then run that scenario once after the fix; cap
verify/fix cycles at three. Static review is not a red or green execution.

| Acceptance | Concrete stimulus and required assertion | Executable evidence / remaining work |
|---|---|---|
| PSC-AC-001 | Declare neighboring set/map containers with all four attributes, including typed factory locals and fields. Assert selected storage independently before insertion; change only one attribute and assert unchanged other-instance contents and identities. | Existing attributed semantics and typed-factory scenarios cover storage. Attribute-only source identity cases require their parser/profile specs and actual execution. |
| PSC-AC-002 | Populate 32 signed keys, replay 128 deterministic insert/update/remove/clear operations, switch populated instances through linear/hash/ordered/auto every 16 operations, and compare every lookup, return value, length, sorted key, and map payload with an independent array model after each operation. | `transition_model_probe.spl` plus the system scenario run the same model on interpreter and LLVM native. Existing nil-payload and unsupported-key probes remain required. |
| PSC-AC-003 | Capture hot and cold text/generic set/map sites. Assert stable distinct site IDs, exact lookup hits/misses/cardinality, and observed distinct/materialization/probe/collision metrics; zero observations must not fabricate measurement. | Capture/collision system scenarios plus metric unit/integration specs. Applicable join/P6 measurements remain an explicit missing implementation/evidence gate. |
| PSC-AC-004 | Reload captured bytes; append an independently identified run and verify p95. Mutate schema/module/workload/target and duplicate/corrupt sample identities separately; each rejection must preserve the previous profile/output. | Existing sprof and CLI integration cases plus system target rejection. The system now reruns the preserved binary and compares full stdout and stderr; mere file existence is insufficient. Byte-exact output retention and hot-path no-I/O instrumentation remain required. |
| PSC-AC-005 | Use identical data with conflicting explicit attribute/profile hints; explicit choice wins. For each failed effect/order/duplicate/ownership/worst-case gate, reject an unsafe nested/hash/merge candidate and preserve baseline outputs. | Existing collision and forced-linear controls cover runtime precedence. Typed planner-to-MIR rejection/selection needs executable implementation and adversarial differential fixtures; advisory strings alone cannot satisfy this row. |
| PSC-AC-006 | Explain the exact captured site. Assert selected algorithm and admitted evidence plus explicit linear/hash/ordered rejection fields, initializer/key-order guards, extra-memory field, and fallback field. Assert emitted choice agrees with the executed instance. | Captured-site system scenario strengthened with these output fields; typed MIR evidence must replace the current `unconnected` boundary before full completion. |
| PSC-AC-007 | Exercise supported primitive and aggregate `Hash + Eq + Ord` keys, optional/nested values, sets/maps, and typed collection operations. For nested/hash/merge plans prove duplicate multiplicity, stable order, empty inputs, collisions, and ownership under P0 gates. | Integer/text probes are partial coverage only. Aggregate dispatch and typed join/MIR fixtures remain missing; unsupported-key rejection does not count as aggregate support. |
| PSC-AC-008 | Run the same accepted semantic/feedback fixtures on interpreter, JIT, LLVM AOT, self-hosted native, and supported SimpleOS targets. Double workload sizes and gate production comparison/probe counts. Resource measurements are best effort per the user's 2026-10-03 selection; record unavailable data rather than imposing unselected latency/memory limits. | Interpreter/LLVM system drivers exist. JIT/SimpleOS execution receipts remain absent. Resource receipts are incomplete and advisory. No single backend or compiler banner proves this row. |

### Current runtime admission evidence

Acceptance lane: `work/item7-acceptance-20261003`, isolated worktree
`C:/dev/simple-item7-acceptance-20261003`, owner acceptance-tests agent.
On 2026-10-03, `SIMPLE_QUALIFIED_RUNTIME` was unset and `C:/dev/simple/bin/release`
did not exist. Both `C:/dev/simple/bin/simple.exe --version` and
`C:/dev/simple-windows-phase2-integrated-20261003/bin/simple.exe --version`
explicitly identified themselves as Rust bootstrap seeds. Neither was used to
run these tests. The separate item1 bootstrap log ended with stage2 link failure
(`rt_fd_stat_snapshot_v1` undefined) and explicitly refused seed fallback.
Consequently new scenarios are written but **NOT RUN**, with red/green execution
blocked by the qualified runtime prerequisite. This must not be presented as
successful TDD execution or production readiness.

| Requirement | Executable evidence required |
|---|---|
| REQ-PSC-001–002 | Source examples with two differently attributed containers, including typed factory local/field initializers; insert/remove/lookup/iteration equivalence through linear, hash, ordered, and auto transitions. |
| REQ-PSC-003–004 | Real `.sprof` v2 capture of size, lookup, distinct-key, public materialization, hash-probe, and hash-collision metrics; file reload; stale module/workload/target rejection; corrupt/duplicate sample rejection; multi-run append and p95 aggregation; atomic output with rejected append leaving prior bytes intact; a later run using feedback. |
| REQ-PSC-005–006 | Compiler `--explain-collection-plan` output with accepted/rejected candidates and guards; no unsafe index substitution before P0 gates. |
| REQ-PSC-007–008 | Generic set/map key cases plus nested/hash/merge cases across interpreter, JIT, LLVM AOT, self-hosted native, and supported SimpleOS target. `generic_key_families_probe.spl` adds text/bool generic backing (including empty/false keys), replacement, populated transitions and sorted snapshots; these authored cases remain unrun and do not replace aggregate-key or join evidence. |
| NFR-PSC-001–005 | Differential random cases, geometric operation counts, no hot-path I/O, cache invalidation, allocations/copied bytes/peak RSS/warm latency. `OrderedMap.lookup_comparisons` shares the production get/contains search path, while `update_comparisons` counts production put/remove calls. The four adaptive families expose production linear lookup counts and captured hash probes/collisions. Geometric perf cases gate ordered, linear, and fixture-specific hash lookup costs at doubled sizes. Adversarial hash cases, allocation, RSS, and warm-latency gates remain required. |

The focused text-set, text-map, generic map/set capture, AVL tree, parser, and `.sprof` unit specs plus `test/02_integration/compiler/profile_switchable_attribute_it_spec.spl`, `test/02_integration/compiler/profile_switchable_cli_feedback_it_spec.spl`, and `test/02_integration/app/optimize/sprof_collection_sample_limit_it_spec.spl` are preliminary evidence only. The CLI probe captures real text-set and text-map sites, measured lookups and public snapshots, appends a second run, and checks early algorithm switches when that profile is loaded. It also checks explicit attribute precedence, workload and target rejection, and rejected append preserving a corrupt prior file. These Simple tests have not run on an admitted source-matched runner. The executable SPipe system scenario and mirrored manual now include text, integer-key generic, and typed factory paths through interpreter and LLVM native builds, but remain unrun under an admitted pure-Simple compiler with no stub fallback. Additional scenarios for aggregate generic keys, typed-MIR, other backends, and NFR requirements are still required.

Windows and WSL admission use the same `test/03_system/qualified_pure_simple_runtime.spl`
helper. It reads `SIMPLE_QUALIFIED_RUNTIME` from the runtime facade first, then
from `/bin/sh` on WSL or `cmd.exe` on Windows when an older test runner hides
the caller environment. A missing path, unidentified binary, or Rust-seed
banner remains a test failure. This portable lookup is test infrastructure;
each platform still needs its own source-matched pure-Simple binary and
interpreter/native receipts before any system scenario can be marked PASS.

The two existing collection benchmark scripts measure list/set/hashset references and may select a Rust seed; they cannot serve as the item 7 performance gate. Add an adaptive-container benchmark that records linear comparisons, hash probes/collisions, ordered lookup and update comparisons, allocation/copied-byte counts, peak RSS, and warm latency for each admitted target profile. Require a qualified source-matched pure-Simple compiler and reject seed evidence.

Identity gate: capture a first-run profile under `@collection_algorithm("auto")`, change only that attribute to `"ordered"`, and prove the second run admits the same module and site identities while selecting the forced ordered representation. A changed path, changed non-attribute source, workload, or target must still reject the old feedback. The source-level parser/profile cases exist but need an admitted runner; the installed Windows executables are Rust seeds and the isolated pure-Simple Stage2 test-runner link is unresolved.

Native feedback gate: `test/02_integration/compiler/profile_switchable_native_feedback_it_spec.spl` captures a real workload with `simple run`, builds that source with the captured `.sprof`, executes the native binary, and checks hot set/map promotion before insertion while cold and forced-linear instances stay linear. It also checks wrong-target rejection preserves the previous binary. This is an executable acceptance spec, not a PASS until it runs under an admitted source-matched pure-Simple CLI.

Collision replay gate: `test/03_system/app/compiler/feature/profile_switchable_container_algorithms_spec.spl` now also writes paired hash probe/collision samples for four parser-issued auto sites and replays them through interpreter and LLVM native execution. The fixture checks ordered storage before insertion and after clear, set/map value preservation, and an explicitly linear control. This is pending the same qualified pure-Simple runtime; it covers integer keys but does not yet establish arbitrary aggregate `Ord` dispatch or typed MIR substitution.

PSC-AC-003 continuation: `test/01_unit/lib/collections/adaptive_set_loop_spec.spl`
checks the explicit observed set-loop API with ordered callback traces, all
representations, Continue, counted Break, error omission, empty zero, malformed
snapshots, and capture rejection without changing logical results. Scenarios
are authored, UNRUN. The native capture-owner selfcheck passed the corresponding
counter, target, zero/absence, overflow and budget contracts. General compiler
loop site transport/instrumentation and joins remain open; this slice does not
mark PSC-AC-003 complete.
