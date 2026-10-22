# Windows piped process cold handle growth

Status: OPEN, P1 qualification blocker; heap/OS owner attribution unresolved.

The genuine Windows fixture compiled and strict-linked against retained Rust199, but cycles2and3 exited36 at exact final handle equality. [Final run38201907318](https://github.com/ormastes/simple/actions/runs/38201907318) reused the actual cycle2 Windows provider object; no repeated provider compile or Simple/Rust generation build occurred.

| Phase | Actual process handles |
|---|---:|
| Baseline |128|
| Empty argv |131|
| Cancel |158|
| Threads |158|
| Slots |158|
| Final |158|

The diagnostic fixture emitted six phases. The driver wrongly expected an additional Unicode phase, so its diagnostic JSON was not written. Actual native exit36 and these six stderr counts remain retained evidence. No fourth retry is allowed. The plateau during threads and sixteen-slot reuse does not prove legitimate initialization or absence of a leak; it rejects the earlier thread-specific attribution.

Source-only investigation binds frozen82 constructor/accessor and validator paths. First spawn reaches BCrypt/Windows process APIs; stdout validation reaches SIMD tier selection, which can resolve CPU configuration through dirs_next cache directories and filesystem metadata. Those are candidate chains, not observed handle ownership. No cold baseline was weakened, no provider eligibility advanced, and no full compiler/core/MCP/whole-test PASS is claimed.
