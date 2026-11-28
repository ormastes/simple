# Seed interpreter: `Capacity` not found under a dotted `use std.io.file_read_text`

- **Status:** OPEN. Worked around in five specs (brace import), not fixed.
- **Scope:** Rust seed interpreter only (`$HOME/.cache/cargo-target-wr-seed1126b/release/simple`,
  built 2026-11-26), `test --no-session-daemon`. Not checked on a self-hosted binary.
- **Found while** diagnosing `test/01_unit/lib/container/agent_source_return_v3/*` (24 of 24 examples
  failed on `release/1.0.0` at 85ea9caddc5).

## Symptom

```
semantic: <spec>:111:5: in call to `text_byte_buffer` (declared at line 15): function `Capacity` not found
(call stack: io_external_text -> external_text -> external_copy_bytes -> external_byte_buffer)
```

The miss is `text_byte_buffer(Capacity(value: capacity))` at `src/lib/common/encoding/external_text.spl:111`,
which does import `use std.common.types.{Capacity}` (`unit Capacity: i64`, `src/lib/common/types.spl:25`).
The reported file:line is the callee's line placed on the spec path.

## Repro (Rust seed interpreter, diagnostic)

```
use std.spec.step
use std.io.file_read_text
describe "probe":
    it "reads":
        val t = file_read_text("src/lib/common/types.spl")
        expect(t.byte_len() > 0).to_equal(true)
```

| Spec imports | Verdict |
|---|---|
| `std.spec.step` + `std.io.file_read_text` | ERROR, `Capacity` not found |
| same + `use std.common.types.{Capacity}` | OK |
| `std.spec.{step}` + `std.io.file_read_text` | OK |
| `std.spec.step` + `std.io.file_read_text` + `std.common.crypto.sha256.sha256_text` | OK |
| `std.spec.step` + `std.io.{file_read_text}` | OK |
| `std.spec.step` + `std.nogc_sync_mut.io.{file_read_text}` | OK |
| `std.spec.step` + `std.nogc_sync_mut.io.file_ops.{file_read_text}` | OK |
| `std.spec.step` + `std.io_runtime.{file_read_text}` | OK |

So a `unit` constructor imported by a transitively loaded module resolves only when some other import of
the spec happens to register it; with two dotted single-symbol imports and nothing else it does not.
`host_linux_service_agent_v4_structure_spec` uses the same dotted io import and passes because it also
imports `std.spec.{step, fail}` and `sha256_text`.

## Workaround

`use std.io.file_read_text` -> `use std.io.{file_read_text}` in the five `agent_source_return_v3`
specs. 74 spec files under `test/` use the dotted form; the others were not run here.

## To fix

Find why the seed's dotted single-symbol `use` path does not register the imported module's transitive
`unit` constructors (the `use std.common.types.{Capacity}` of `external_text.spl`), then revert the
five brace imports.
