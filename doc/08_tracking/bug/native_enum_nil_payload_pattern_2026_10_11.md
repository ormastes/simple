# Nested nil enum payload and optional text provenance

Status: OPEN. Canonical bug ID: `native_enum_nil_payload_pattern_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/2981

Original failure: C35 runner Ok(nil) payload unsupported at rt_hal_isolated_host.spl:157. First binding workaround ARM exit1; unwrapped text formatted as integer handle.

Workaround commits:

- `3ac1706cb94ac4ab35d7b4f8b81bba7be728af2a`; recovery parent `7324234fe33dcc7292849f4907439353228d8535` (review only).
- `9773949ac215c2cb8e8e1234db6b1bc40e967d12`; recovery parent `3ac1706cb94ac4ab35d7b4f8b81bba7be728af2a` (review only).

Current qualification: C36 narrow six-assertion fixture ARM runtime PASS; RISC-V ELF243 object PASS, not execution. Actual rt_hal_isolated_host consumer still MIR FAIL on separate callback fields; private process-loop/runner not qualified.

Producer: `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c36-result-optional-text-boundary/result_optional_payload_workaround/{arm-runtime-source-coverage,riscv-runtime-source-coverage}/`.

Reproducing/prevention source: `test/fixtures/compiler/result_optional_payload_workaround/main.spl`.

Background fix owner and removal condition: MIR enum literal-payload and optional text provenance owners. Restore original Ok(Some(chunk))/Ok(nil) arms and remove identity helper only after original-form negative/present/absent controls and real consumer pass.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: 3ac1706cb94ac4ab35d7b4f8b81bba7be728af2a -> dbc1c66792be83a937d0b7806324788049f9bf5d (stable patch-id equal; both UNLANDED on checked release); 9773949ac215c2cb8e8e1234db6b1bc40e967d12 -> 09cbce4e77a7707881d570739bd1d50c39703648 (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: Passing narrow C36 ARM/RISC-V fixture source 9773949ac215c2cb8e8e1234db6b1bc40e967d12; actual C36 consumer integrationf7fdaf remains failing on callback ownership.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.
