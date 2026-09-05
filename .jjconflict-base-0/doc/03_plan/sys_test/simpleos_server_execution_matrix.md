# System test plan: SimpleOS server execution matrix

Trace the frozen receipt, modes, steps, and helpers in
`.spipe/simpleos_server_execution_matrix/state.md`.

1. REQ-001..003: ARM boot, VFS launch, HTTP file, DB write/read and fresh-boot
   persistence.
2. REQ-004..007: physical UNO identity/hash, VFS launch, protocol restart,
   forced CPU-only, then Adreno/Vulkan submit/completion/readback.
3. REQ-008..011: equivalent Linux CPU rows, optional CUDA compute row, dynload
   absence in CPU mode, and before/after optimization evidence when required.
4. REQ-012: deliberate-red rejection of marker, host substitution, missing
   receipt fields and GPU fallback.

No scenario may use an empty body, placeholder pass, or unretained observation.

## Executable and manual artifacts

- Executable: `test/03_system/os/server/simpleos_server_execution_matrix_spec.spl`
- Authored mirror: `doc/06_spec/03_system/os/server/simpleos_server_execution_matrix_spec.md`
- Manual policy: the ARM, UNO CPU, UNO GPU, Linux CPU, and Linux optional-GPU
  rows are visible; deliberate-red substitution checks are folded. Logs,
  protocol transcripts, and artifacts are linked rather than embedded. The
  mounted database credential is bounded to 128 bytes and its bytes must never
  be retained in a receipt, log, command line, or protocol artifact. The disk
  image is sensitive, non-distributable acceptance material; retain its
  SHA-256 for provenance and securely destroy the image after reboot proof.
- Current provenance: authored/uncredited. The storage floor and QEMU executable
  preflight pass. Runtime execution and SPipe/docgen were not run because the
  required current-source ARM compiler/sysroot/runtime artifacts are absent.

## Traceability and honest status

| Requirements | Scenarios | Coverage status |
|---|---|---|
| REQ-001..003 | ARM64 QEMU CPU | Executable fail-fast scaffold; source prerequisites advanced, runtime blocked |
| REQ-004..007 | UNO Q CPU and GPU | Executable fail-fast scaffolds; identity-only evidence, physical SimpleOS runtime/provider absent |
| REQ-008..011 | Linux CPU and optional GPU | Executable fail-fast scaffolds; listener and DB ABI blockers prevent comparable evidence |
| REQ-012 | Deliberate-red rejection | Executable fail-fast checker scaffold; live rejection helper absent |
| NFR-001..007 | All matrix rows | Encoded in receipt/helper/manual contracts; no runtime credit |

The spec deliberately stays red until each live owner replaces its `fail(...)`
body. Unavailable rows are not skipped, source inspection is not execution
coverage, and the authored mirror is not generated-doc provenance.

## Resume gate

After current-source ARM compiler/sysroot/runtime prerequisites are restored,
implement the frozen helpers, run each acceptance row once, run standalone
SPipe/docgen once with zero stubs, retain its transcript, and obtain independent
highest-capability review. No execution or docgen was attempted in this lane.
