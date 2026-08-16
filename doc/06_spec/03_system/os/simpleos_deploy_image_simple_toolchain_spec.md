# SimpleOS target payload image admission — operator manual

Source: `test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl`

Status: source/manual current; pure-Simple Stage-4 execution, `spipe-docgen`,
and seven-score `sspec-maintain` evidence remain blocked by B-HOST-CLI.
Stubs: 0. Scenarios: 3 active, 0 skipped, 0 pending.

## Purpose and claim boundary

This `image-admission` spec calls the production
`os.installer.image_builder.build_install_image_with_simple_binary` API. It
proves that marker, Rust-seed, and wrong-target payloads are rejected before
`/SYS/SIMPLETOOL.SDN` is staged. It does not prove a valid image was produced,
booted, or exercised in a guest.

## Preconditions

- Run from the repository root with an admitted pure-Simple Stage-4 runner.
- The test may write isolated ignored fixtures below `build/tmp/`.
- The Rust seed and bootstrap-only Stage 2 are not admissible test runners or
  payload provenance.

## Operator workflow

1. Run the executable SSpec once with the admitted runner.
2. Require all three examples to execute and exit zero.
3. Confirm every result is an error from the production image builder and that
   no toolchain manifest exists in the corresponding rootfs tree.
4. Retain the runner path/SHA-256, command, and stdout/stderr.
5. Generate the SPipe manual with `0 stubs` and inspect all seven
   `sspec-maintain` scores when Stage 4 is available.

## Scenarios

### Marker without provenance

`step("Submit a marker payload to the production image builder")`

The builder must return an error containing `lacks target provenance` and must
not create `/SYS/SIMPLETOOL.SDN`.

### Rust bootstrap-seed provenance

`step("Submit seed provenance to the production image builder")`

Even with the correct target, focused entry, entry-closure flag, and LLVM
backend, a stamp naming `compiler_rust` must be rejected with `bootstrap seed`
before ELF staging.

### Wrong target provenance

`step("Submit wrong-target provenance to the production image builder")`

An `aarch64-unknown-simpleos` stamp submitted for an x86_64 image must be
rejected with `target mismatch` before ELF staging.

## Traceability

| Requirement | Coverage | Claim boundary |
|---|---|---|
| REQ-004 | Production builder refuses to stage unadmitted toolchain roles/manifest | Negative image admission |
| REQ-007 | Marker and Rust-seed payloads fail verification | Negative image admission |
| NFR-002 | Missing/wrong provenance fails closed | Negative image admission |
| REQ-SOS-TD-002 / REQ-SOS-TD-003 | Not satisfied here | Require admitted positive image and live deployment receipts |

## Evidence and provenance

The oracle is the production image builder imported by the executable spec.
There are no source-string assertions or test-only reimplementations of its
decision. Record the spec SHA-256, `src/os/installer/image_builder.spl`
SHA-256, runner SHA-256, command, exit code, stdout, and stderr.

<details>
<summary>Executable SSpec flow</summary>

```simple
describe "SimpleOS deploy image Simple toolchain payload":
    it "should reject a marker payload without a provenance stamp":
        step("Submit a marker payload to the production image builder")

    it "should reject payload provenance from the Rust bootstrap seed":
        step("Submit seed provenance to the production image builder")

    it "should reject a payload stamped for the wrong target":
        step("Submit wrong-target provenance to the production image builder")
```

The complete reproducible source and assertions are at the Source path above.

</details>

## Compatibility and limitations

- This is negative admission coverage; a green result does not establish a
  deployable payload or bootable image.
- Positive image and same-run guest evidence remain blocked by B-HOST-CLI,
  B-TARGET-SIMPLE, B-GUEST-LLD, B-IMAGE, and B-DESKTOP-LIVE.
- Full acceptance remains
  `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`.
