# Kernel dependency contracts: literal scanner input

**Provenance:** Authored from the exact executable specification; this is not a generated-manual completeness claim.

**Purpose and audience:** Compiler maintainers reviewing kernel dependency ownership and the source text passed to the call scanner.

**Source:** `test/01_unit/compiler/plugin_arch/kernel_dependency_boundary_spec.spl`

**Requirements:** KPM-REQ-001, KPM-REQ-007, KPM-REQ-009, retained from the executable source.

**Setup and behavior:** Use the existing ApiSurface, shared-library policy, and scan_source_calls imports. The repaired scanner argument uses a raw import fragment so `{sha256_text}` remains literal, followed by a normal newline and the original call text. A raw prefix on the entire escaped string would incorrectly preserve backslash-n. The production scanner is unchanged.

**Evidence scope:** Four authored scenarios contain nine assertion lines. The focused cycle-2 bootstrap source diagnostic executed only the repaired original scanner scenario and the new literal/newline prevention scenario: **2 passed, 0 failed, 0 skipped, 0 dropped**. The first two original scenario bodies are unchanged, previously passed, and were not rerun. Both admission/body receipts closed authentically; all observed loaded paths existed and matched prelaunch pins, including the real scanner owner. These facts do not establish native, whole-suite, or immutable-byte qualification.

**Source SHA256:** `4d7192b358a227f025c984dd7d30c6fd25ddb2fcef2551f12fa8129379b0e2cc`.

**Evidence:** `build/native_probe/phase1-scanner-literal-fixture-repair-20261010/terminal-summary.json` and `strict-loader-audit.json`; focused source SHA256 `7f865185a586492523b1ed42c7224e4fa8bcd4ef498f6a369dd35741e360dd13`.

**Verification and troubleshooting:** Reuse the retained passing evidence; do not repeat it. A missing-variable error naming sha256_text indicates accidental interpolation before the scanner call. A one-line source indicates a literal backslash-n was passed. Missing or unpinned loaded paths invalidate source attribution even if the raw test verdict passes. New source changes require their own reviewed focused criteria within the remaining feature budget.

## constructs the API surface contract without tool ownership

**Execution:** Preserved prior baseline case; not rerun for this repair.

**Action:** Construct the actual ApiSurface contract and check its module identity and empty function inventory.

**Exact oracles:**

- `expect(surface.module).to_equal("example")`
- `expect(surface.functions.len()).to_equal(0)`

<details>
<summary>Actual scenario setup and body</summary>

```simple
        val surface = ApiSurface.create("example")
        expect(surface.module).to_equal("example")
        expect(surface.functions.len()).to_equal(0)
```

</details>

## provides shared-library policy from the kernel contract

**Execution:** Preserved prior baseline case; not rerun for this repair.

**Action:** Read the actual shared-library policy and check the extension and SPL_SHARED_LIBRARY define.

**Exact oracles:**

- `expect(flags.output_extension.starts_with(".")).to_equal(true)`
- `expect(flags.defines).to_contain("SPL_SHARED_LIBRARY")`

<details>
<summary>Actual scenario setup and body</summary>

```simple
        val flags = get_shared_lib_flags()
        expect(flags.output_extension.starts_with(".")).to_equal(true)
        expect(flags.defines).to_contain("SPL_SHARED_LIBRARY")
```

</details>

## keeps call scanning in semantic ownership

**Execution:** Verified in the targeted 2/2 source diagnostic.

**Action:** Pass source text with a literal brace-delimited import, a real newline, and the unchanged call to scan_source_calls; verify the caller path.

**Exact oracles:**

- `expect(scanned.module_path).to_equal("caller.spl")`

<details>
<summary>Actual scenario setup and body</summary>

```simple
        val scanned = scan_source_calls("caller.spl",
            r"use std.common.crypto.sha256.{sha256_text}" + "\n" + "fn run(): sha256_text(\"x\")")
        expect(scanned.module_path).to_equal("caller.spl")
```

</details>

## preserves literal import braces and the real source newline

**Execution:** Verified in the targeted 2/2 source diagnostic.

**Action:** Declare a same-named local sentinel, then construct the raw import fragment and real newline. Assert exactly two source lines, literal braces, unchanged call text, and the real scanner caller path.

**Exact oracles:**

- `expect(lines.len()).to_equal(2)`
- `expect(lines[0]).to_equal(r"use std.common.crypto.sha256.{sha256_text}")`
- `expect(lines[1]).to_equal("fn run(): sha256_text(\"x\")")`
- `expect(scanned.module_path).to_equal("literal.spl")`

<details>
<summary>Actual scenario setup and body</summary>

```simple
        val sha256_text = "must_not_be_interpolated"
        val content = r"use std.common.crypto.sha256.{sha256_text}" + "\n" + "fn run(): sha256_text(\"x\")"
        val lines = content.split("\n")
        expect(lines.len()).to_equal(2)
        expect(lines[0]).to_equal(r"use std.common.crypto.sha256.{sha256_text}")
        expect(lines[1]).to_equal("fn run(): sha256_text(\"x\")")
        val scanned = scan_source_calls("literal.spl", content)
        expect(scanned.module_path).to_equal("literal.spl")
```

</details>

## Complete executable setup and preserved source

<details>
<summary>Full specification</summary>

```simple
# @req KPM-REQ-001 KPM-REQ-007 KPM-REQ-009
use compiler.common.api_surface_contract.{ApiSurface}
use compiler.common.shared_lib_flags.{get_shared_lib_flags}
use compiler.tools.verify.layer_call_scan.{scan_source_calls}

describe "kernel dependency contracts":
    it "constructs the API surface contract without tool ownership":
        val surface = ApiSurface.create("example")
        expect(surface.module).to_equal("example")
        expect(surface.functions.len()).to_equal(0)

    it "provides shared-library policy from the kernel contract":
        val flags = get_shared_lib_flags()
        expect(flags.output_extension.starts_with(".")).to_equal(true)
        expect(flags.defines).to_contain("SPL_SHARED_LIBRARY")

    it "keeps call scanning in semantic ownership":
        val scanned = scan_source_calls("caller.spl",
            r"use std.common.crypto.sha256.{sha256_text}" + "\n" + "fn run(): sha256_text(\"x\")")
        expect(scanned.module_path).to_equal("caller.spl")

    it "preserves literal import braces and the real source newline":
        val sha256_text = "must_not_be_interpolated"
        val content = r"use std.common.crypto.sha256.{sha256_text}" + "\n" + "fn run(): sha256_text(\"x\")"
        val lines = content.split("\n")
        expect(lines.len()).to_equal(2)
        expect(lines[0]).to_equal(r"use std.common.crypto.sha256.{sha256_text}")
        expect(lines[1]).to_equal("fn run(): sha256_text(\"x\")")
        val scanned = scan_source_calls("literal.spl", content)
        expect(scanned.module_path).to_equal("literal.spl")
```

</details>
