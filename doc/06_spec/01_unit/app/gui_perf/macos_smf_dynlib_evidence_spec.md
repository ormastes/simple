# Macos Smf Dynlib Evidence Specification

> Tests covering macOS SMF dynlib evidence helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Smf Dynlib Evidence Specification

## Scenarios

### macOS SMF dynlib evidence helpers

#### accepts only macOS arm64 hosts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only macOS arm64 hosts
   - Expected: gui_mac_smf_dynlib_is_arm64("arm64") is true
   - Expected: gui_mac_smf_dynlib_is_arm64("aarch64") is true
   - Expected: gui_mac_smf_dynlib_host_supported("macos", "arm64") is true
   - Expected: gui_mac_smf_dynlib_host_supported("linux", "arm64") is false
   - Expected: gui_mac_smf_dynlib_host_supported("macos", "x86_64") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only macOS arm64 hosts")
expect(gui_mac_smf_dynlib_is_arm64("arm64")).to_equal(true)
expect(gui_mac_smf_dynlib_is_arm64("aarch64")).to_equal(true)
expect(gui_mac_smf_dynlib_host_supported("macos", "arm64")).to_equal(true)
expect(gui_mac_smf_dynlib_host_supported("linux", "arm64")).to_equal(false)
expect(gui_mac_smf_dynlib_host_supported("macos", "x86_64")).to_equal(false)
```

</details>

#### uses stable macOS dylib and SMF artifact paths

- uses stable macOS dylib and SMF artifact paths
   - Expected: paths.dynlib_path equals `build/gui/libpure_gui_hot.dylib`
   - Expected: paths.smf_path equals `build/gui/pure_gui_hot.smf`
   - Expected: paths.wrapper_path equals `build/gui/smf_wrap_host_dynlib`
   - Expected: paths.probe_path equals `build/gui/smf_dynlib_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses stable macOS dylib and SMF artifact paths")
val paths = gui_mac_smf_dynlib_default_paths("bin/simple")
expect(paths.dynlib_path).to_equal("build/gui/libpure_gui_hot.dylib")
expect(paths.smf_path).to_equal("build/gui/pure_gui_hot.smf")
expect(paths.wrapper_path).to_equal("build/gui/smf_wrap_host_dynlib")
expect(paths.probe_path).to_equal("build/gui/smf_dynlib_probe")
```

</details>

<details>
<summary>Advanced: builds shell commands for cold orchestration outside the hot loop</summary>

#### builds shell commands for cold orchestration outside the hot loop

- builds shell commands for cold orchestration outside the hot loop
   - Expected: gui_mac_smf_dynlib_shell_quote("a'b") equals `'a'\\''b'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds shell commands for cold orchestration outside the hot loop")
val paths = gui_mac_smf_dynlib_default_paths("bin/simple")
expect(gui_mac_smf_dynlib_shell_quote("a'b")).to_equal("'a'\\''b'")
expect(gui_mac_smf_dynlib_compile_dynlib_command(paths)).to_contain("--shared")
expect(gui_mac_smf_dynlib_compile_dynlib_command(paths)).to_contain("libpure_gui_hot.dylib")
expect(gui_mac_smf_dynlib_wrap_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARCH='arm64'")
expect(gui_mac_smf_dynlib_wrap_command(paths)).to_contain("SIMPLE_GUI_SMF_OUTPUT='build/gui/pure_gui_hot.smf'")
expect(gui_mac_smf_dynlib_contract_command(paths)).to_contain("run src/app/gui_perf/smf_artifact_contract.spl")
expect(gui_mac_smf_dynlib_contract_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARTIFACT='build/gui/pure_gui_hot.smf'")
expect(gui_mac_smf_dynlib_qemu_parity_command(paths)).to_contain("run src/app/gui_perf/qemu_arm64_smf_parity_evidence.spl")
expect(gui_mac_smf_dynlib_qemu_parity_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARTIFACT='build/gui/pure_gui_hot.smf'")
expect(gui_mac_smf_dynlib_qemu_loader_parity_command(paths)).to_contain("run src/app/gui_perf/qemu_arm64_smf_loader_parity_evidence.spl")
expect(gui_mac_smf_dynlib_qemu_loader_parity_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARTIFACT='build/gui/pure_gui_hot.smf'")
expect(gui_mac_smf_dynlib_probe_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARTIFACT='build/gui/pure_gui_hot.smf'")
expect(gui_mac_smf_dynlib_probe_command_with_host(paths, "macos-arm64", "Apple M3")).to_contain("SIMPLE_GUI_DYNLIB_HOST_PROFILE='macos-arm64'")
expect(gui_mac_smf_dynlib_probe_command_with_host(paths, "macos-arm64", "Apple M3")).to_contain("SIMPLE_GUI_DYNLIB_HOST_CPU='Apple M3'")
```

</details>


</details>

#### accepts only role-2 arm64 SMF artifact contract rows

- accepts only role-2 arm64 SMF artifact contract rows
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(good) is true
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(missing) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(wrong_role) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(wrong_arch) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(no_dynlib) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(wrong_symbol) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(missing_sha) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(duplicate_sha) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(missing_size) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(zero_size) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(nonnumeric_size) is false
   - Expected: gui_mac_smf_dynlib_accepts_contract_row(duplicate_status) is false
   - Expected: gui_mac_smf_dynlib_select_stdout_row("warning before row\n" + good + "\n", "GUI_SMF_ARTIFACT_CONTRACT") equals `good`
   - Expected: gui_mac_smf_dynlib_select_stdout_row(good + "\n" + good, "GUI_SMF_ARTIFACT_CONTRACT") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only role-2 arm64 SMF artifact contract rows")
val good = "GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf sha256=abc size=4096 smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64"
val missing = good.replace("status=pass", "status=missing")
val wrong_role = good.replace("smf_role=2", "smf_role=1")
val wrong_arch = good.replace("arch=3", "arch=1")
val no_dynlib = good.replace("embedded_dynlib=true", "embedded_dynlib=false")
val wrong_symbol = good.replace("symbol=gui_dynlib_hot_probe_tick", "symbol=other")
val missing_sha = good.replace(" sha256=abc", "")
val duplicate_sha = good + " sha256=def"
val missing_size = good.replace(" size=4096", "")
val zero_size = good.replace("size=4096", "size=0")
val nonnumeric_size = good.replace("size=4096", "size=abc")
val duplicate_status = good + " status=missing"
expect(gui_mac_smf_dynlib_accepts_contract_row(good)).to_equal(true)
expect(gui_mac_smf_dynlib_accepts_contract_row(missing)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(wrong_role)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(wrong_arch)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(no_dynlib)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(wrong_symbol)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(missing_sha)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(duplicate_sha)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(missing_size)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(zero_size)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(nonnumeric_size)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(duplicate_status)).to_equal(false)
expect(gui_mac_smf_dynlib_select_stdout_row("warning before row\n" + good + "\n", "GUI_SMF_ARTIFACT_CONTRACT")).to_equal(good)
expect(gui_mac_smf_dynlib_select_stdout_row(good + "\n" + good, "GUI_SMF_ARTIFACT_CONTRACT")).to_equal("")
```

</details>

#### accepts only contract-only QEMU ARM64 SMF parity rows

- accepts only contract-only QEMU ARM64 SMF parity rows
   - Expected: gui_mac_smf_dynlib_accepts_qemu_parity_row(good) is true
   - Expected: gui_mac_smf_dynlib_accepts_qemu_parity_row(fail) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_parity_row(wrong_arch) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_parity_row(wrong_symbol) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_parity_row(live) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_parity_row(wrong_adapter) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_parity_row(duplicate_live) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only contract-only QEMU ARM64 SMF parity rows")
val good = "GUI_QEMU_ARM64_SMF_PARITY status=contract-pass artifact=build/gui/pure_gui_hot.smf smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick adapter=simpleos-framebuffer-virtio command_count=4 dirty_regions=4 same_artifact_contract=true live_qemu=false reason=same-smf-artifact-reaches-pure-gui-adapter"
val fail = good.replace("status=contract-pass", "status=contract-fail")
val wrong_arch = good.replace("arch=3", "arch=1")
val wrong_symbol = good.replace("symbol=gui_dynlib_hot_probe_tick", "symbol=other_symbol")
val live = good.replace("live_qemu=false", "live_qemu=true")
val wrong_adapter = good.replace("adapter=simpleos-framebuffer-virtio", "adapter=web-renderer")
val duplicate_live = good + " live_qemu=true"
expect(gui_mac_smf_dynlib_accepts_qemu_parity_row(good)).to_equal(true)
expect(gui_mac_smf_dynlib_accepts_qemu_parity_row(fail)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_parity_row(wrong_arch)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_parity_row(wrong_symbol)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_parity_row(live)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_parity_row(wrong_adapter)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_parity_row(duplicate_live)).to_equal(false)
```

</details>

#### accepts only SimpleOS loader-backed QEMU ARM64 SMF parity rows

- accepts only SimpleOS loader-backed QEMU ARM64 SMF parity rows
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(good) is true
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(fail) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(wrong_arch) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(wrong_symbol) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(wrong_loader) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(no_dynload) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(no_callable) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(live) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(wrong_adapter) is false
   - Expected: gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(duplicate_callable) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only SimpleOS loader-backed QEMU ARM64 SMF parity rows")
val good = "GUI_QEMU_ARM64_SMF_LOADER_PARITY status=loader-contract-pass artifact=build/gui/pure_gui_hot.smf smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick loader=smf_dynlib adapter=simpleos-framebuffer-virtio command_count=4 dirty_regions=4 dynload_pass=true process_callable=true live_qemu=false reason=smf-dynlib-artifact-reaches-pure-gui-adapter"
val fail = good.replace("status=loader-contract-pass", "status=loader-contract-fail")
val wrong_arch = good.replace("arch=3", "arch=1")
val wrong_symbol = good.replace("symbol=gui_dynlib_hot_probe_tick", "symbol=other_symbol")
val wrong_loader = good.replace("loader=smf_dynlib", "loader=artifact_contract_only")
val no_dynload = good.replace("dynload_pass=true", "dynload_pass=false")
val no_callable = good.replace("process_callable=true", "process_callable=false")
val live = good.replace("live_qemu=false", "live_qemu=true")
val wrong_adapter = good.replace("adapter=simpleos-framebuffer-virtio", "adapter=web-renderer")
val duplicate_callable = good + " process_callable=false"
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(good)).to_equal(true)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(fail)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(wrong_arch)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(wrong_symbol)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(wrong_loader)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(no_dynload)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(no_callable)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(live)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(wrong_adapter)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_qemu_loader_parity_row(duplicate_callable)).to_equal(false)
```

</details>

#### accepts only real SMF dynlib hot-call probe rows

- accepts only real SMF dynlib hot-call probe rows
   - Expected: gui_mac_smf_dynlib_row_value(good, "loader") equals `smf_dynlib`
   - Expected: gui_mac_smf_dynlib_row_key_count(duplicate_loader, "loader") equals `2`
   - Expected: gui_mac_smf_dynlib_row_i64(good, "p99_us") equals `1i64`
   - Expected: gui_mac_smf_dynlib_row_has_unsigned_decimal(good, "p99_us") is true
   - Expected: gui_mac_smf_dynlib_row_unsigned_i64(good, "p99_us") equals `1i64`
   - Expected: gui_mac_smf_dynlib_row_unsigned_i64(nonnumeric_p99, "p99_us") equals `-1i64`
   - Expected: gui_mac_smf_dynlib_unsigned_decimal_token("212") is true
   - Expected: gui_mac_smf_dynlib_unsigned_decimal_token("abc") is false
   - Expected: gui_mac_smf_dynlib_probe_metrics_valid(good) is true
   - Expected: gui_mac_smf_dynlib_probe_metrics_valid(measured) is true
   - Expected: gui_mac_smf_dynlib_probe_metrics_valid(p99_under_p95) is false
   - Expected: gui_mac_smf_dynlib_row_has_one_i64(duplicate_p99, "p99_us") is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(good) is true
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(measured) is true
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(wrong_artifact) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(host) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(host_sffi_diagnostic) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(native_dynload) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(native_host_dynload) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(direct) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(fail) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(wrong_cache) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(wrong_host) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(wrong_arch) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(wrong_profile) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(missing_cpu) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(wrong_symbol) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(partial_samples) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(wrong_expected) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(missing_p99) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(loose_threshold) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(over_threshold) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(inconsistent_pass) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(nonnumeric_p99) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(missing_warmup) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(zero_warmup) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(missing_p50) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(missing_p95) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(missing_max) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(p95_under_p50) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(p99_under_p95) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(max_under_p99) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(non_empty_error) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_loader) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_dynload) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_host_dynload) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_call_source) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_error) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_p99) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_threshold) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_samples) is false
   - Expected: gui_mac_smf_dynlib_accepts_probe_row(duplicate_expected_samples) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 94 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only real SMF dynlib hot-call probe rows")
val good = "GUI_DYNLIB_PERF artifact=build/gui/pure_gui_hot.smf dynlib_path=build/gui/pure_gui_hot.smf.extracted.dylib host_os=macos host_arch=arm64 host_profile=macos-arm64 host_cpu=Apple_M3 loader=smf_dynlib dynload=smf_dynlib host_dynload=sffi symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 expected_samples=128 warmup=16 p50_us=1 p95_us=1 p99_us=1 max_us=1 threshold_us=1000 pass=true error="
val measured = "GUI_DYNLIB_PERF artifact=build/gui/pure_gui_hot.smf dynlib_path=build/gui/pure_gui_hot.smf.extracted.dylib host_os=macos host_arch=arm64 host_profile=macos-arm64 host_cpu=Apple_M3 loader=smf_dynlib dynload=smf_dynlib host_dynload=sffi symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 expected_samples=128 warmup=16 p50_us=23 p95_us=30 p99_us=212 max_us=404 threshold_us=1000 pass=true error="
val wrong_artifact = good.replace("artifact=build/gui/pure_gui_hot.smf", "artifact=build/gui/other.smf")
val host = good.replace("loader=smf_dynlib", "loader=host_dynlib")
val host_sffi_diagnostic = good.replace("loader=smf_dynlib dynload=smf_dynlib", "loader=host_dynlib dynload=host_dynlib_diagnostic")
val native_dynload = good.replace("dynload=smf_dynlib", "dynload=native")
val native_host_dynload = good.replace("host_dynload=sffi", "host_dynload=native")
val direct = good.replace("call_source=dynlib_symbol_call", "call_source=direct_simple")
val fail = good.replace("pass=true error=", "pass=false error=not-smf-dynlib")
val wrong_cache = good.replace("dynlib_path=build/gui/pure_gui_hot.smf.extracted.dylib", "dynlib_path=")
val wrong_host = good.replace("host_os=macos", "host_os=linux")
val wrong_arch = good.replace("host_arch=arm64", "host_arch=x86_64")
val wrong_profile = good.replace("host_profile=macos-arm64", "host_profile=linux-x86_64")
val missing_cpu = good.replace("host_cpu=Apple_M3", "host_cpu=unknown")
val wrong_symbol = good.replace("symbol=gui_dynlib_hot_probe_tick", "symbol=other_symbol")
val partial_samples = good.replace("samples=128", "samples=64")
val wrong_expected = good.replace("expected_samples=128", "expected_samples=64")
val missing_p99 = good.replace("p99_us=1 ", "")
val loose_threshold = good.replace("threshold_us=1000", "threshold_us=5000")
val over_threshold = good.replace("p99_us=1", "p99_us=1000")
val inconsistent_pass = good.replace("p99_us=1", "p99_us=2500")
val nonnumeric_p99 = good.replace("p99_us=1", "p99_us=abc")
val missing_warmup = good.replace(" warmup=16", "")
val zero_warmup = good.replace("warmup=16", "warmup=0")
val missing_p50 = good.replace(" p50_us=1", "")
val missing_p95 = good.replace(" p95_us=1", "")
val missing_max = good.replace(" max_us=1", "")
val p95_under_p50 = good.replace("p50_us=1 p95_us=1", "p50_us=2 p95_us=1")
val p99_under_p95 = good.replace("p95_us=1 p99_us=1", "p95_us=2 p99_us=1")
val max_under_p99 = good.replace("p99_us=1 max_us=1", "p99_us=2 max_us=1")
val non_empty_error = good.replace("error=", "error=p99-over-threshold")
val duplicate_loader = good + " loader=host_dynlib"
val duplicate_dynload = good + " dynload=native"
val duplicate_host_dynload = good + " host_dynload=native"
val duplicate_call_source = good + " call_source=direct_simple"
val duplicate_error = good + " error=not-smf-dynlib"
val duplicate_p99 = good + " p99_us=5000"
val duplicate_threshold = good + " threshold_us=5000"
val duplicate_samples = good + " samples=64"
val duplicate_expected_samples = good + " expected_samples=64"
expect(gui_mac_smf_dynlib_row_value(good, "loader")).to_equal("smf_dynlib")
expect(gui_mac_smf_dynlib_row_key_count(duplicate_loader, "loader")).to_equal(2)
expect(gui_mac_smf_dynlib_row_i64(good, "p99_us")).to_equal(1i64)
expect(gui_mac_smf_dynlib_row_has_unsigned_decimal(good, "p99_us")).to_equal(true)
expect(gui_mac_smf_dynlib_row_unsigned_i64(good, "p99_us")).to_equal(1i64)
expect(gui_mac_smf_dynlib_row_unsigned_i64(nonnumeric_p99, "p99_us")).to_equal(-1i64)
expect(gui_mac_smf_dynlib_unsigned_decimal_token("212")).to_equal(true)
expect(gui_mac_smf_dynlib_unsigned_decimal_token("abc")).to_equal(false)
expect(gui_mac_smf_dynlib_probe_metrics_valid(good)).to_equal(true)
expect(gui_mac_smf_dynlib_probe_metrics_valid(measured)).to_equal(true)
expect(gui_mac_smf_dynlib_probe_metrics_valid(p99_under_p95)).to_equal(false)
expect(gui_mac_smf_dynlib_row_has_one_i64(duplicate_p99, "p99_us")).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(good)).to_equal(true)
expect(gui_mac_smf_dynlib_accepts_probe_row(measured)).to_equal(true)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_artifact)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(host)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(host_sffi_diagnostic)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(native_dynload)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(native_host_dynload)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(direct)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(fail)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_cache)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_host)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_arch)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_profile)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(missing_cpu)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_symbol)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(partial_samples)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_expected)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(missing_p99)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(loose_threshold)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(over_threshold)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(inconsistent_pass)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(nonnumeric_p99)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(missing_warmup)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(zero_warmup)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(missing_p50)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(missing_p95)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(missing_max)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(p95_under_p50)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(p99_under_p95)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(max_under_p99)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(non_empty_error)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_loader)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_dynload)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_host_dynload)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_call_source)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_error)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_p99)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_threshold)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_samples)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(duplicate_expected_samples)).to_equal(false)
```

</details>

#### reports non-mac hosts as explicit skips

- reports non-mac hosts as explicit skips


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports non-mac hosts as explicit skips")
val row = gui_mac_smf_dynlib_skip_row("linux", "x86_64")
expect(row).to_contain("status=skip")
expect(row).to_contain("requires-macos-arm64")
```

</details>

#### reports mac pass evidence with host profile and CPU details

- reports mac pass evidence with host profile and CPU details
   - Expected: gui_mac_smf_dynlib_evidence_token("Apple M3 Pro") equals `Apple_M3_Pro`
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row) is true
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row.replace("host_cpu=Apple_M3", "host_cpu=unknown")) is false
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row.replace("status=pass", "status=skip")) is false
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row.replace("artifact_sha256=abc", "artifact_sha256=")) is false
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row.replace("artifact_size=4096", "artifact_size=0")) is false
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row.replace("artifact_size=4096", "artifact_size=abc")) is false
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row + " artifact_sha256=def") is false
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row + " artifact_size=8192") is false
   - Expected: gui_mac_smf_dynlib_accepts_pass_row(row + " status=skip") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports mac pass evidence with host profile and CPU details")
expect(gui_mac_smf_dynlib_evidence_token("Apple M3 Pro")).to_equal("Apple_M3_Pro")
val row = gui_mac_smf_dynlib_pass_row("macos", "arm64", "macos-arm64", "Apple M3", "build/gui/pure_gui_hot.smf", "abc", "4096")
expect(row).to_contain("status=pass")
expect(row).to_contain("host_os=macos")
expect(row).to_contain("arch=arm64")
expect(row).to_contain("host_profile=macos-arm64")
expect(row).to_contain("host_cpu=Apple_M3")
expect(row).to_contain("artifact=build/gui/pure_gui_hot.smf")
expect(row).to_contain("artifact_sha256=abc")
expect(row).to_contain("artifact_size=4096")
expect(gui_mac_smf_dynlib_accepts_pass_row(row)).to_equal(true)
expect(gui_mac_smf_dynlib_accepts_pass_row(row.replace("host_cpu=Apple_M3", "host_cpu=unknown"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_pass_row(row.replace("status=pass", "status=skip"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_pass_row(row.replace("artifact_sha256=abc", "artifact_sha256="))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_pass_row(row.replace("artifact_size=4096", "artifact_size=0"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_pass_row(row.replace("artifact_size=4096", "artifact_size=abc"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_pass_row(row + " artifact_sha256=def")).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_pass_row(row + " artifact_size=8192")).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_pass_row(row + " status=skip")).to_equal(false)
```

</details>

#### accepts only full ordered mac SMF dynlib evidence transcripts

- accepts only full ordered mac SMF dynlib evidence transcripts
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full) is true
   - Expected: gui_mac_smf_dynlib_transcript_check_row(full) equals `GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass`
   - Expected: gui_mac_smf_dynlib_accepts_transcript(contract + "\n" + qemu + "\n" + probe + "\n" + pass_row) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(contract + "\n" + loader + "\n" + qemu + "\n" + probe + "\n" + pass_row) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full.replace("call_source=dynlib_symbol_call", "call_source=direct_simple")) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full.replace("artifact=build/gui/pure_gui_hot.smf", "artifact=build/gui/other.smf")) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full.replace("dynload=smf_dynlib", "dynload=native")) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full.replace("host_dynload=sffi", "host_dynload=native")) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full.replace("loader=smf_dynlib dynload=smf_dynlib", "loader=host_dynlib dynload=host_dynlib_diagnostic")) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full.replace("artifact_sha256=abc", "artifact_sha256=def")) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full.replace("artifact_size=4096", "artifact_size=8192")) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(contract + "\nGUI_DYNLIB_PERF pass=false error=p99-over-threshold\n" + qemu + "\n" + loader + "\n" + probe + "\n" + pass_row) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript(full + "\nGUI_DYNLIB_PERF pass=false error=p99-over-threshold") is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript("Compiled src/app/gui_perf/pure_gui_hot_dynlib_export.spl\n" + full) is false
   - Expected: gui_mac_smf_dynlib_accepts_transcript("GUI_SMF_WRAP ok=true input=build/gui/libpure_gui_hot.dylib output=build/gui/pure_gui_hot.smf\n" + full) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only full ordered mac SMF dynlib evidence transcripts")
val contract = "GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf sha256=abc size=4096 smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64"
val qemu = "GUI_QEMU_ARM64_SMF_PARITY status=contract-pass artifact=build/gui/pure_gui_hot.smf smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick adapter=simpleos-framebuffer-virtio command_count=4 dirty_regions=4 same_artifact_contract=true live_qemu=false reason=same-smf-artifact-reaches-pure-gui-adapter"
val loader = "GUI_QEMU_ARM64_SMF_LOADER_PARITY status=loader-contract-pass artifact=build/gui/pure_gui_hot.smf smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick loader=smf_dynlib adapter=simpleos-framebuffer-virtio command_count=4 dirty_regions=4 dynload_pass=true process_callable=true live_qemu=false reason=smf-dynlib-artifact-reaches-pure-gui-adapter"
val probe = "GUI_DYNLIB_PERF artifact=build/gui/pure_gui_hot.smf dynlib_path=build/gui/pure_gui_hot.smf.extracted.dylib host_os=macos host_arch=arm64 host_profile=macos-arm64 host_cpu=Apple_M3 loader=smf_dynlib dynload=smf_dynlib host_dynload=sffi symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 expected_samples=128 warmup=16 p50_us=1 p95_us=1 p99_us=1 max_us=1 threshold_us=1000 pass=true error="
val pass_row = gui_mac_smf_dynlib_pass_row("macos", "arm64", "macos-arm64", "Apple_M3", "build/gui/pure_gui_hot.smf", "abc", "4096")
val full = contract + "\n" + qemu + "\n" + loader + "\n" + probe + "\n" + pass_row
expect(gui_mac_smf_dynlib_accepts_transcript(full)).to_equal(true)
expect(gui_mac_smf_dynlib_transcript_check_row(full)).to_equal("GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass")
expect(gui_mac_smf_dynlib_accepts_transcript(contract + "\n" + qemu + "\n" + probe + "\n" + pass_row)).to_equal(false)
expect(gui_mac_smf_dynlib_transcript_check_row(contract + "\n" + qemu + "\n" + probe + "\n" + pass_row)).to_contain("status=fail")
expect(gui_mac_smf_dynlib_accepts_transcript(contract + "\n" + loader + "\n" + qemu + "\n" + probe + "\n" + pass_row)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(full.replace("call_source=dynlib_symbol_call", "call_source=direct_simple"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(full.replace("artifact=build/gui/pure_gui_hot.smf", "artifact=build/gui/other.smf"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(full.replace("dynload=smf_dynlib", "dynload=native"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(full.replace("host_dynload=sffi", "host_dynload=native"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(full.replace("loader=smf_dynlib dynload=smf_dynlib", "loader=host_dynlib dynload=host_dynlib_diagnostic"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(full.replace("artifact_sha256=abc", "artifact_sha256=def"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(full.replace("artifact_size=4096", "artifact_size=8192"))).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(contract + "\nGUI_DYNLIB_PERF pass=false error=p99-over-threshold\n" + qemu + "\n" + loader + "\n" + probe + "\n" + pass_row)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript(full + "\nGUI_DYNLIB_PERF pass=false error=p99-over-threshold")).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript("Compiled src/app/gui_perf/pure_gui_hot_dynlib_export.spl\n" + full)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_transcript("GUI_SMF_WRAP ok=true input=build/gui/libpure_gui_hot.dylib output=build/gui/pure_gui_hot.smf\n" + full)).to_equal(false)
```

</details>

#### keeps cold orchestration stdout out of the strict release transcript

- keeps cold orchestration stdout out of the strict release transcript
   - Expected: source does not contain `print stdout.trim()`
   - Expected: source contains `val (_stdout, stderr, code) = _shell(command, timeout_ms)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps cold orchestration stdout out of the strict release transcript")
val source = rt_file_read_text("src/app/gui_perf/macos_smf_dynlib_evidence.spl")
expect(source.contains("print stdout.trim()")).to_equal(false)
expect(source.contains("val (_stdout, stderr, code) = _shell(command, timeout_ms)")).to_equal(true)
expect(source).to_contain("gui_mac_smf_dynlib_select_stdout_row(contract_out, \"GUI_SMF_ARTIFACT_CONTRACT\")")
expect(source).to_contain("gui_mac_smf_dynlib_select_stdout_row(probe_out, \"GUI_DYNLIB_PERF\")")
```

</details>

#### creates the selected transcript path parent directory

- creates the selected transcript path parent directory
   - Expected: gui_mac_smf_dynlib_transcript_parent_dir("build/gui/macos_smf_dynlib_transcript.log") equals `build/gui`
   - Expected: gui_mac_smf_dynlib_transcript_parent_dir("macos_smf_dynlib_transcript.log") equals `.`
   - Expected: gui_mac_smf_dynlib_transcript_parent_dir("/tmp/gui/transcript.log") equals `/tmp/gui`
   - Expected: gui_mac_smf_dynlib_transcript_mkdir_command("build/gui run/a'b/transcript.log") equals `mkdir -p 'build/gui run/a'\\''b'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates the selected transcript path parent directory")
expect(gui_mac_smf_dynlib_transcript_parent_dir("build/gui/macos_smf_dynlib_transcript.log")).to_equal("build/gui")
expect(gui_mac_smf_dynlib_transcript_parent_dir("macos_smf_dynlib_transcript.log")).to_equal(".")
expect(gui_mac_smf_dynlib_transcript_parent_dir("/tmp/gui/transcript.log")).to_equal("/tmp/gui")
expect(gui_mac_smf_dynlib_transcript_mkdir_command("build/gui run/a'b/transcript.log")).to_equal("mkdir -p 'build/gui run/a'\\''b'")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering macOS SMF dynlib evidence helpers.
- macOS SMF dynlib evidence helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6e3a0edb93fc4ff0630e9e176052214f0465bcf020973f2a87aa8aee65dd8c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6e3a0edb93fc4ff0630e9e176052214f0465bcf020973f2a87aa8aee65dd8c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6e3a0edb93fc4ff0630e9e176052214f0465bcf020973f2a87aa8aee65dd8c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl
mirror: doc/06_spec/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=40
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only macOS arm64 hosts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses stable macOS dylib and SMF artifact paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds shell commands for cold orchestration outside the hot loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
