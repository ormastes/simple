# Simpleos Riscv Network Gate Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Riscv Network Gate Specification

## Scenarios

### SimpleOS RISC-V network readiness gate

#### keeps the RV64 boot handoff freestanding and QEMU-memory explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boot = rt_file_read_text("src/os/kernel/arch/riscv64/boot.spl")

expect(boot).to_contain("extern fn log_raw_println(msg: text)")
expect(boot).to_contain("extern fn rt_riscv_qemu_ram_base() -> u64")
expect(boot).to_contain("extern fn rt_riscv_qemu_heap_size() -> u64")
expect(boot).to_contain("extern fn rt_riscv_noalloc_pmm_init(")
expect(boot).to_contain("rt_riscv_noalloc_pmm_init(")
expect(boot).to_contain("riscv_noalloc_heap_init(")
expect(boot).to_contain("rt_riscv_qemu_ram_base()")
expect(boot).to_contain("rt_riscv_qemu_heap_start()")
expect(boot).to_contain("os_main()")
expect(boot.index_of("use os.kernel.log.klog_api") ?? -1).to_equal(-1)
expect(boot.index_of("riscv_boot_mem_init") ?? -1).to_equal(-1)
```

</details>

#### keeps hosted boot logging out of the HTTP handoff closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val os_main = rt_file_read_text("src/os/kernel/boot/os_main.spl")
val services = rt_file_read_text("src/os/kernel/boot/riscv_services.spl")
val http = rt_file_read_text("src/os/kernel/boot/http_baremetal.spl")

expect(os_main).to_contain("extern fn log_raw_println(msg: text)")
expect(services).to_contain("extern fn log_raw_println(msg: text)")
expect(http).to_contain("extern fn log_raw_println(msg: text)")
expect(os_main.index_of("use os.kernel.log.klog_api") ?? -1).to_equal(-1)
expect(services.index_of("use os.kernel.log.klog_api") ?? -1).to_equal(-1)
expect(http.index_of("use os.kernel.log.klog_api") ?? -1).to_equal(-1)
```

</details>

#### keeps the freestanding C runtime linked without hosted OS helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = rt_file_read_text("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")

expect(runtime).to_contain("void unsafe(void)")
expect(runtime).to_contain("spl_i64 rt_riscv_noalloc_pmm_init(")
expect(runtime).to_contain("uart_line(\"PMM OK\")")
expect(runtime).to_contain("RT_PCI_IO_BASE")
expect(runtime).to_contain("#define RT_PCI_MAX_DEVICES 32")
expect(runtime).to_contain("RT_VIRTIO_NET_TX_QUEUE")
expect(runtime).to_contain("rt_submit_tx_probe")
expect(runtime).to_contain("RT_NET_RX_POST_COUNT")
expect(runtime).to_contain("RT_VIRTIO_GPU_LEGACY_DEVICE_ID")
expect(runtime).to_contain("RT_PCI_LEGACY_GPU_IO_PORT")
expect(runtime).to_contain("RT_VIRTIO_BLK_LEGACY_DEVICE_ID")
expect(runtime).to_contain("RT_PCI_LEGACY_BLK_IO_PORT")
expect(runtime).to_contain("RT_NVFS_MAGIC")
expect(runtime).to_contain("rt_gpu_cmd_get_display_info")
expect(runtime).to_contain("rt_gpu_cmd_transfer_flush")
expect(runtime).to_contain("spl_i64 rt_storage_init(void)")
expect(runtime).to_contain("spl_i64 rt_storage_read_probe(void)")
expect(runtime).to_contain("spl_u64 rt_riscv_qemu_ram_base(void)")
expect(runtime).to_contain("return 0x80000000ULL;")
expect(runtime).to_contain("return 0x87000000ULL;")
expect(runtime).to_contain("spl_i64 rt_time_now_unix_micros(void)")
expect(runtime).to_contain("spl_u64 rt_riscv_seed(void)")
expect(runtime).to_contain("void *boot_alloc;")
expect(runtime).to_contain("kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(size)")
expect(runtime).to_contain("if (boot_alloc)")
expect(runtime).to_contain("rt_entropy_hardware_ready(void)")
expect(runtime).to_contain("return 0;")
```

</details>

#### requires packet TX and RX readiness before reporting network ready

- Require every packet and socket facade gate before readiness


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require every packet and socket facade gate before readiness")
val services = rt_file_read_text("src/os/kernel/boot/riscv_services.spl")

expect(services).to_contain("extern fn rt_net_tx_test() -> i64")
expect(services).to_contain("extern fn rt_net_rx_ready() -> i64")
expect(services).to_contain("val device_id = rt_pci_get_field(i, 6)")
expect(services).to_contain("device_id == 0x1000 or device_id == 0x1041")
expect(services).to_contain("val tx_rc = _decode_riscv_status(rt_net_tx_test())")
expect(services).to_contain("val rx_rc = _decode_riscv_status(rt_net_rx_ready())")
expect(services).to_contain("[net-riscv] Network packet TX unavailable rc=")
expect(services).to_contain("[net-riscv] Network packet TX ready")
expect(services).to_contain("[net-riscv] Network packet RX unavailable rc=")
expect(services).to_contain("network_ok = 1")
expect(services).to_contain("if not net_facade_linked:\n                                    log_raw_println(\"[net-riscv] Net socket facade unavailable\")\n                                    network_ok = 0\n                                else:\n                                    val tcp_probe_fd = boot_tcp_probe_bind(\"0.0.0.0:0\")")

val tx_probe = services.find("val tx_rc = _decode_riscv_status(rt_net_tx_test())")
val rx_probe = services.find("val rx_rc = _decode_riscv_status(rt_net_rx_ready())")
val ready_set = services.find("[net-riscv] Network service ready")
expect(tx_probe).to_be_greater_than(-1)
expect(rx_probe).to_be_greater_than(-1)
expect(rx_probe).to_be_greater_than(tx_probe)
expect(ready_set).to_be_greater_than(rx_probe)
```

</details>

#### keeps the freestanding runtime on real virtio packet IO

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = rt_file_read_text("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")

expect(runtime).to_contain("spl_i64 rt_net_tx_test(void)")
expect(runtime).to_contain("spl_i64 rt_net_rx_ready(void)")
expect(runtime).to_contain("RT_VIRTIO_NET_LEGACY_DEVICE_ID")
expect(runtime).to_contain("RT_VIRTIO_NET_MODERN_DEVICE_ID")
expect(runtime).to_contain("rt_pci_is_virtio_net")
expect(runtime).to_contain("rt_poll_rx_once")
expect(runtime).to_contain("rt_process_rx_frame")
expect(runtime).to_contain("rt_process_tcp")
expect(runtime).to_contain("rt_send_arp_reply")
expect(runtime).to_contain("rt_send_tcp_packet")
expect(runtime).to_contain("fallback_json_response")
expect(runtime).to_contain("fallback_html_response")
```

</details>

#### uses a real virtio-gpu control queue for display readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = rt_file_read_text("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")
val services = rt_file_read_text("src/os/kernel/boot/riscv_services.spl")
val script = rt_file_read_text("scripts/qemu/qemu_rv64_http_test.shs")

expect(runtime).to_contain("spl_i64 rt_display_init(void)")
expect(runtime).to_contain("rt_pci_is_virtio_gpu")
expect(runtime).to_contain("RT_VIRTIO_GPU_MODERN_DEVICE_ID")
expect(runtime).to_contain("rt_gpu_setup_modern")
expect(runtime).to_contain("RT_VIRTIO_MODERN_QUEUE_DESC_LO")
expect(runtime).to_contain("RT_GPU_CMD_GET_DISPLAY_INFO")
expect(runtime).to_contain("RT_GPU_CMD_RESOURCE_CREATE_2D")
expect(runtime).to_contain("RT_GPU_CMD_RESOURCE_ATTACH_BACKING")
expect(runtime).to_contain("RT_GPU_CMD_SET_SCANOUT")
expect(runtime).to_contain("RT_GPU_CMD_TRANSFER_TO_HOST_2D")
expect(runtime).to_contain("RT_GPU_CMD_RESOURCE_FLUSH")
expect(runtime).to_contain("return g_rt_display_ready ? RT_GPU_WIDTH : 0;")
expect(runtime).to_contain("return g_rt_display_ready ? RT_GPU_HEIGHT : 0;")
expect(runtime.contains("rt_gpu_fill_test_pattern")).to_be(false)
expect(runtime.index_of("spl_i64 rt_display_init(void) {\n    return -1;") ?? -1).to_equal(-1)
expect(services).to_contain("[display-riscv] Display unavailable")
expect(services).to_contain("riscv_display_width = riscv64_display_width()")
expect(services.contains("riscv64_display_present()")).to_equal(false)
expect(services).to_contain("[display-riscv] Display service ready: {{riscv_display_width}}x{{riscv_display_height}} framebuffer")
expect(script).to_contain("--with-display")
expect(script).to_contain("virtio-gpu-pci,disable-modern=on,disable-legacy=off")
expect(script).to_contain("Display service ready")
```

</details>

#### uses a real virtio-blk queue, NVFS superblock, and arena payload for storage readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = rt_file_read_text("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")
val services = rt_file_read_text("src/os/kernel/boot/riscv_services.spl")
val script = rt_file_read_text("scripts/qemu/qemu_rv64_http_test.shs")

expect(runtime).to_contain("RT_VIRTIO_BLK_LEGACY_DEVICE_ID")
expect(runtime).to_contain("RT_VIRTIO_BLK_MODERN_DEVICE_ID")
expect(runtime).to_contain("RT_VIRTIO_BLK_QUEUE")
expect(runtime).to_contain("VIRTIO_BLK_T_IN")
expect(runtime).to_contain("rt_pci_is_virtio_blk")
expect(runtime).to_contain("rt_storage_read_sector")
expect(runtime).to_contain("rt_storage_probe_nvfs_superblock")
expect(runtime).to_contain("rt_storage_probe_nvfs_arena_payload")
expect(runtime).to_contain("rt_storage_sector_has_nvfs_superblock")
expect(runtime).to_contain("RT_NVFS_MAGIC")
expect(runtime).to_contain("RT_NVFS_VERSION")
expect(runtime).to_contain("RT_VIRTQ_DESC_F_NEXT | RT_VIRTQ_DESC_F_WRITE")
expect(runtime).to_contain("rt_io_write16(g_rt_blk_bar0, RT_VIRTIO_PCI_QUEUE_NOTIFY, RT_VIRTIO_BLK_QUEUE)")
expect(runtime.index_of("spl_i64 rt_storage_init(void) {\n    return -1;") ?? -1).to_equal(-1)
expect(services).to_contain("extern fn rt_storage_init() -> i64")
expect(services).to_contain("extern fn rt_storage_read_probe() -> i64")
expect(services).to_contain("extern fn rt_storage_nvfs_ready() -> i64")
expect(services).to_contain("extern fn rt_storage_nvfs_arena_ready() -> i64")
expect(services).to_contain("[storage-riscv] Storage unavailable rc=")
expect(services).to_contain("[storage-riscv] NVFS superblock probe passed")
expect(services).to_contain("[storage-riscv] NVFS arena payload probe passed")
expect(services).to_contain("[storage-riscv] Storage service ready")
expect(services).to_contain("fn riscv_storage_ready() -> bool")
expect(services).to_contain("[fs-riscv] NVFS root superblock ready")
expect(services).to_contain("[fs-riscv] NVFS arena payload ready")
expect(services).to_contain("[init] filesystem: nvfs-superblock-ready")
expect(services).to_contain("fn riscv_filesystem_ready() -> bool")
expect(script).to_contain("--with-storage")
expect(script).to_contain("virtio-blk-pci,drive=blk0")
expect(script).to_contain("\\123\\106\\126\\116\\002\\000\\000\\000")
expect(script).to_contain("SIMPLEOS_NVFS_ARENA_FILE")
expect(script).to_contain("Storage service ready")
expect(script).to_contain("NVFS root superblock ready")
expect(script).to_contain("[fs-riscv] NVFS arena payload ready")
```

</details>

#### routes weak C TCP fallbacks through the boot packet provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = rt_file_read_text("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")

expect(runtime).to_contain("__attribute__((weak)) spl_i64 rt_io_tcp_bind")
expect(runtime).to_contain("__attribute__((weak)) spl_i64 rt_io_tcp_write_text")
expect(runtime).to_contain("__attribute__((weak)) spl_i64 rt_io_tcp_close")
expect(runtime.index_of("return text ? (spl_i64)text->len : -1;") ?? -1).to_equal(-1)
expect(runtime).to_contain("return rt_boot_tcp_bind(addr);")
expect(runtime).to_contain("return rt_boot_tcp_accept_timeout(fd, ms);")
expect(runtime).to_contain("return rt_boot_tcp_write_text(fd, data);")
expect(runtime).to_contain("return rt_boot_tcp_close(fd) == 0 ? 11 : 19;")
```

</details>

#### keeps netstack init unavailable until packet TX and RX are ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val net_init = rt_file_read_text("src/os/services/netstack/netstack_init.spl")

expect(net_init).to_contain("extern fn rt_net_tx_test() -> i64")
expect(net_init).to_contain("extern fn rt_net_rx_ready() -> i64")
expect(net_init).to_contain("val tx_ready = _decode_riscv_status(rt_net_tx_test())")
expect(net_init).to_contain("val rx_ready = _decode_riscv_status(rt_net_rx_ready())")
expect(net_init).to_contain("[net-init] C network TX unavailable rc=")
expect(net_init).to_contain("[net-init] C network RX unavailable rc=")
expect(net_init).to_contain("g_net_initialized = true")

val tx_probe = net_init.find("val tx_ready = _decode_riscv_status(rt_net_tx_test())")
val rx_probe = net_init.find("val rx_ready = _decode_riscv_status(rt_net_rx_ready())")
val ready_set = net_init.find("g_net_initialized = true")
expect(tx_probe).to_be_greater_than(-1)
expect(rx_probe).to_be_greater_than(-1)
expect(rx_probe).to_be_greater_than(tx_probe)
expect(ready_set).to_be_greater_than(rx_probe)
```

</details>

#### fails closed in the baremetal IoDriver shim until packet TX and RX are ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shim = rt_file_read_text("src/os/kernel/net/driver_shim.spl")

expect(shim).to_contain("extern fn rt_net_tx_test() -> i64")
expect(shim).to_contain("extern fn rt_net_rx_ready() -> i64")
expect(shim).to_contain("fn driver_shim_packet_io_ready() -> bool")
expect(shim).to_contain("rt_net_tx_test() == 0 and rt_net_rx_ready() == 0")
expect(shim).to_contain("rt_io_tcp_write_text(fd, data)")
expect(shim).to_contain("if written < 0:\n        return -1")
expect(shim).to_contain("result_val: written")
expect(shim).to_contain("if not driver_shim_packet_io_ready():\n        return -1")
expect(shim).to_contain("if not driver_shim_packet_io_ready():\n        return RT_LINK_STATE_UNKNOWN")
expect(shim).to_contain("if not driver_shim_packet_io_ready():\n        return \"\"")
expect(shim.index_of("data discarded") ?? -1).to_equal(-1)
expect(shim.index_of("baremetal always reports UP") ?? -1).to_equal(-1)
```

</details>

#### does not let TCP shims fake listener or write success without netstack

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shim = rt_file_read_text("src/os/kernel/net/tcp_shim.spl")

expect(shim).to_contain("No fake listener is created")
expect(shim).to_contain("if not net_tcp_available():\n        return -1")
expect(shim.index_of("g_next_os_fd") ?? -1).to_equal(-1)
expect(shim.index_of("data.len().to_i64()") ?? -1).to_equal(-1)
expect(shim).to_contain("Returns -1 if the fd is invalid or the netstack is unavailable")
```

</details>

#### lets the sync HTTP server serve inline when thread spawn is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = rt_file_read_text("src/lib/nogc_sync_mut/http_server/server.spl")
val response = rt_file_read_text("src/lib/nogc_sync_mut/http_server/response.spl")

expect(server).to_contain("val handler = thread_spawn_with_args(stream, self")
expect(server).to_contain("if handler.handle < 0:")
expect(server).to_contain("SimpleHttpServer.handle_connection_static(self, stream)")
expect(server).to_contain("if not write_response(stream, resp):")
expect(response).to_contain("match stream.write_text(wire):")
expect(server).to_contain("handler.free()")
```

</details>

#### reports sync HTTP response write failure on fail-closed TCP streams

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stream = TcpStream(fd: -1, open: true)

expect(write_response(stream, HttpResponse.ok("hello"))).to_equal(false)
expect(write_error(stream, HttpStatus.BadRequest, "bad request")).to_equal(false)
```

</details>

#### keeps the boot-local TCP shim delegated to the packet provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boot_shim = rt_file_read_text("src/os/kernel/boot/tcp_baremetal_min.spl")

expect(boot_shim).to_contain("extern fn rt_boot_tcp_bind(addr: text) -> i64")
expect(boot_shim).to_contain("pub fn rt_io_tcp_bind(addr: text) -> i64:\n    boot_tcp_probe_bind(addr)")
expect(boot_shim).to_contain("pub fn rt_io_tcp_write_text(fd: i64, data: text) -> i64:\n    rt_boot_tcp_write_text(fd, data)")
```

</details>

### SimpleOS RISC-V QEMU HTTP scripts

#### requires live POST database state evidence beyond boot readiness

This scenario accepts a boot only when the canonical HTTP listener owns one
persistent database service, CREATE precedes INSERT and SELECT in the same
guest session, every HTTP response is retained, and the checker rejects
readiness-only evidence.

- Inspect the live guest request client
   - Expected: checker.index_of("Bootstrap TCP shim bound on 0.0.0.0:8080") ?? -1 equals `-1`
   - Expected: listener.index_of("SimpleDbService.new()") ?? -1 equals `-1`
- Require CREATE INSERT and SELECT in one boot session
- Reject readiness-only retained evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the live guest request client")
val smoke = rt_file_read_text("scripts/qemu/qemu_rv64_http_test.shs")
val checker = rt_file_read_text("scripts/qemu/check_simpleos_rv64_db_server.shs")
val service = rt_file_read_text("src/os/services/database/simple_db_service.spl")
val listener = rt_file_read_text("src/os/kernel/boot/http_baremetal.spl")

expect(smoke).to_contain("--with-db")
expect(smoke).to_contain("WITH_DB=true\n      WITH_STORAGE=true")
expect(smoke).to_contain("printf 'POST /db HTTP/1.0")
expect(smoke).to_contain("printf '%s\\n' \"$DB_RESPONSE\" > \"$DB_QUERY_LOG\"")
expect(smoke).to_contain("[ ! \"$BUILD_STAMP\" -nt \"$ELF\" ]")
expect(smoke).to_contain("^simple_bin=.*(compiler_rust|simple_seed)")
expect(checker).to_contain("[http_baremetal] Listening on 0.0.0.0:8080")
expect(listener).to_contain("[http_baremetal] Listening on 0.0.0.0:8080")
expect(checker.index_of("Bootstrap TCP shim bound on 0.0.0.0:8080") ?? -1).to_equal(-1)
expect(service).to_contain("var g_simple_db_service: SimpleDbService = SimpleDbService(tables: [], rows: [])")
expect(listener).to_contain("simple_db_execute_http_request(request)")
expect(listener.index_of("SimpleDbService.new()") ?? -1).to_equal(-1)

step("Require CREATE INSERT and SELECT in one boot session")
val create = smoke.find("db_request 'CREATE codex'")
val insert = smoke.find("db_request 'INSERT codex answer codex-41'")
val select = smoke.find("db_request 'SELECT codex answer'")
expect(create).to_be_greater_than(-1)
expect(insert).to_be_greater_than(create)
expect(select).to_be_greater_than(insert)

step("Reject readiness-only retained evidence")
expect(checker).to_contain("[ -f \"$db_query_log\" ] || fail \"db_query_log_missing\"")
expect(checker).to_contain("grep -c 'HTTP/1.1 200 OK' \"$db_query_log\"")
expect(checker).to_contain("grep -q 'OK CREATE' \"$db_query_log\"")
expect(checker).to_contain("grep -q 'OK INSERT' \"$db_query_log\"")
expect(checker).to_contain("fail \"db_negative_content_length\"")
val readiness = checker.find("pass \"serial_live_request_path_ready\"")
val selected_value = checker.find("grep -q 'codex-41' \"$db_query_log\"")
val connected = checker.find("pass \"simpleos_rv64_db_server_connected\"")
expect(readiness).to_be_greater_than(-1)
expect(selected_value).to_be_greater_than(readiness)
expect(connected).to_be_greater_than(selected_value)
```

</details>

#### keeps the RV64 smoke script explicit about the deferred boundary

- expect qemu deferred script contract
   - Expected: script.index_of("scripts/os/simpleos-native-build.shs --target riscv64gc-unknown-none") ?? -1 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_qemu_deferred_script_contract("scripts/qemu/qemu_rv64_http_test.shs")
val script = rt_file_read_text("scripts/qemu/qemu_rv64_http_test.shs")

expect(script).to_contain("build/os/simpleos_riscv64.elf")
expect(script).to_contain("--allow-prebuilt-artifact")
expect(script).to_contain("current-source build stamp not found")
expect(script).to_contain("as current-source RV64 QEMU evidence")
expect(script).to_contain("Build it first through the SimpleOS runner with a target-capable compiler")
expect(script).to_contain("bin/simple os build --arch=riscv64")
expect(script).to_contain("^backend=(llvm|cranelift)$")
expect(script).to_contain("^target=riscv64-unknown-none$")
expect(script).to_contain("^entry=src/os/kernel/arch/riscv64/boot.spl$")
expect(script).to_contain("^simple_bin=.*(compiler_rust|simple_seed)")
expect(script).to_contain("Rust-seed provenance is not self-hosted RV64 evidence")
expect(script).to_contain("--expect-http-only")
expect(script).to_contain("EXPECT_HTTP_ONLY=true")
expect(script).to_contain("PMM OK")
expect(script).to_contain("HEAP OK")
expect(script).to_contain("Network packet TX ready")
expect(script).to_contain("Network packet RX unavailable")
expect(script).to_contain("RISC-V TLS not production-ready")
expect(script.index_of("scripts/os/simpleos-native-build.shs --target riscv64gc-unknown-none") ?? -1).to_equal(-1)
```

</details>

#### keeps the RV32 smoke script explicit about the deferred boundary

- expect qemu deferred script contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_qemu_deferred_script_contract("scripts/qemu/qemu_rv32_http_test.shs")
```

</details>

#### documents the real LLVM-backed RV32 build prerequisite

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = rt_file_read_text("scripts/qemu/qemu_rv32_http_test.shs")

expect(script).to_contain("Build it first with an LLVM-enabled compiler")
expect(script).to_contain("--backend llvm")
expect(script).to_contain("--target riscv32-unknown-none")
expect(script.index_of("riscv32gc-unknown-none") ?? -1).to_equal(-1)
```

</details>

#### maps current RV32 backend failures to actionable prerequisites

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = rt_file_read_text("src/os/_QemuRunner/runner_targets.spl")

expect(runner).to_contain("native backend 'llvm' is not available")
expect(runner).to_contain("Cranelift native builds do not support hosted riscv32 yet")
expect(runner).to_contain("LLVM backend unavailable: rebuild the selected Simple compiler")
```

</details>

#### runs the RV64 HTTP, NVFS storage, and database QEMU gate when explicitly enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = rt_file_read_text("scripts/qemu/qemu_rv64_http_test.shs")

expect(script).to_contain("--expect-http-only")
expect(script).to_contain("--with-storage")
expect(script).to_contain("--with-db")
expect(script).to_contain("WARNING: --allow-prebuilt-artifact gives smoke-only evidence")
expect(script).to_contain("Storage service ready")
expect(script).to_contain("NVFS root superblock ready")
expect(script).to_contain("SIMPLEOS_NVFS_ARENA_FILE")

if rv64_http_storage_live_enabled():
    val result = rt_process_run_timeout(
        "env",
        [
            "SERIAL_LOG=build/test-artifacts/simpleos-rv64-http-db-live/serial.log",
            "DB_QUERY_LOG=build/test-artifacts/simpleos-rv64-http-db-live/db_query.log",
            "sh", "scripts/qemu/qemu_rv64_http_test.shs",
            "--expect-http-only", "--with-storage", "--with-db",
        ],
        90000,
    )
    val output = result[0] + result[1]

    expect(result[2]).to_equal(0)
    expect(output).to_contain("HTTP-only PASSED")
    expect(output).to_contain("Storage service verified")
    expect(output).to_contain("NVFS root superblock verified")
    expect(output).to_contain("NVFS arena payload ready")
    expect(output).to_contain("DB CREATE/INSERT/SELECT... PASS (codex-41)")
    expect(output).to_contain("GET /health (HTTP)... PASS (200)")
    expect(output).to_contain("GET / (HTTP)... PASS (200)")
    expect(output).to_contain("SKIP (HTTP-only gate; RISC-V TLS not production-ready)")
    expect(output).to_contain("GET /health content-type... PASS (JSON)")
    expect(output).to_contain("GET / content-type... PASS (HTML)")

    val checker_result = rt_process_run_timeout(
        "sh",
        [
            "scripts/qemu/check_simpleos_rv64_db_server.shs",
            "--artifacts", "build/test-artifacts/simpleos-rv64-http-db-live",
        ],
        10000,
    )
    val checker_output = checker_result[0] + checker_result[1]
    expect(checker_result[2]).to_equal(0)
    expect(checker_output).to_contain("PASS simpleos_rv64_db_server_connected")
else:
    print "SKIP: set SIMPLEOS_RV64_HTTP_STORAGE_QEMU=1 to run live RV64 HTTP+NVFS+DB QEMU gate"
```

</details>

### SimpleOS QEMU network entrypoint gates

#### does not report os_network success for query/no-crash socket placeholders

- expect no fake network pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_no_fake_network_pass("test/03_system/os/os_network_spec.spl")
val source = rt_file_read_text("test/03_system/os/os_network_spec.spl")
expect(source).to_contain("_assert(net_ready, \"Network stack initialized\")")
expect(source).to_contain("_assert(bind_result >= 0")
expect(source).to_contain("_assert(conn_result >= 0")
```

</details>

#### does not report full-stack network success for no-crash socket placeholders

- expect no fake network pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/03_system/os/os_full_stack_spec.spl"
expect_no_fake_network_pass(path)
expect(rt_file_read_text(path)).to_contain("_assert(services_network_ready()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_riscv_network_gate_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS RISC-V network readiness gate
- SimpleOS RISC-V QEMU HTTP scripts
- SimpleOS QEMU network entrypoint gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
