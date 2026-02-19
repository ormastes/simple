# Embedded Test Runner Design

**Status:** Draft
**Date:** 2026-02-05
**Author:** Claude

---

## 1. Overview

Design for a modular embedded test runner system with:
- **Core**: Shared test runner logic (discovery, parsing, reporting)
- **Host**: Runs on development machine, orchestrates tests
- **Client**: Runs on target (QEMU/hardware), executes tests
- **Driver**: Automates loading, execution, and result collection

```
┌─────────────────────────────────────────────────────────────────┐
│                      Test Runner Driver                         │
│  (simple test --embedded --target=qemu-x86)                     │
└─────────────────────────────────────────────────────────────────┘
                              │
         ┌────────────────────┴────────────────────┐
         ▼                                         ▼
┌─────────────────────┐                 ┌─────────────────────┐
│  Embedded Host      │                 │  Embedded Client    │
│  (runs on PC)       │ ◄──── Serial ───► (runs on target)   │
│                     │      Protocol   │                     │
│  - Load binary      │                 │  - Execute tests    │
│  - Parse output     │                 │  - Send results     │
│  - Collect results  │                 │  - Exit with code   │
└─────────────────────┘                 └─────────────────────┘
         │                                         │
         ▼                                         ▼
┌─────────────────────┐                 ┌─────────────────────┐
│  Test Runner Core   │                 │  Test Runner Core   │
│  (shared logic)     │                 │  (minimal subset)   │
└─────────────────────┘                 └─────────────────────┘
```

---

## 2. Architecture

### 2.1 Component Hierarchy

```
src/app/test_runner/
├── core/                        # Shared core (both host and client)
│   ├── mod.spl                  # Module exports
│   ├── types.spl                # TestResult, TestCase, TestSuite types
│   ├── protocol.spl             # Binary protocol definitions
│   ├── format.spl               # Output formatting
│   └── constants.spl            # Shared constants
│
├── host/                        # Host-side runner
│   ├── mod.spl
│   ├── loader.spl               # Binary loader (QEMU, OpenOCD, etc.)
│   ├── transport.spl            # Serial/JTAG/TCP transport
│   ├── parser.spl               # Parse client output
│   ├── collector.spl            # Collect and aggregate results
│   └── reporter.spl             # Generate reports
│
├── client/                      # Target-side runner (minimal)
│   ├── mod.spl
│   ├── harness.spl              # Test execution harness
│   ├── output.spl               # Send results via semihosting
│   └── assert.spl               # Assertion macros
│
└── driver/                      # Main driver (CLI integration)
    ├── mod.spl
    ├── main.spl                 # Entry point
    ├── config.spl               # Configuration parsing
    └── targets/                 # Target-specific drivers
        ├── qemu.spl             # QEMU loader
        ├── openocd.spl          # OpenOCD/GDB loader
        ├── jlink.spl            # J-Link loader
        └── serial.spl           # Serial bootloader
```

### 2.2 Data Flow

```
1. Discovery Phase (Host)
   ┌─────────────────┐
   │ Find test files │ ──► *.spl files matching pattern
   │ Parse test info │ ──► Extract describe/it blocks
   │ Build test list │ ──► TestSuite with TestCases
   └─────────────────┘

2. Compilation Phase (Host)
   ┌─────────────────┐
   │ Compile tests   │ ──► simple build --target=baremetal-x86
   │ Link binary     │ ──► test_runner.elf
   │ Generate tables │ ──► String intern table (SMF section)
   └─────────────────┘

3. Loading Phase (Host → Target)
   ┌─────────────────┐
   │ Start QEMU      │ ──► qemu-system-i386 -kernel test.elf
   │ Open transport  │ ──► Serial stdio / TCP socket
   │ Wait for ready  │ ──► [CLIENT READY] message
   └─────────────────┘

4. Execution Phase (Client)
   ┌─────────────────┐
   │ Run tests       │ ──► Execute each TestCase
   │ Send results    │ ──► Binary protocol over serial
   │ Exit            │ ──► Debug exit with status
   └─────────────────┘

5. Collection Phase (Host)
   ┌─────────────────┐
   │ Parse output    │ ──► Decode binary protocol
   │ Reconstruct     │ ──► Use string table for messages
   │ Aggregate       │ ──► Build TestResults
   └─────────────────┘

6. Reporting Phase (Host)
   ┌─────────────────┐
   │ Format output   │ ──► Console, JSON, JUnit XML
   │ Update database │ ──► doc/test/test_db.sdn
   │ Exit with code  │ ──► 0 = pass, 1 = fail
   └─────────────────┘
```

---

## 3. Core Module Design

### 3.1 Types (`compiler_core/types.spl`)

```simple
# Test case status
val TEST_STATUS_PENDING: i32 = 0
val TEST_STATUS_RUNNING: i32 = 1
val TEST_STATUS_PASSED: i32 = 2
val TEST_STATUS_FAILED: i32 = 3
val TEST_STATUS_SKIPPED: i32 = 4
val TEST_STATUS_TIMEOUT: i32 = 5

# Test case
class TestCase:
    id: i32                    # Unique ID (handle for embedded)
    name: text                 # Test name
    suite: text                # Parent suite name
    status: i32                # TEST_STATUS_*
    duration_ms: i64           # Execution time
    message: text              # Failure message (if failed)
    file: text                 # Source file
    line: i32                  # Source line

impl TestCase:
    static fn create(id: i32, name: text, suite: text) -> TestCase:
        TestCase(
            id: id,
            name: name,
            suite: suite,
            status: TEST_STATUS_PENDING,
            duration_ms: 0,
            message: "",
            file: "",
            line: 0
        )

    fn is_passed() -> bool:
        self.status == TEST_STATUS_PASSED

    fn is_failed() -> bool:
        self.status == TEST_STATUS_FAILED

# Test suite (collection of test cases)
class TestSuite:
    name: text
    file: text
    test_count: i32
    passed_count: i32
    failed_count: i32
    skipped_count: i32
    duration_ms: i64

impl TestSuite:
    static fn create(name: text, file: text) -> TestSuite:
        TestSuite(
            name: name,
            file: file,
            test_count: 0,
            passed_count: 0,
            failed_count: 0,
            skipped_count: 0,
            duration_ms: 0
        )

# Aggregate results
class TestResults:
    total: i32
    passed: i32
    failed: i32
    skipped: i32
    timeout: i32
    duration_ms: i64

impl TestResults:
    static fn empty() -> TestResults:
        TestResults(
            total: 0,
            passed: 0,
            failed: 0,
            skipped: 0,
            timeout: 0,
            duration_ms: 0
        )

    fn success_rate() -> f64:
        if self.total == 0:
            100.0
        else:
            (self.passed as f64 / self.total as f64) * 100.0
```

### 3.2 Protocol (`core/protocol.spl`)

```simple
# Binary protocol for embedded test output
#
# Message format:
#   [u8]  Magic (0xAB)
#   [u8]  Version (0x01)
#   [u8]  Message type
#   [u16] Payload length (little-endian)
#   [...]  Payload (depends on type)

# Protocol constants
val PROTO_MAGIC: i32 = 0xAB
val PROTO_VERSION: i32 = 0x01

# Message types
val MSG_READY: i32 = 0x01           # Client ready
val MSG_SUITE_START: i32 = 0x10     # Suite started
val MSG_SUITE_END: i32 = 0x11       # Suite ended
val MSG_TEST_START: i32 = 0x20      # Test started
val MSG_TEST_PASS: i32 = 0x21       # Test passed
val MSG_TEST_FAIL: i32 = 0x22       # Test failed
val MSG_TEST_SKIP: i32 = 0x23       # Test skipped
val MSG_LOG: i32 = 0x30             # Log message
val MSG_ASSERT_FAIL: i32 = 0x40     # Assertion failed
val MSG_COMPLETE: i32 = 0xFF        # All tests complete

# Payload structures (conceptual - actual bytes)
#
# MSG_READY:
#   [u32] client_version
#   [u32] test_count
#
# MSG_SUITE_START:
#   [u32] suite_id (handle)
#
# MSG_TEST_START:
#   [u32] test_id (handle)
#
# MSG_TEST_PASS:
#   [u32] test_id
#   [u32] duration_ms
#
# MSG_TEST_FAIL:
#   [u32] test_id
#   [u32] duration_ms
#   [u32] message_handle (interned string)
#   [u32] file_handle
#   [u32] line_number
#
# MSG_COMPLETE:
#   [u32] total
#   [u32] passed
#   [u32] failed
#   [u32] skipped

class ProtocolMessage:
    msg_type: i32
    payload_len: i32

impl ProtocolMessage:
    # Encode message header to bytes
    fn encode_header() -> [i32]:
        [PROTO_MAGIC, PROTO_VERSION, self.msg_type,
         self.payload_len & 0xFF, (self.payload_len >> 8) & 0xFF]

# Encode 32-bit value as little-endian bytes
fn encode_u32(val: i32) -> [i32]:
    [val & 0xFF, (val >> 8) & 0xFF, (val >> 16) & 0xFF, (val >> 24) & 0xFF]

# Decode 32-bit value from little-endian bytes
fn decode_u32(b0: i32, b1: i32, b2: i32, b3: i32) -> i32:
    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
```

### 3.3 Output Formatting (`compiler_core/format.spl`)

```simple
# Format test results for display

# Format styles
val FORMAT_SIMPLE: i32 = 0      # One line per test
val FORMAT_VERBOSE: i32 = 1     # Full output with details
val FORMAT_DOC: i32 = 2         # RSpec-style nested
val FORMAT_JSON: i32 = 3        # JSON output
val FORMAT_JUNIT: i32 = 4       # JUnit XML

fn format_test_result(tc: TestCase, style: i32) -> text:
    if style == FORMAT_SIMPLE:
        format_simple(tc)
    elif style == FORMAT_VERBOSE:
        format_verbose(tc)
    else:
        format_simple(tc)

fn format_simple(tc: TestCase) -> text:
    val status_str = if tc.status == TEST_STATUS_PASSED: "[PASS]"
        elif tc.status == TEST_STATUS_FAILED: "[FAIL]"
        elif tc.status == TEST_STATUS_SKIPPED: "[SKIP]"
        else: "[????]"
    "{status_str} {tc.suite} :: {tc.name} ({tc.duration_ms}ms)"

fn format_verbose(tc: TestCase) -> text:
    val base = format_simple(tc)
    if tc.status == TEST_STATUS_FAILED and tc.message != "":
        "{base}\n       Error: {tc.message}\n       at {tc.file}:{tc.line}"
    else:
        base

fn format_summary(results: TestResults) -> text:
    val rate = results.success_rate()
    "Total: {results.total}, Passed: {results.passed}, Failed: {results.failed}, " +
    "Skipped: {results.skipped}, Duration: {results.duration_ms}ms ({rate:.1}%)"
```

---

## 4. Host Module Design

### 4.1 Loader (`host/loader.spl`)

```simple
# Binary loader interface
# Implementations for different targets

# Loader type
val LOADER_QEMU: i32 = 0
val LOADER_OPENOCD: i32 = 1
val LOADER_JLINK: i32 = 2
val LOADER_SERIAL: i32 = 3

class LoaderConfig:
    loader_type: i32
    binary_path: text
    target_arch: text          # "x86", "arm", "riscv32"
    timeout_ms: i64
    extra_args: text           # Additional arguments

impl LoaderConfig:
    static fn qemu(binary: text, arch: text) -> LoaderConfig:
        LoaderConfig(
            loader_type: LOADER_QEMU,
            binary_path: binary,
            target_arch: arch,
            timeout_ms: 30000,
            extra_args: ""
        )

# Loader result
class LoaderResult:
    success: bool
    process_id: i32
    transport_path: text       # e.g., "/tmp/qemu_serial.sock"
    error_message: text

# Abstract loader operations (implemented per target)
fn loader_start(config: LoaderConfig) -> LoaderResult:
    if config.loader_type == LOADER_QEMU:
        qemu_loader_start(config)
    else:
        LoaderResult(success: false, process_id: 0,
                     transport_path: "", error_message: "Unknown loader type")

fn loader_stop(pid: i32):
    # Kill process
    pass

fn loader_wait(pid: i32, timeout_ms: i64) -> i32:
    # Wait for process with timeout, return exit code
    0
```

### 4.2 QEMU Loader (`host/targets/qemu.spl`)

```simple
# QEMU-specific loader implementation

fn qemu_loader_start(config: LoaderConfig) -> LoaderResult:
    # Build QEMU command
    val qemu_cmd = get_qemu_command(config.target_arch)

    # QEMU arguments for embedded testing
    val args = [
        "-kernel", config.binary_path,
        "-serial", "stdio",
        "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
        "-display", "none",
        "-no-reboot"
    ]

    # Start QEMU process
    # (Uses FFI to spawn process)
    val result = spawn_process(qemu_cmd, args)

    LoaderResult(
        success: result.success,
        process_id: result.pid,
        transport_path: "stdio",
        error_message: result.error
    )

fn get_qemu_command(arch: text) -> text:
    if arch == "x86" or arch == "i686":
        "qemu-system-i386"
    elif arch == "x86_64":
        "qemu-system-x86_64"
    elif arch == "arm" or arch == "arm32":
        "qemu-system-arm"
    elif arch == "arm64" or arch == "aarch64":
        "qemu-system-aarch64"
    elif arch == "riscv32":
        "qemu-system-riscv32"
    elif arch == "riscv64":
        "qemu-system-riscv64"
    else:
        "qemu-system-i386"  # Default

# Map QEMU exit code to test result
fn qemu_exit_code_to_result(exit_code: i32) -> (bool, text):
    if exit_code == 1:
        (true, "Tests passed")
    elif exit_code == 3:
        (false, "Tests failed")
    elif exit_code == 124:
        (false, "Timeout")
    else:
        (false, "Unknown exit code: {exit_code}")
```

### 4.3 Transport (`host/transport.spl`)

```simple
# Transport layer for host-client communication

# Transport type
val TRANSPORT_STDIO: i32 = 0
val TRANSPORT_SERIAL: i32 = 1
val TRANSPORT_TCP: i32 = 2
val TRANSPORT_FILE: i32 = 3

class Transport:
    transport_type: i32
    path: text                 # Device path, file, or "stdio"
    baud_rate: i32             # For serial
    connected: bool

impl Transport:
    static fn stdio() -> Transport:
        Transport(
            transport_type: TRANSPORT_STDIO,
            path: "stdio",
            baud_rate: 0,
            connected: true
        )

    static fn serial(device: text, baud: i32) -> Transport:
        Transport(
            transport_type: TRANSPORT_SERIAL,
            path: device,
            baud_rate: baud,
            connected: false
        )

    # Read bytes from transport
    me read(max_bytes: i32) -> [i32]:
        # Implementation depends on transport type
        []

    # Write bytes to transport
    me write(data: [i32]) -> bool:
        # Implementation depends on transport type
        true

    # Read until delimiter or timeout
    me read_until(delimiter: i32, timeout_ms: i64) -> [i32]:
        []

    # Close transport
    me close():
        self.connected = false
```

### 4.4 Parser (`host/parser.spl`)

```simple
# Parse binary protocol from client

class ProtocolParser:
    buffer: [i32]
    string_table: StringInternTable
    current_suite: text
    results: TestResults

impl ProtocolParser:
    static fn create(string_table: StringInternTable) -> ProtocolParser:
        ProtocolParser(
            buffer: [],
            string_table: string_table,
            current_suite: "",
            results: TestResults.empty()
        )

    # Feed bytes into parser
    me feed(data: [i32]):
        for byte in data:
            self.buffer.push(byte)
        self.process_buffer()

    # Process buffered data
    me process_buffer():
        while self.buffer.len() >= 5:  # Minimum message size
            # Check magic
            if self.buffer[0] != PROTO_MAGIC:
                self.buffer.remove(0)
                continue

            # Check version
            if self.buffer[1] != PROTO_VERSION:
                self.buffer.remove(0)
                continue

            # Get message type and length
            val msg_type = self.buffer[2]
            val payload_len = self.buffer[3] | (self.buffer[4] << 8)

            # Check if we have full message
            if self.buffer.len() < 5 + payload_len:
                return  # Wait for more data

            # Extract payload
            val payload = self.buffer[5..5 + payload_len]

            # Remove processed bytes
            self.buffer = self.buffer[5 + payload_len..]

            # Handle message
            self.handle_message(msg_type, payload)

    # Handle parsed message
    me handle_message(msg_type: i32, payload: [i32]):
        if msg_type == MSG_READY:
            self.handle_ready(payload)
        elif msg_type == MSG_SUITE_START:
            self.handle_suite_start(payload)
        elif msg_type == MSG_TEST_PASS:
            self.handle_test_pass(payload)
        elif msg_type == MSG_TEST_FAIL:
            self.handle_test_fail(payload)
        elif msg_type == MSG_COMPLETE:
            self.handle_complete(payload)

    me handle_ready(payload: [i32]):
        val version = decode_u32(payload[0], payload[1], payload[2], payload[3])
        val test_count = decode_u32(payload[4], payload[5], payload[6], payload[7])
        print "[HOST] Client ready: version={version}, tests={test_count}"

    me handle_test_pass(payload: [i32]):
        val test_id = decode_u32(payload[0], payload[1], payload[2], payload[3])
        val duration = decode_u32(payload[4], payload[5], payload[6], payload[7])
        val name = self.string_table.get(test_id)
        print "[PASS] {name} ({duration}ms)"
        self.results.passed = self.results.passed + 1
        self.results.total = self.results.total + 1

    me handle_test_fail(payload: [i32]):
        val test_id = decode_u32(payload[0], payload[1], payload[2], payload[3])
        val duration = decode_u32(payload[4], payload[5], payload[6], payload[7])
        val msg_handle = decode_u32(payload[8], payload[9], payload[10], payload[11])
        val name = self.string_table.get(test_id)
        val message = self.string_table.get(msg_handle)
        print "[FAIL] {name} ({duration}ms)"
        print "       {message}"
        self.results.failed = self.results.failed + 1
        self.results.total = self.results.total + 1

    me handle_complete(payload: [i32]):
        val total = decode_u32(payload[0], payload[1], payload[2], payload[3])
        val passed = decode_u32(payload[4], payload[5], payload[6], payload[7])
        val failed = decode_u32(payload[8], payload[9], payload[10], payload[11])
        print "[HOST] Tests complete: {passed}/{total} passed, {failed} failed"
```

---

## 5. Client Module Design

### 5.1 Harness (`client/harness.spl`)

```simple
# Minimal test harness for embedded targets
# Designed for minimal code size

# Global state
var g_test_count: i32 = 0
var g_passed: i32 = 0
var g_failed: i32 = 0
var g_current_test: i32 = 0
var g_test_start_time: i64 = 0

# Initialize harness
fn test_harness_init(test_count: i32):
    g_test_count = test_count
    g_passed = 0
    g_failed = 0
    g_current_test = 0

    # Send ready message
    send_ready(test_count)

# Start a test
fn test_begin(test_id: i32):
    g_current_test = test_id
    g_test_start_time = get_time_ms()
    send_test_start(test_id)

# Mark test passed
fn test_pass():
    val duration = get_time_ms() - g_test_start_time
    g_passed = g_passed + 1
    send_test_pass(g_current_test, duration as i32)

# Mark test failed
fn test_fail(message_handle: i32, file_handle: i32, line: i32):
    val duration = get_time_ms() - g_test_start_time
    g_failed = g_failed + 1
    send_test_fail(g_current_test, duration as i32, message_handle, file_handle, line)

# Finish all tests
fn test_harness_complete():
    send_complete(g_test_count, g_passed, g_failed)

    # Exit with appropriate code
    val exit_code = if g_failed > 0: 1 else: 0
    embedded_exit(exit_code)

# Get time in milliseconds (platform-specific)
fn get_time_ms() -> i64:
    # Uses SYS_CLOCK semihosting or timer
    0

# Exit (platform-specific)
fn embedded_exit(code: i32):
    # Uses debug exit port on QEMU
    # Or SYS_EXIT semihosting
    pass
```

### 5.2 Output (`client/output.spl`)

```simple
# Send protocol messages via semihosting

# Port I/O for x86 QEMU
fn outb(port: i32, value: i32):
    # Assembly stub
    pass

val COM1_DATA: i32 = 0x3F8
val COM1_LSR: i32 = 0x3FD

fn serial_write_byte(b: i32):
    # Wait for transmit ready
    while (inb(COM1_LSR) & 0x20) == 0:
        pass
    outb(COM1_DATA, b)

fn send_message(msg_type: i32, payload: [i32]):
    # Send header
    serial_write_byte(PROTO_MAGIC)
    serial_write_byte(PROTO_VERSION)
    serial_write_byte(msg_type)
    serial_write_byte(payload.len() & 0xFF)
    serial_write_byte((payload.len() >> 8) & 0xFF)

    # Send payload
    for byte in payload:
        serial_write_byte(byte)

fn send_ready(test_count: i32):
    val version_bytes = encode_u32(1)  # Version 1
    val count_bytes = encode_u32(test_count)
    send_message(MSG_READY, version_bytes + count_bytes)

fn send_test_start(test_id: i32):
    send_message(MSG_TEST_START, encode_u32(test_id))

fn send_test_pass(test_id: i32, duration_ms: i32):
    val payload = encode_u32(test_id) + encode_u32(duration_ms)
    send_message(MSG_TEST_PASS, payload)

fn send_test_fail(test_id: i32, duration_ms: i32, msg: i32, file: i32, line: i32):
    val payload = encode_u32(test_id) + encode_u32(duration_ms) +
                  encode_u32(msg) + encode_u32(file) + encode_u32(line)
    send_message(MSG_TEST_FAIL, payload)

fn send_complete(total: i32, passed: i32, failed: i32):
    val payload = encode_u32(total) + encode_u32(passed) +
                  encode_u32(failed) + encode_u32(0)  # skipped
    send_message(MSG_COMPLETE, payload)
```

### 5.3 Assertions (`client/assert.spl`)

```simple
# Minimal assertion macros for embedded tests

# Assert condition is true
fn assert_true(condition: bool, msg_handle: i32, file_handle: i32, line: i32):
    if not condition:
        test_fail(msg_handle, file_handle, line)
        # In embedded: may halt or continue depending on config

# Assert equality
fn assert_eq_i32(actual: i32, expected: i32, msg_handle: i32, file_handle: i32, line: i32):
    if actual != expected:
        test_fail(msg_handle, file_handle, line)

fn assert_eq_i64(actual: i64, expected: i64, msg_handle: i32, file_handle: i32, line: i32):
    if actual != expected:
        test_fail(msg_handle, file_handle, line)

# Assert inequality
fn assert_ne_i32(actual: i32, expected: i32, msg_handle: i32, file_handle: i32, line: i32):
    if actual == expected:
        test_fail(msg_handle, file_handle, line)
```

---

## 6. Driver Module Design

### 6.1 Main Entry (`driver/main.spl`)

```simple
# Main embedded test runner driver

fn run_embedded_tests(config: EmbeddedTestConfig) -> i32:
    print "═══════════════════════════════════════════════════════════"
    print "  Embedded Test Runner"
    print "  Target: {config.target}"
    print "  Binary: {config.binary_path}"
    print "═══════════════════════════════════════════════════════════"
    print ""

    # Phase 1: Load string table from SMF
    print "[1/5] Loading string table..."
    val string_table = load_string_table(config.smf_path)
    if not string_table.has_entries():
        print "Warning: No string table found, using handles as names"

    # Phase 2: Start loader (QEMU, OpenOCD, etc.)
    print "[2/5] Starting target ({config.loader_type})..."
    val loader_config = LoaderConfig(
        loader_type: config.loader_type,
        binary_path: config.binary_path,
        target_arch: config.target_arch,
        timeout_ms: config.timeout_ms,
        extra_args: config.extra_args
    )
    val loader_result = loader_start(loader_config)
    if not loader_result.success:
        print "ERROR: Failed to start target: {loader_result.error_message}"
        return 1

    # Phase 3: Open transport
    print "[3/5] Connecting to target..."
    var transport = Transport.stdio()

    # Phase 4: Run tests and collect results
    print "[4/5] Running tests..."
    var parser = ProtocolParser.create(string_table)

    val start_time = get_time_ms()
    var running = true

    while running:
        # Read from transport
        val data = transport.read(256)
        if data.len() > 0:
            parser.feed(data)

        # Check for completion
        if parser.results.total >= g_expected_tests:
            running = false

        # Check timeout
        if get_time_ms() - start_time > config.timeout_ms:
            print "ERROR: Test timeout after {config.timeout_ms}ms"
            running = false

    # Phase 5: Wait for target exit and report
    print "[5/5] Collecting results..."
    val exit_code = loader_wait(loader_result.process_id, 5000)
    val (success, message) = qemu_exit_code_to_result(exit_code)

    # Print summary
    print ""
    print "═══════════════════════════════════════════════════════════"
    print format_summary(parser.results)
    print "═══════════════════════════════════════════════════════════"

    if parser.results.failed > 0:
        1
    else:
        0

# Configuration
class EmbeddedTestConfig:
    target: text               # "qemu-x86", "qemu-arm", "openocd"
    binary_path: text          # Path to test binary
    smf_path: text             # Path to SMF file with string table
    target_arch: text          # "x86", "arm", "riscv32"
    loader_type: i32           # LOADER_QEMU, etc.
    timeout_ms: i64
    extra_args: text
    output_format: i32         # FORMAT_SIMPLE, etc.
```

---

## 7. Integration with Existing Test Runner

### 7.1 Refactored Test Runner Structure

```
src/app/test_runner_new/
├── main.spl                   # Entry point (unchanged)
├── test_runner_files.spl      # → Uses compiler_core/discovery.spl
├── test_runner_execute.spl    # → Uses compiler_core/executor.spl
├── test_runner_types.spl      # → Imports from compiler_core/types.spl
├── test_runner_output.spl     # → Uses compiler_core/format.spl
└── embedded/                  # NEW: Embedded test support
    └── runner.spl             # Calls driver/main.spl
```

### 7.2 CLI Integration

```bash
# Existing commands (unchanged)
simple test                           # All tests (Rust + Simple)
simple test --no-rust-tests           # Simple tests only
simple test path/to/spec.spl          # Single file

# New embedded commands
simple test --embedded                # All embedded tests
simple test --embedded --target=qemu-x86
simple test --embedded --target=qemu-arm
simple test --embedded --target=openocd --device=/dev/ttyUSB0
simple test --embedded --binary=test.elf
simple test --embedded --timeout=60000
```

---

## 8. Implementation Plan

### Phase 1: Core Module (16h)

| Task | Hours | Description |
|------|-------|-------------|
| types.spl | 4 | TestCase, TestSuite, TestResults |
| protocol.spl | 4 | Binary protocol encoding/decoding |
| format.spl | 4 | Output formatting |
| constants.spl | 2 | Shared constants |
| Unit tests | 2 | Core module tests |

### Phase 2: Client Module (24h)

| Task | Hours | Description |
|------|-------|-------------|
| harness.spl | 8 | Test execution harness |
| output.spl | 8 | Protocol output via serial |
| assert.spl | 4 | Assertion functions |
| x86 backend | 4 | x86-specific output (QEMU) |

### Phase 3: Host Module (32h)

| Task | Hours | Description |
|------|-------|-------------|
| loader.spl | 4 | Loader interface |
| qemu.spl | 8 | QEMU loader implementation |
| transport.spl | 8 | Serial/stdio transport |
| parser.spl | 8 | Protocol parser |
| collector.spl | 4 | Result aggregation |

### Phase 4: Driver Module (16h)

| Task | Hours | Description |
|------|-------|-------------|
| main.spl | 8 | Main driver logic |
| config.spl | 4 | Configuration parsing |
| CLI integration | 4 | Add --embedded flag |

### Phase 5: Integration & Testing (16h)

| Task | Hours | Description |
|------|-------|-------------|
| Refactor existing runner | 8 | Use shared core modules |
| End-to-end tests | 4 | Full pipeline tests |
| Documentation | 4 | Usage guide |

**Total: 104 hours (13 days)**

---

## 9. File Structure Summary

```
src/app/test_runner/
├── core/
│   ├── mod.spl
│   ├── types.spl           # 150 lines
│   ├── protocol.spl        # 200 lines
│   ├── format.spl          # 100 lines
│   └── constants.spl       # 50 lines
├── host/
│   ├── mod.spl
│   ├── loader.spl          # 100 lines
│   ├── transport.spl       # 150 lines
│   ├── parser.spl          # 200 lines
│   ├── collector.spl       # 100 lines
│   └── targets/
│       ├── qemu.spl        # 150 lines
│       ├── openocd.spl     # 150 lines (future)
│       └── jlink.spl       # 150 lines (future)
├── client/
│   ├── mod.spl
│   ├── harness.spl         # 100 lines
│   ├── output.spl          # 150 lines
│   └── assert.spl          # 80 lines
└── driver/
    ├── mod.spl
    ├── main.spl            # 200 lines
    └── config.spl          # 100 lines

Total: ~1,930 lines
```

---

## 10. Testing Strategy

### Unit Tests

```simple
# test/app/test_runner/core_spec.spl
describe "TestCase":
    it "creates with default values":
        val tc = TestCase.create(1, "test", "suite")
        expect(tc.status).to(eq(TEST_STATUS_PENDING))

describe "Protocol":
    it "encodes u32 correctly":
        val bytes = encode_u32(0x12345678)
        expect(bytes).to(eq([0x78, 0x56, 0x34, 0x12]))
```

### Integration Tests

```bash
# Build test binary
simple build --target=baremetal-x86 test/embedded/basic_test.spl

# Run via embedded runner
simple test --embedded --target=qemu-x86 --binary=test.elf
```

### QEMU Hardware Tests

Use existing test binaries:
- `src/baremetal/test/qemu_semihost_test.elf`
- `src/baremetal/test/qemu_protocol_test.elf`

---

## 11. Future Extensions

### Phase 6: Additional Targets (Future)

- OpenOCD support for real hardware
- J-Link support
- Serial bootloader support
- Multi-device parallel testing

### Phase 7: Advanced Features (Future)

- Code coverage for embedded
- Performance profiling
- Memory leak detection
- Flash programming

---

## 12. References

- Existing test runner: `src/app/test_runner_new/`
- Semihosting API: `src/baremetal/system_api.spl`
- QEMU runner: `src/baremetal/qemu_runner.sh`
- String interning: `src/baremetal/string_intern.spl`
- Database layer: `src/lib/database/`
