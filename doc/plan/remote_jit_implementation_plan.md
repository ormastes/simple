# Remote JIT Execution Implementation Plan

**Date:** 2026-02-05
**Status:** Planning Complete
**Author:** Claude
**Priority:** P0 - RISC-V32 + QEMU + GDB + 1 HW Breakpoint

---

## 1. Executive Summary

This plan implements remote JIT execution for the Simple compiler, enabling code compilation on a host machine and execution on remote/embedded targets via debug probes (GDB/TRACE32).

**Key Innovation:** Single hardware breakpoint multiplexing - supports unlimited software breakpoints using only 1 HW breakpoint.

### 1.1 Implementation Scope

| Feature | Status | Priority |
|---------|--------|----------|
| RISC-V32 Target | **Implement** | P0 |
| GDB RSP Protocol | **Implement** | P0 |
| HW Breakpoint Sharing | **Implement** | P0 |
| QEMU Integration | **Implement** | P0 |
| TRACE32 Protocol | **Implement** | P1 |
| ARM32 Target | Design Only | P2 |
| ARM32 + TRACE32 | Design Only | P2 |

---

## 2. Phase 0: Foundation (Week 1)

### 2.1 Project Structure Setup

**Task 0.1:** Create module structure
```bash
mkdir -p src/remote/{target,debugger,breakpoint,codegen}
mkdir -p test/remote
```

**Files to create:**
```
src/remote/
├── mod.spl                 # Module exports
├── error.spl               # Error types
├── types.spl               # Common types
├── target/
│   ├── mod.spl             # Target trait
│   └── riscv32.spl         # RISC-V32 target
├── debugger/
│   ├── mod.spl             # Debugger trait
│   └── gdb.spl             # GDB implementation
├── breakpoint/
│   ├── mod.spl             # BP manager
│   └── predictor.spl       # Hit predictor
└── manager.spl             # Execution manager
```

**Deliverable:** Module skeleton with trait definitions

### 2.2 Error Types

**File:** `src/remote/error.spl`

```simple
enum RemoteError:
    # Connection errors
    ConnectionFailed(text)
    ConnectionTimeout
    ConnectionClosed

    # Protocol errors
    ProtocolError(text)
    ChecksumMismatch
    UnexpectedResponse(text)

    # Target errors
    TargetNotHalted
    TargetException(u32)
    InvalidAddress(u64)
    InvalidRegister(usize)

    # Breakpoint errors
    BreakpointFull
    BreakpointNotFound(u32)

    # Execution errors
    ExecutionTimeout
    CodeUploadFailed
    MemoryAllocationFailed

impl RemoteError:
    fn message() -> text:
        match self:
            ConnectionFailed(msg): "Connection failed: {msg}"
            ConnectionTimeout: "Connection timeout"
            # ... etc
```

### 2.3 Common Types

**File:** `src/remote/types.spl`

```simple
enum Architecture:
    Arm32
    RiscV32
    X86_64

enum Endianness:
    Little
    Big

enum BreakpointType:
    Execute
    Read
    Write
    Access

enum HaltReason:
    Breakpoint(addr: u64)
    Watchpoint(addr: u64)
    SingleStep
    Exception(code: u32)
    UserHalt

struct MemoryRegion:
    start: u64
    size: u64
    name: text
    executable: bool
    writable: bool

struct DebugConfig:
    host: text
    port: u16
    target: Architecture
    timeout_ms: u32
```

**Deliverable:** Complete type definitions

---

## 3. Phase 1: RISC-V32 Target (Week 1-2)

### 3.1 Target Trait Definition

**File:** `src/remote/target/mod.spl`

```simple
trait Target:
    # Identity
    fn name() -> text
    fn arch() -> Architecture
    fn endianness() -> Endianness

    # Registers
    fn register_count() -> usize
    fn register_name(index: usize) -> text
    fn register_size() -> usize  # bytes
    fn pc_index() -> usize
    fn sp_index() -> usize
    fn ra_index() -> usize

    # Calling convention
    fn arg_registers() -> [usize]
    fn return_register() -> usize
    fn callee_saved() -> [usize]

    # Debug hardware
    fn hw_bp_count() -> usize
    fn supports_single_step() -> bool

    # Instructions
    fn breakpoint_instruction() -> [u8]
    fn nop_instruction() -> [u8]
    fn instruction_alignment() -> usize
```

### 3.2 RISC-V32 Implementation

**File:** `src/remote/target/riscv32.spl`

```simple
class RiscV32Target implements Target:
    fn name() -> text:
        "RISC-V32 (RV32IMAC)"

    fn arch() -> Architecture:
        Architecture.RiscV32

    fn endianness() -> Endianness:
        Endianness.Little

    fn register_count() -> usize:
        33  # x0-x31 + PC

    fn register_name(index: usize) -> text:
        val NAMES = [
            "zero", "ra", "sp", "gp", "tp",
            "t0", "t1", "t2", "s0", "s1",
            "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
            "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
            "t3", "t4", "t5", "t6", "pc"
        ]
        if index < NAMES.len():
            NAMES[index]
        else:
            "x{index}"

    fn register_size() -> usize:
        4  # 32-bit

    fn pc_index() -> usize:
        32

    fn sp_index() -> usize:
        2  # x2

    fn ra_index() -> usize:
        1  # x1

    fn arg_registers() -> [usize]:
        [10, 11, 12, 13, 14, 15, 16, 17]  # a0-a7

    fn return_register() -> usize:
        10  # a0

    fn callee_saved() -> [usize]:
        [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]  # s0-s11

    fn hw_bp_count() -> usize:
        4  # QEMU default

    fn supports_single_step() -> bool:
        true

    fn breakpoint_instruction() -> [u8]:
        # EBREAK = 0x00100073 (little-endian)
        [0x73, 0x00, 0x10, 0x00]

    fn nop_instruction() -> [u8]:
        # ADDI x0, x0, 0 = 0x00000013
        [0x13, 0x00, 0x00, 0x00]

    fn instruction_alignment() -> usize:
        2  # Compressed extension allows 2-byte
```

### 3.3 Tests

**File:** `test/remote/target_spec.spl`

```simple
describe "RiscV32Target":
    val target = RiscV32Target()

    it "reports correct architecture":
        assert target.arch() == Architecture.RiscV32

    it "has 33 registers":
        assert target.register_count() == 33

    it "names registers correctly":
        assert target.register_name(0) == "zero"
        assert target.register_name(1) == "ra"
        assert target.register_name(2) == "sp"
        assert target.register_name(10) == "a0"
        assert target.register_name(32) == "pc"

    it "identifies special registers":
        assert target.pc_index() == 32
        assert target.sp_index() == 2
        assert target.ra_index() == 1

    it "provides EBREAK instruction":
        val ebreak = target.breakpoint_instruction()
        assert ebreak == [0x73, 0x00, 0x10, 0x00]
```

**Deliverable:** Complete RISC-V32 target with tests

---

## 4. Phase 2: GDB RSP Protocol (Week 2-3)

### 4.1 TCP Socket SFFI

**File:** `src/remote/socket.spl`

```simple
# SFFI for TCP sockets
extern fn rt_tcp_connect(host: text, port: u16) -> i64
extern fn rt_tcp_close(fd: i64)
extern fn rt_tcp_read(fd: i64, buf: ptr<u8>, len: usize) -> i64
extern fn rt_tcp_write(fd: i64, buf: ptr<u8>, len: usize) -> i64
extern fn rt_tcp_set_timeout(fd: i64, ms: u32)

class TcpSocket:
    fd: i64

    static fn connect(host: text, port: u16) -> Result<TcpSocket, RemoteError>:
        val fd = rt_tcp_connect(host, port)
        if fd < 0:
            return Err(RemoteError.ConnectionFailed(host))
        Ok(TcpSocket(fd: fd))

    fn close():
        rt_tcp_close(self.fd)

    fn read(buf: [u8]) -> Result<usize, RemoteError>:
        val n = rt_tcp_read(self.fd, buf.as_ptr(), buf.len())
        if n < 0:
            return Err(RemoteError.ConnectionClosed)
        Ok(n as usize)

    fn write(data: [u8]) -> Result<usize, RemoteError>:
        val n = rt_tcp_write(self.fd, data.as_ptr(), data.len())
        if n < 0:
            return Err(RemoteError.ConnectionClosed)
        Ok(n as usize)

    fn set_timeout(ms: u32):
        rt_tcp_set_timeout(self.fd, ms)
```

### 4.2 GDB RSP Packet Layer

**File:** `src/remote/debugger/gdb_packet.spl`

```simple
class GdbPacketLayer:
    socket: TcpSocket
    ack_mode: bool
    buffer: [u8]

    static fn new(socket: TcpSocket) -> GdbPacketLayer:
        GdbPacketLayer(
            socket: socket,
            ack_mode: true,
            buffer: []
        )

    fn send(data: text) -> Result<(), RemoteError>:
        # Format: $<data>#<checksum>
        val checksum = self.compute_checksum(data)
        val packet = "${data}#{checksum:02x}"

        self.socket.write(packet.as_bytes())?

        if self.ack_mode:
            val ack = self.read_byte()?
            if ack != '+' as u8:
                return Err(RemoteError.ProtocolError("NACK"))

        Ok(())

    fn receive() -> Result<text, RemoteError>:
        # Wait for '$'
        loop:
            val byte = self.read_byte()?
            if byte == '$' as u8:
                break

        # Read until '#'
        var data: [u8] = []
        loop:
            val byte = self.read_byte()?
            if byte == '#' as u8:
                break
            data.push(byte)

        # Read checksum (2 hex digits)
        val cs1 = self.read_byte()?
        val cs2 = self.read_byte()?

        # Verify checksum
        val received_cs = self.parse_hex_byte(cs1, cs2)?
        val computed_cs = self.compute_checksum_bytes(data)

        if received_cs != computed_cs:
            if self.ack_mode:
                self.socket.write(['-' as u8])?
            return Err(RemoteError.ChecksumMismatch)

        # Send ACK
        if self.ack_mode:
            self.socket.write(['+' as u8])?

        Ok(String.from_utf8(data))

    fn disable_ack():
        self.ack_mode = false

    fn compute_checksum(data: text) -> u8:
        self.compute_checksum_bytes(data.as_bytes())

    fn compute_checksum_bytes(data: [u8]) -> u8:
        var sum: u32 = 0
        for byte in data:
            sum = (sum + byte as u32) % 256
        sum as u8
```

### 4.3 GDB Debugger Implementation

**File:** `src/remote/debugger/gdb.spl`

```simple
class GdbDebugger implements Debugger:
    packets: GdbPacketLayer
    target: Architecture
    reg_size: usize

    static fn connect(config: DebugConfig) -> Result<GdbDebugger, RemoteError>:
        # Connect TCP
        val socket = TcpSocket.connect(config.host, config.port)?
        socket.set_timeout(config.timeout_ms)

        val packets = GdbPacketLayer.new(socket)

        var debugger = GdbDebugger(
            packets: packets,
            target: config.target,
            reg_size: 4  # 32-bit default
        )

        # Handshake
        debugger.handshake()?

        Ok(debugger)

    fn handshake() -> Result<(), RemoteError>:
        # Query supported features
        self.packets.send("qSupported:hwbreak+;swbreak+")?
        val features = self.packets.receive()?

        # Try to disable ACK mode (faster)
        if features.contains("QStartNoAckMode+"):
            self.packets.send("QStartNoAckMode")?
            val response = self.packets.receive()?
            if response == "OK":
                self.packets.disable_ack()

        Ok(())

    fn disconnect():
        self.packets.send("D")  # Detach (ignore errors)
        self.packets.socket.close()

    # === Memory Operations ===

    fn read_memory(addr: u64, size: usize) -> Result<[u8], RemoteError>:
        val cmd = "m{:x},{:x}".format(addr, size)
        self.packets.send(cmd)?
        val response = self.packets.receive()?

        if response.starts_with("E"):
            return Err(RemoteError.InvalidAddress(addr))

        self.decode_hex_bytes(response)

    fn write_memory(addr: u64, data: [u8]) -> Result<(), RemoteError>:
        val hex = self.encode_hex_bytes(data)
        val cmd = "M{:x},{:x}:{}".format(addr, data.len(), hex)
        self.packets.send(cmd)?
        val response = self.packets.receive()?

        if response != "OK":
            return Err(RemoteError.InvalidAddress(addr))

        Ok(())

    # === Register Operations ===

    fn read_register(index: usize) -> Result<u64, RemoteError>:
        val cmd = "p{:x}".format(index)
        self.packets.send(cmd)?
        val response = self.packets.receive()?

        if response.starts_with("E"):
            return Err(RemoteError.InvalidRegister(index))

        self.decode_hex_u64_le(response)

    fn write_register(index: usize, value: u64) -> Result<(), RemoteError>:
        val hex = self.encode_hex_u64_le(value, self.reg_size)
        val cmd = "P{:x}={}".format(index, hex)
        self.packets.send(cmd)?
        val response = self.packets.receive()?

        if response != "OK":
            return Err(RemoteError.InvalidRegister(index))

        Ok(())

    # === Execution Control ===

    fn halt() -> Result<(), RemoteError>:
        # Send Ctrl-C (0x03)
        self.packets.socket.write([0x03])?
        self.wait_halt(1000)

    fn resume() -> Result<(), RemoteError>:
        self.packets.send("c")?
        Ok(())

    fn single_step() -> Result<(), RemoteError>:
        self.packets.send("s")?
        self.wait_halt(1000)

    fn wait_halt(timeout_ms: u32) -> Result<HaltReason, RemoteError>:
        self.packets.socket.set_timeout(timeout_ms)
        val response = self.packets.receive()?

        self.parse_stop_reply(response)

    fn parse_stop_reply(response: text) -> Result<HaltReason, RemoteError>:
        if response.starts_with("S"):
            # S05 = SIGTRAP (breakpoint)
            val signal = u8.from_hex(response[1:3])?
            match signal:
                5: Ok(HaltReason.Breakpoint(0))
                11: Ok(HaltReason.Exception(11))  # SIGSEGV
                _: Ok(HaltReason.Exception(signal as u32))

        elif response.starts_with("T"):
            # T05thread:1; (extended format)
            Ok(HaltReason.Breakpoint(0))

        else:
            Err(RemoteError.UnexpectedResponse(response))

    # === Breakpoints ===

    fn set_hw_breakpoint(addr: u64, bp_type: BreakpointType)
        -> Result<(), RemoteError>:
        val type_code = match bp_type:
            Execute: 1
            Write: 2
            Read: 3
            Access: 4

        val cmd = "Z{},{:x},4".format(type_code, addr)
        self.packets.send(cmd)?
        val response = self.packets.receive()?

        match response:
            "OK": Ok(())
            "": Err(RemoteError.NotSupported("Hardware breakpoints"))
            _: Err(RemoteError.BreakpointFull)

    fn clear_hw_breakpoint(addr: u64, bp_type: BreakpointType)
        -> Result<(), RemoteError>:
        val type_code = match bp_type:
            Execute: 1
            Write: 2
            Read: 3
            Access: 4

        val cmd = "z{},{:x},4".format(type_code, addr)
        self.packets.send(cmd)?
        val response = self.packets.receive()?

        if response != "OK":
            return Err(RemoteError.ProtocolError("Clear BP failed"))

        Ok(())

    # === Hex Encoding/Decoding ===

    fn encode_hex_bytes(data: [u8]) -> text:
        var result = ""
        for byte in data:
            result = result + "{:02x}".format(byte)
        result

    fn decode_hex_bytes(hex: text) -> Result<[u8], RemoteError>:
        if hex.len() % 2 != 0:
            return Err(RemoteError.ProtocolError("Invalid hex"))

        var result: [u8] = []
        var i = 0
        while i < hex.len():
            val byte = u8.from_hex(hex[i:i+2])?
            result.push(byte)
            i += 2

        Ok(result)

    fn encode_hex_u64_le(value: u64, size: usize) -> text:
        var result = ""
        for i in 0..size:
            val byte = ((value >> (i * 8)) & 0xFF) as u8
            result = result + "{:02x}".format(byte)
        result

    fn decode_hex_u64_le(hex: text) -> Result<u64, RemoteError>:
        val bytes = self.decode_hex_bytes(hex)?
        var value: u64 = 0
        for i in 0..bytes.len():
            value = value | ((bytes[i] as u64) << (i * 8))
        Ok(value)
```

### 4.4 Tests

**File:** `test/remote/gdb_spec.spl`

```simple
describe "GdbPacketLayer":
    it "computes checksum correctly":
        val layer = GdbPacketLayer.new(mock_socket())
        assert layer.compute_checksum("qSupported") == 0x37

    it "encodes packets correctly":
        # $qSupported#37

describe "GdbDebugger":
    # These tests require QEMU running
    # Start with: qemu-system-riscv32 -machine virt -s -S

    slow_it "connects to QEMU":
        val debugger = GdbDebugger.connect(DebugConfig(
            host: "localhost",
            port: 1234,
            target: Architecture.RiscV32,
            timeout_ms: 5000
        ))?

        assert debugger.is_connected()
        debugger.disconnect()

    slow_it "reads registers":
        val debugger = connect_qemu()?
        val pc = debugger.read_register(32)?  # PC
        print "PC = 0x{pc:08X}"
        debugger.disconnect()

    slow_it "writes memory":
        val debugger = connect_qemu()?

        val data = [0x13, 0x00, 0x00, 0x00]  # NOP
        debugger.write_memory(0x80000000, data)?

        val read_back = debugger.read_memory(0x80000000, 4)?
        assert read_back == data

        debugger.disconnect()

    slow_it "sets hardware breakpoint":
        val debugger = connect_qemu()?

        debugger.set_hw_breakpoint(0x80000000, BreakpointType.Execute)?
        debugger.resume()?
        val halt = debugger.wait_halt(1000)?

        match halt:
            HaltReason.Breakpoint(_): pass
            _: fail("Expected breakpoint")

        debugger.disconnect()
```

**Deliverable:** Complete GDB RSP implementation with tests

---

## 5. Phase 3: HW Breakpoint Sharing (Week 3-4)

### 5.1 Breakpoint Manager

**File:** `src/remote/breakpoint/mod.spl`

```simple
struct SoftwareBreakpoint:
    id: u32
    addr: u64
    enabled: bool
    hit_count: u32

class BreakpointManager:
    debugger: Box<dyn Debugger>
    sw_bps: [SoftwareBreakpoint]
    current_hw_addr: u64?
    next_id: u32
    predictor: HitPredictor

    static fn new(debugger: Box<dyn Debugger>) -> BreakpointManager:
        BreakpointManager(
            debugger: debugger,
            sw_bps: [],
            current_hw_addr: nil,
            next_id: 1,
            predictor: HitPredictor.new()
        )

    # === Breakpoint CRUD ===

    me add(addr: u64) -> u32:
        val id = self.next_id
        self.next_id += 1

        self.sw_bps.push(SoftwareBreakpoint(
            id: id,
            addr: addr,
            enabled: true,
            hit_count: 0
        ))

        self.sync_hw_bp()
        id

    me remove(id: u32):
        self.sw_bps = self.sw_bps.filter(\bp: bp.id != id)
        self.sync_hw_bp()

    me enable(id: u32):
        for bp in self.sw_bps:
            if bp.id == id:
                bp.enabled = true
        self.sync_hw_bp()

    me disable(id: u32):
        for bp in self.sw_bps:
            if bp.id == id:
                bp.enabled = false
        self.sync_hw_bp()

    # === HW Breakpoint Synchronization ===

    me sync_hw_bp():
        val enabled = self.sw_bps.filter(\bp: bp.enabled)

        if enabled.is_empty():
            self.clear_hw_bp()
            return

        # Use predictor to select best BP
        val next_addr = self.predictor.predict(
            enabled.map(\bp: bp.addr)
        )

        if Some(next_addr) != self.current_hw_addr:
            self.set_hw_bp(next_addr)

    me set_hw_bp(addr: u64):
        # Clear existing
        if self.current_hw_addr.?:
            self.debugger.clear_hw_breakpoint(
                self.current_hw_addr.unwrap(),
                BreakpointType.Execute
            )

        # Set new
        self.debugger.set_hw_breakpoint(addr, BreakpointType.Execute)
        self.current_hw_addr = Some(addr)

    me clear_hw_bp():
        if self.current_hw_addr.?:
            self.debugger.clear_hw_breakpoint(
                self.current_hw_addr.unwrap(),
                BreakpointType.Execute
            )
            self.current_hw_addr = nil

    # === Execution with BP Rotation ===

    fn run_until_bp() -> Result<BreakpointHit?, RemoteError>:
        loop:
            self.sync_hw_bp()
            self.debugger.resume()?

            val halt = self.debugger.wait_halt(30000)?

            match halt:
                HaltReason.Breakpoint(addr):
                    # Check if real BP or rotation
                    val hit = self.check_hit(addr)
                    if hit.?:
                        return Ok(hit)

                    # Not real, rotate
                    self.rotate_hw_bp()

                HaltReason.Exception(code):
                    return Err(RemoteError.TargetException(code))

                _:
                    return Ok(nil)

    fn check_hit(addr: u64) -> BreakpointHit?:
        val pc = self.debugger.read_register(32)?  # PC

        for bp in self.sw_bps:
            if bp.addr == pc and bp.enabled:
                bp.hit_count += 1
                self.predictor.record(pc)

                return Some(BreakpointHit(
                    id: bp.id,
                    addr: pc,
                    count: bp.hit_count
                ))

        nil

    me rotate_hw_bp():
        val enabled = self.sw_bps.filter(\bp: bp.enabled)

        if enabled.len() <= 1:
            return

        # Find current and move to next
        var idx = 0
        for i in 0..enabled.len():
            if Some(enabled[i].addr) == self.current_hw_addr:
                idx = i
                break

        idx = (idx + 1) % enabled.len()
        self.set_hw_bp(enabled[idx].addr)

struct BreakpointHit:
    id: u32
    addr: u64
    count: u32
```

### 5.2 Hit Predictor

**File:** `src/remote/breakpoint/predictor.spl`

```simple
class HitPredictor:
    history: [u64]
    counts: Dict<u64, u32>
    max_history: usize

    static fn new() -> HitPredictor:
        HitPredictor(
            history: [],
            counts: {},
            max_history: 100
        )

    me record(addr: u64):
        # Update history
        self.history.push(addr)
        if self.history.len() > self.max_history:
            self.history.remove(0)

        # Update count
        val count = self.counts.get(addr) ?? 0
        self.counts[addr] = count + 1

    fn predict(candidates: [u64]) -> u64:
        if candidates.len() == 1:
            return candidates[0]

        # Strategy: Most frequently hit
        var best = candidates[0]
        var best_count: u32 = 0

        for addr in candidates:
            val count = self.counts.get(addr) ?? 0
            if count > best_count:
                best_count = count
                best = addr

        # Fallback: Lowest address (sequential code)
        if best_count == 0:
            best = candidates.min()

        best
```

### 5.3 Tests

**File:** `test/remote/breakpoint_spec.spl`

```simple
describe "BreakpointManager":
    it "adds breakpoints":
        val mgr = BreakpointManager.new(mock_debugger())

        val id1 = mgr.add(0x80000100)
        val id2 = mgr.add(0x80000200)

        assert id1 == 1
        assert id2 == 2
        assert mgr.sw_bps.len() == 2

    it "removes breakpoints":
        val mgr = BreakpointManager.new(mock_debugger())

        val id = mgr.add(0x80000100)
        mgr.remove(id)

        assert mgr.sw_bps.len() == 0

    it "rotates through breakpoints":
        val mock = MockDebugger()
        val mgr = BreakpointManager.new(Box(mock))

        mgr.add(0x80000100)
        mgr.add(0x80000200)
        mgr.add(0x80000300)

        # First sync should set BP at first address
        assert mgr.current_hw_addr == Some(0x80000100)

        # Rotate should move to next
        mgr.rotate_hw_bp()
        assert mgr.current_hw_addr == Some(0x80000200)

        mgr.rotate_hw_bp()
        assert mgr.current_hw_addr == Some(0x80000300)

        mgr.rotate_hw_bp()
        assert mgr.current_hw_addr == Some(0x80000100)  # Wrap

describe "HitPredictor":
    it "predicts most frequent":
        val pred = HitPredictor.new()

        pred.record(0x100)
        pred.record(0x100)
        pred.record(0x200)

        assert pred.predict([0x100, 0x200, 0x300]) == 0x100

    it "falls back to lowest on tie":
        val pred = HitPredictor.new()

        assert pred.predict([0x300, 0x100, 0x200]) == 0x100
```

**Deliverable:** Complete breakpoint manager with sharing algorithm

---

## 6. Phase 4: QEMU Integration (Week 4)

### 6.1 QEMU Setup Script

**File:** `script/qemu-riscv32.sh`

```bash
#!/bin/bash
# Start QEMU RISC-V32 with GDB server

QEMU=qemu-system-riscv32
MACHINE=virt
MEMORY=128M
GDB_PORT=1234

# Check if QEMU installed
if ! command -v $QEMU &> /dev/null; then
    echo "Error: $QEMU not found"
    echo "Install with: apt-get install qemu-system-riscv32"
    exit 1
fi

# Parse arguments
KERNEL=""
WAIT_GDB=true

while [[ $# -gt 0 ]]; do
    case $1 in
        -k|--kernel)
            KERNEL="$2"
            shift 2
            ;;
        -p|--port)
            GDB_PORT="$2"
            shift 2
            ;;
        -n|--no-wait)
            WAIT_GDB=false
            shift
            ;;
        *)
            echo "Usage: $0 [-k kernel.elf] [-p port] [-n]"
            exit 1
            ;;
    esac
done

# Build command
CMD="$QEMU -machine $MACHINE -cpu rv32 -m $MEMORY -nographic"

if [ -n "$KERNEL" ]; then
    CMD="$CMD -bios none -kernel $KERNEL"
fi

CMD="$CMD -gdb tcp::$GDB_PORT"

if $WAIT_GDB; then
    CMD="$CMD -S"
    echo "Waiting for GDB connection on port $GDB_PORT..."
fi

echo "Running: $CMD"
exec $CMD
```

### 6.2 Integration Test

**File:** `test/remote/integration_spec.spl`

```simple
describe "QEMU Integration":
    # Requires QEMU running:
    # ./script/qemu-riscv32.sh -n

    slow_it "uploads and executes code":
        val debugger = GdbDebugger.connect(DebugConfig(
            host: "localhost",
            port: 1234,
            target: Architecture.RiscV32,
            timeout_ms: 5000
        ))?

        # Simple RISC-V32 program: return 42
        # li a0, 42 (addi a0, zero, 42)
        # ret (jalr zero, ra, 0)
        val code = [
            0x13, 0x05, 0xa0, 0x02,  # addi a0, zero, 42
            0x67, 0x80, 0x00, 0x00   # jalr zero, ra, 0
        ]

        # Upload to RAM
        val addr = 0x80000000u64
        debugger.write_memory(addr, code)?

        # Set PC
        debugger.write_register(32, addr)?  # PC

        # Set SP (stack top)
        debugger.write_register(2, 0x80100000)?  # SP

        # Set return address to trap
        debugger.write_register(1, 0xDEADBEEF)?  # RA

        # Set breakpoint at return
        debugger.set_hw_breakpoint(0xDEADBEEF, BreakpointType.Execute)?

        # Run
        debugger.resume()?
        val halt = debugger.wait_halt(1000)?

        # Check result
        val a0 = debugger.read_register(10)?  # a0
        assert a0 == 42

        debugger.disconnect()

    slow_it "handles multiple breakpoints with sharing":
        val debugger = GdbDebugger.connect(default_config())?
        val bp_mgr = BreakpointManager.new(Box(debugger))

        # Upload code with multiple functions
        upload_test_program(debugger)?

        # Set breakpoints at each function
        bp_mgr.add(0x80000100)  # func1
        bp_mgr.add(0x80000200)  # func2
        bp_mgr.add(0x80000300)  # func3

        # Run and collect hits
        var hits: [u64] = []
        for _ in 0..10:
            val hit = bp_mgr.run_until_bp()?
            if hit.?:
                hits.push(hit.unwrap().addr)

        # Verify all breakpoints were hit
        assert hits.contains(0x80000100)
        assert hits.contains(0x80000200)
        assert hits.contains(0x80000300)

        debugger.disconnect()
```

**Deliverable:** Working QEMU integration with tests

---

## 7. Phase 5: TRACE32 Integration (Week 5)

### 7.1 TRACE32 SFFI

**File:** `src/remote/debugger/trace32_ffi.spl`

```simple
# TRACE32 Remote Control Interface FFI
# Requires: Rust implementation calling TRACE32 Python API

extern fn rt_t32_init(config: text) -> i64
extern fn rt_t32_exit(handle: i64)
extern fn rt_t32_cmd(handle: i64, cmd: text) -> i64
extern fn rt_t32_get_state(handle: i64) -> i64
extern fn rt_t32_read_memory(handle: i64, addr: u64, size: u32) -> [u8]
extern fn rt_t32_write_memory(handle: i64, addr: u64, data: [u8]) -> i64
extern fn rt_t32_read_register(handle: i64, name: text) -> u64
extern fn rt_t32_write_register(handle: i64, name: text, value: u64) -> i64

# State constants
val T32_STATE_DOWN: i64 = 0
val T32_STATE_RUNNING: i64 = 1
val T32_STATE_STOPPED: i64 = 2
```

### 7.2 TRACE32 Debugger

**File:** `src/remote/debugger/trace32.spl`

```simple
class Trace32Debugger implements Debugger:
    handle: i64
    target: RiscV32Target

    static fn connect(config: DebugConfig) -> Result<Trace32Debugger, RemoteError>:
        val t32_config = "NODE={} PORT={} PACKLEN=1024".format(
            config.host, config.port
        )

        val handle = rt_t32_init(t32_config)
        if handle < 0:
            return Err(RemoteError.ConnectionFailed("TRACE32"))

        var debugger = Trace32Debugger(
            handle: handle,
            target: RiscV32Target()
        )

        # Configure for RISC-V
        debugger.cmd("SYStem.CPU RISCV")?
        debugger.cmd("SYStem.Up")?

        Ok(debugger)

    fn disconnect():
        self.cmd("SYStem.Down")
        rt_t32_exit(self.handle)

    fn cmd(command: text) -> Result<(), RemoteError>:
        val result = rt_t32_cmd(self.handle, command)
        if result < 0:
            return Err(RemoteError.ProtocolError(command))
        Ok(())

    # === Memory Operations ===

    fn read_memory(addr: u64, size: usize) -> Result<[u8], RemoteError>:
        val data = rt_t32_read_memory(self.handle, addr, size as u32)
        if data.len() != size:
            return Err(RemoteError.InvalidAddress(addr))
        Ok(data)

    fn write_memory(addr: u64, data: [u8]) -> Result<(), RemoteError>:
        val result = rt_t32_write_memory(self.handle, addr, data)
        if result < 0:
            return Err(RemoteError.InvalidAddress(addr))
        Ok(())

    # === Register Operations ===

    fn read_register(index: usize) -> Result<u64, RemoteError>:
        val name = self.target.register_name(index)
        Ok(rt_t32_read_register(self.handle, name))

    fn write_register(index: usize, value: u64) -> Result<(), RemoteError>:
        val name = self.target.register_name(index)
        val result = rt_t32_write_register(self.handle, name, value)
        if result < 0:
            return Err(RemoteError.InvalidRegister(index))
        Ok(())

    # === Execution Control ===

    fn halt() -> Result<(), RemoteError>:
        self.cmd("Break")

    fn resume() -> Result<(), RemoteError>:
        self.cmd("Go")

    fn single_step() -> Result<(), RemoteError>:
        self.cmd("Step")

    fn wait_halt(timeout_ms: u32) -> Result<HaltReason, RemoteError>:
        val start = time_now_ms()

        loop:
            val state = rt_t32_get_state(self.handle)
            if state == T32_STATE_STOPPED:
                val pc = self.read_register(32)?
                return Ok(HaltReason.Breakpoint(pc))

            if time_now_ms() - start > timeout_ms:
                return Err(RemoteError.Timeout)

            sleep_ms(10)

    # === Breakpoints ===

    fn set_hw_breakpoint(addr: u64, bp_type: BreakpointType)
        -> Result<(), RemoteError>:
        val flags = match bp_type:
            Execute: "/Program /Hard"
            Read: "/Read /Hard"
            Write: "/Write /Hard"
            Access: "/Read /Write /Hard"

        self.cmd("Break.Set 0x{:X} {}".format(addr, flags))

    fn clear_hw_breakpoint(addr: u64, bp_type: BreakpointType)
        -> Result<(), RemoteError>:
        self.cmd("Break.Delete 0x{:X}".format(addr))
```

### 7.3 Tests

**File:** `test/remote/trace32_spec.spl`

```simple
describe "Trace32Debugger":
    # Requires TRACE32 running with RCL server

    slow_it "connects to TRACE32":
        val debugger = Trace32Debugger.connect(DebugConfig(
            host: "localhost",
            port: 20000,
            target: Architecture.RiscV32,
            timeout_ms: 5000
        ))?

        assert debugger.is_connected()
        debugger.disconnect()

    slow_it "reads and writes memory":
        val debugger = connect_trace32()?

        val data = [0x13, 0x00, 0x00, 0x00]
        debugger.write_memory(0x80000000, data)?

        val read_back = debugger.read_memory(0x80000000, 4)?
        assert read_back == data

        debugger.disconnect()
```

**Deliverable:** Complete TRACE32 implementation

---

## 8. Phase 6: Remote Execution Manager (Week 5-6)

### 8.1 Execution Manager

**File:** `src/remote/manager.spl`

```simple
struct ExecutionConfig:
    code_base: u64
    data_base: u64
    stack_top: u64

class RemoteExecutionManager:
    target: Box<dyn Target>
    debugger: Box<dyn Debugger>
    bp_manager: BreakpointManager
    config: ExecutionConfig
    allocated: u64  # Next free address in code region

    static fn new(
        target: Box<dyn Target>,
        debugger: Box<dyn Debugger>,
        config: ExecutionConfig
    ) -> RemoteExecutionManager:
        RemoteExecutionManager(
            target: target,
            debugger: debugger,
            bp_manager: BreakpointManager.new(debugger.clone()),
            config: config,
            allocated: config.code_base
        )

    # === Code Upload ===

    fn upload(code: [u8]) -> Result<u64, RemoteError>:
        # Align to instruction boundary
        val align = self.target.instruction_alignment()
        if self.allocated % align != 0:
            self.allocated += align - (self.allocated % align)

        val addr = self.allocated
        self.debugger.write_memory(addr, code)?
        self.allocated += code.len() as u64

        Ok(addr)

    # === Execution ===

    fn execute(entry: u64, args: [u64]) -> Result<u64, RemoteError>:
        # Set up call frame
        self.setup_call(entry, args)?

        # Set trap address for return
        val trap = 0xFFFFFFFFu64
        self.debugger.write_register(self.target.ra_index(), trap)?
        self.bp_manager.add(trap)

        # Run until return
        loop:
            val hit = self.bp_manager.run_until_bp()?
            match hit:
                Some(h) if h.addr == trap:
                    break
                Some(_):
                    # Other breakpoint, continue
                    continue
                nil:
                    break

        # Get return value
        self.debugger.read_register(self.target.return_register())

    fn setup_call(entry: u64, args: [u64]) -> Result<(), RemoteError>:
        # Set PC
        self.debugger.write_register(self.target.pc_index(), entry)?

        # Set SP
        self.debugger.write_register(
            self.target.sp_index(),
            self.config.stack_top
        )?

        # Set arguments
        val arg_regs = self.target.arg_registers()
        for i in 0..min(args.len(), arg_regs.len()):
            self.debugger.write_register(arg_regs[i], args[i])?

        Ok(())

    # === Debugging ===

    fn add_breakpoint(addr: u64) -> u32:
        self.bp_manager.add(addr)

    fn remove_breakpoint(id: u32):
        self.bp_manager.remove(id)

    fn step() -> Result<(), RemoteError>:
        self.debugger.single_step()

    fn read_registers() -> Result<[u64], RemoteError>:
        var regs: [u64] = []
        for i in 0..self.target.register_count():
            regs.push(self.debugger.read_register(i)?)
        Ok(regs)
```

### 8.2 User-Facing API

**File:** `src/remote/mod.spl`

```simple
# Re-exports for public API
pub use types.*
pub use error.*
pub use target.{Target, RiscV32Target}
pub use debugger.{Debugger, GdbDebugger, Trace32Debugger}
pub use breakpoint.BreakpointManager
pub use manager.{RemoteExecutionManager, ExecutionConfig}

# Convenience functions

fn connect_qemu(port: u16 = 1234) -> Result<RemoteExecutionManager, RemoteError>:
    val debugger = GdbDebugger.connect(DebugConfig(
        host: "localhost",
        port: port,
        target: Architecture.RiscV32,
        timeout_ms: 5000
    ))?

    Ok(RemoteExecutionManager.new(
        target: Box(RiscV32Target()),
        debugger: Box(debugger),
        config: ExecutionConfig(
            code_base: 0x80000000,
            data_base: 0x80100000,
            stack_top: 0x80200000
        )
    ))

fn connect_trace32(port: u16 = 20000) -> Result<RemoteExecutionManager, RemoteError>:
    val debugger = Trace32Debugger.connect(DebugConfig(
        host: "localhost",
        port: port,
        target: Architecture.RiscV32,
        timeout_ms: 5000
    ))?

    Ok(RemoteExecutionManager.new(
        target: Box(RiscV32Target()),
        debugger: Box(debugger),
        config: ExecutionConfig(
            code_base: 0x80000000,
            data_base: 0x80100000,
            stack_top: 0x80200000
        )
    ))
```

**Deliverable:** Complete execution manager with convenience API

---

## 9. Timeline Summary

| Week | Phase | Deliverable |
|------|-------|-------------|
| 1 | 0-1 | Foundation + RISC-V32 Target |
| 2 | 2 | GDB RSP Packet Layer |
| 3 | 2-3 | GDB Debugger + BP Manager |
| 4 | 4 | QEMU Integration Tests |
| 5 | 5 | TRACE32 Implementation |
| 6 | 6 | Execution Manager + API |

**Total:** 6 weeks

---

## 10. Test Matrix

| Test | QEMU | Real HW | TRACE32 Sim |
|------|------|---------|-------------|
| Target trait | ✅ Unit | - | - |
| GDB packet | ✅ Unit | - | - |
| GDB connect | ✅ Slow | ⏳ | - |
| GDB memory | ✅ Slow | ⏳ | - |
| GDB breakpoint | ✅ Slow | ⏳ | - |
| BP sharing | ✅ Slow | ⏳ | - |
| TRACE32 | - | ⏳ | ⏳ |
| Integration | ✅ Slow | ⏳ | ⏳ |

**Legend:** ✅ Implement, ⏳ If available, - Not applicable

---

## 11. Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| QEMU version differences | Medium | Pin to specific version |
| GDB protocol extensions | Low | Stick to core commands |
| TRACE32 API changes | Medium | Version check + fallback |
| HW BP count varies | Medium | Runtime detection |
| Network latency | Low | Local testing default |

---

## 12. Success Criteria

**Phase 1-4 (RISC-V32 + GDB + QEMU):**
- [ ] Can connect to QEMU via GDB
- [ ] Can upload arbitrary machine code
- [ ] Can execute code and get return value
- [ ] Can set 10+ breakpoints with 1 HW BP
- [ ] All breakpoints fire correctly
- [ ] Prediction improves hit rate

**Phase 5 (TRACE32):**
- [ ] Can connect to TRACE32 simulator
- [ ] Same tests pass as GDB
- [ ] Shares BP manager code

**Phase 6 (Integration):**
- [ ] Clean API for users
- [ ] Works with Simple JIT output
- [ ] Documentation complete
