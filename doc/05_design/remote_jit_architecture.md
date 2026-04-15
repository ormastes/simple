# Remote JIT Execution Architecture Design

**Date:** 2026-02-05
**Status:** Design Complete
**Author:** Claude

## 1. System Overview

### 1.1 Goals

1. **Compile on host, execute on target** via debug probe
2. **Support multiple targets:** ARM32, RISC-V32
3. **Support multiple debuggers:** GDB (JTAG), TRACE32
4. **Share hardware breakpoints** via software multiplexing
5. **Minimal interface** for easy porting

### 1.2 Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                              HOST SYSTEM                                 │
│                                                                          │
│  ┌────────────────────┐    ┌────────────────────┐    ┌───────────────┐ │
│  │   Simple Source    │    │   Simple Compiler  │    │  Code Cache   │ │
│  │   (.spl files)     │───▶│   JIT Backend     │───▶│  (Machine     │ │
│  └────────────────────┘    │   (Cranelift)      │    │   Code)       │ │
│                            └────────────────────┘    └───────┬───────┘ │
│                                                              │         │
│  ┌───────────────────────────────────────────────────────────▼───────┐ │
│  │                    Remote Execution Manager                        │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐               │ │
│  │  │ Breakpoint  │  │   Memory    │  │  Register   │               │ │
│  │  │  Manager    │  │   Manager   │  │  Manager    │               │ │
│  │  │  (SW→HW)    │  │  (Upload)   │  │  (R/W)      │               │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘               │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                      │                                  │
│  ┌───────────────────────────────────▼───────────────────────────────┐ │
│  │                    Debug Protocol Adapter                          │ │
│  │  ┌───────────────────────┐    ┌───────────────────────┐          │ │
│  │  │    GDB RSP Client     │    │   TRACE32 RCL Client  │          │ │
│  │  │    (TCP Socket)       │    │   (TCP/API)           │          │ │
│  │  └───────────┬───────────┘    └───────────┬───────────┘          │ │
│  └──────────────┼────────────────────────────┼───────────────────────┘ │
└─────────────────┼────────────────────────────┼───────────────────────── │
                  │                            │                          │
══════════════════╪════════════════════════════╪════════ Network ════════
                  │                            │
┌─────────────────┼────────────────────────────┼──────────────────────────┐
│                 │       DEBUG PROBES         │                          │
│  ┌──────────────▼──────────────┐  ┌─────────▼────────────────────┐    │
│  │   OpenOCD / GDB Server      │  │      TRACE32 PowerDebug      │    │
│  │   (JTAG/SWD Interface)      │  │      (JTAG/SWD/cJTAG)        │    │
│  └──────────────┬──────────────┘  └─────────┬────────────────────┘    │
└─────────────────┼────────────────────────────┼──────────────────────────┘
                  │                            │
══════════════════╪════════════════════════════╪════════ JTAG/SWD ═══════
                  │                            │
┌─────────────────▼────────────────────────────▼──────────────────────────┐
│                         TARGET DEVICE                                    │
│                                                                          │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                    Debug Hardware                                  │ │
│  │  ┌─────────────────────────────────────────────────────────────┐ │ │
│  │  │  ARM32 (Cortex-M):          │  RISC-V32:                    │ │ │
│  │  │  - FPB: 6-8 instruction BP  │  - Triggers: 2-4 configurable │ │ │
│  │  │  - DWT: 4 data watchpoints  │  - Debug Module               │ │ │
│  │  └─────────────────────────────────────────────────────────────┘ │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────────┐ │
│  │   Code Region    │  │   Data Region    │  │   Peripherals        │ │
│  │   (Executable)   │  │   (Read/Write)   │  │   (MMIO)             │ │
│  │   0x08000000     │  │   0x20000000     │  │   0x40000000         │ │
│  └──────────────────┘  └──────────────────┘  └──────────────────────┘ │
└──────────────────────────────────────────────────────────────────────────┘
```

---

## 2. Target Platform Abstraction

### 2.1 Target Trait

```simple
# Target architecture abstraction
trait Target:
    # Identification
    fn name() -> text
    fn arch() -> Architecture
    fn endianness() -> Endianness

    # Register operations
    fn register_count() -> usize
    fn register_name(index: usize) -> text
    fn register_size(index: usize) -> usize
    fn pc_register_index() -> usize
    fn sp_register_index() -> usize
    fn return_register_index() -> usize

    # Calling convention
    fn arg_registers() -> [usize]
    fn return_registers() -> [usize]
    fn callee_saved_registers() -> [usize]

    # Debug hardware
    fn hw_breakpoint_count() -> usize
    fn hw_watchpoint_count() -> usize
    fn supports_single_step() -> bool

    # Instruction info
    fn breakpoint_instruction() -> [u8]
    fn min_instruction_size() -> usize
    fn max_instruction_size() -> usize

    # Code generation
    fn code_generator() -> Box<dyn CodeGenerator>

enum Architecture:
    Arm32
    Arm64
    RiscV32
    RiscV64
    X86
    X86_64

enum Endianness:
    Little
    Big
```

### 2.2 ARM32 Target Implementation

```simple
class Arm32Target implements Target:
    fn name() -> text:
        "ARM32 (Cortex-M)"

    fn arch() -> Architecture:
        Architecture.Arm32

    fn endianness() -> Endianness:
        Endianness.Little

    fn register_count() -> usize:
        17  # R0-R15 + CPSR

    fn register_name(index: usize) -> text:
        match index:
            0..=12: "R{index}"
            13: "SP"
            14: "LR"
            15: "PC"
            16: "CPSR"
            _: "UNKNOWN"

    fn register_size(index: usize) -> usize:
        4  # 32-bit

    fn pc_register_index() -> usize:
        15

    fn sp_register_index() -> usize:
        13

    fn return_register_index() -> usize:
        0  # R0

    fn arg_registers() -> [usize]:
        [0, 1, 2, 3]  # R0-R3

    fn return_registers() -> [usize]:
        [0, 1]  # R0-R1

    fn callee_saved_registers() -> [usize]:
        [4, 5, 6, 7, 8, 9, 10, 11]  # R4-R11

    fn hw_breakpoint_count() -> usize:
        6  # FPB (minimum)

    fn hw_watchpoint_count() -> usize:
        4  # DWT

    fn supports_single_step() -> bool:
        true  # Via debug halting

    fn breakpoint_instruction() -> [u8]:
        [0x00, 0xBE]  # BKPT #0 (Thumb)

    fn min_instruction_size() -> usize:
        2  # Thumb

    fn max_instruction_size() -> usize:
        4  # Thumb-2

    fn code_generator() -> Box<dyn CodeGenerator>:
        Box(Arm32CodeGenerator())
```

### 2.3 RISC-V32 Target Implementation

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
        val abi_names = [
            "zero", "ra", "sp", "gp", "tp",
            "t0", "t1", "t2",
            "s0", "s1",
            "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
            "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
            "t3", "t4", "t5", "t6"
        ]
        if index < 32:
            abi_names[index]
        elif index == 32:
            "pc"
        else:
            "UNKNOWN"

    fn register_size(index: usize) -> usize:
        4  # 32-bit

    fn pc_register_index() -> usize:
        32

    fn sp_register_index() -> usize:
        2  # x2/sp

    fn return_register_index() -> usize:
        10  # x10/a0

    fn arg_registers() -> [usize]:
        [10, 11, 12, 13, 14, 15, 16, 17]  # a0-a7

    fn return_registers() -> [usize]:
        [10, 11]  # a0-a1

    fn callee_saved_registers() -> [usize]:
        [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]  # s0-s11

    fn hw_breakpoint_count() -> usize:
        4  # Typical (QEMU default)

    fn hw_watchpoint_count() -> usize:
        4  # Shared with breakpoints

    fn supports_single_step() -> bool:
        true  # Via debug module

    fn breakpoint_instruction() -> [u8]:
        [0x73, 0x00, 0x10, 0x00]  # EBREAK (little-endian)

    fn min_instruction_size() -> usize:
        2  # Compressed (C extension)

    fn max_instruction_size() -> usize:
        4  # Standard

    fn code_generator() -> Box<dyn CodeGenerator>:
        Box(RiscV32CodeGenerator())
```

---

## 3. Debug Protocol Abstraction

### 3.1 Debugger Trait

```simple
# Debug protocol abstraction
trait Debugger:
    # Connection
    fn connect(config: DebugConfig) -> Result<Self, DebugError>
    fn disconnect()
    fn is_connected() -> bool

    # Memory operations
    fn read_memory(addr: u64, size: usize) -> Result<[u8], DebugError>
    fn write_memory(addr: u64, data: [u8]) -> Result<(), DebugError>

    # Register operations
    fn read_register(index: usize) -> Result<u64, DebugError>
    fn write_register(index: usize, value: u64) -> Result<(), DebugError>
    fn read_all_registers() -> Result<[u64], DebugError>
    fn write_all_registers(values: [u64]) -> Result<(), DebugError>

    # Execution control
    fn halt() -> Result<(), DebugError>
    fn resume() -> Result<(), DebugError>
    fn single_step() -> Result<(), DebugError>
    fn is_halted() -> Result<bool, DebugError>
    fn wait_for_halt(timeout_ms: u32) -> Result<HaltReason, DebugError>

    # Breakpoints (hardware)
    fn set_hw_breakpoint(index: usize, addr: u64, bp_type: BreakpointType)
        -> Result<(), DebugError>
    fn clear_hw_breakpoint(index: usize) -> Result<(), DebugError>
    fn get_hw_breakpoint_count() -> usize

    # Target info
    fn get_target_info() -> Result<TargetInfo, DebugError>

struct DebugConfig:
    host: text
    port: u16
    target: Architecture
    options: Dict<text, text>

enum BreakpointType:
    Execute
    Read
    Write
    Access

enum HaltReason:
    Breakpoint(addr: u64)
    Watchpoint(addr: u64, access: AccessType)
    SingleStep
    Halt
    Exception(code: u32)
    Unknown

enum AccessType:
    Read
    Write

struct TargetInfo:
    name: text
    arch: Architecture
    endianness: Endianness
    memory_map: [MemoryRegion]

struct MemoryRegion:
    start: u64
    end: u64
    permissions: Permissions
    name: text

enum Permissions:
    ReadOnly
    ReadWrite
    Execute
    ReadWriteExecute

enum DebugError:
    ConnectionFailed(text)
    Timeout
    TargetNotHalted
    InvalidAddress(u64)
    InvalidRegister(usize)
    BreakpointFull
    ProtocolError(text)
    NotSupported(text)
```

### 3.2 GDB RSP Implementation

```simple
class GdbDebugger implements Debugger:
    socket: TcpSocket
    target: Architecture
    packet_buffer: [u8]
    ack_mode: bool

    # === Connection ===

    fn connect(config: DebugConfig) -> Result<Self, DebugError>:
        val socket = TcpSocket.connect(config.host, config.port)?
        socket.set_timeout(5000)

        var debugger = GdbDebugger(
            socket: socket,
            target: config.target,
            packet_buffer: [],
            ack_mode: true
        )

        # Handshake
        debugger.send_packet("qSupported:hwbreak+;swbreak+")?
        val features = debugger.recv_packet()?

        # Disable ACK mode if supported
        if features.contains("QStartNoAckMode+"):
            debugger.send_packet("QStartNoAckMode")?
            debugger.recv_packet()?
            debugger.ack_mode = false

        Ok(debugger)

    fn disconnect():
        self.send_packet("D")  # Detach
        self.socket.close()

    fn is_connected() -> bool:
        self.socket.is_connected()

    # === Memory Operations ===

    fn read_memory(addr: u64, size: usize) -> Result<[u8], DebugError>:
        val cmd = "m{:x},{:x}".format(addr, size)
        self.send_packet(cmd)?
        val response = self.recv_packet()?

        if response.starts_with("E"):
            return Err(DebugError.InvalidAddress(addr))

        Ok(self.decode_hex(response))

    fn write_memory(addr: u64, data: [u8]) -> Result<(), DebugError>:
        val hex_data = self.encode_hex(data)
        val cmd = "M{:x},{:x}:{}".format(addr, data.len(), hex_data)
        self.send_packet(cmd)?
        val response = self.recv_packet()?

        if response != "OK":
            return Err(DebugError.InvalidAddress(addr))

        Ok(())

    # === Register Operations ===

    fn read_register(index: usize) -> Result<u64, DebugError>:
        val cmd = "p{:x}".format(index)
        self.send_packet(cmd)?
        val response = self.recv_packet()?

        if response.starts_with("E"):
            return Err(DebugError.InvalidRegister(index))

        Ok(self.decode_hex_u64(response))

    fn write_register(index: usize, value: u64) -> Result<(), DebugError>:
        val size = self.register_size(index)
        val hex_value = self.encode_hex_u64(value, size)
        val cmd = "P{:x}={}".format(index, hex_value)
        self.send_packet(cmd)?
        val response = self.recv_packet()?

        if response != "OK":
            return Err(DebugError.InvalidRegister(index))

        Ok(())

    # === Execution Control ===

    fn halt() -> Result<(), DebugError>:
        # Send break (Ctrl-C)
        self.socket.write([0x03])
        self.wait_for_halt(1000)
        Ok(())

    fn resume() -> Result<(), DebugError>:
        self.send_packet("c")?
        Ok(())

    fn single_step() -> Result<(), DebugError>:
        self.send_packet("s")?
        self.wait_for_halt(1000)?
        Ok(())

    fn is_halted() -> Result<bool, DebugError>:
        # Send status query
        self.send_packet("?")?
        val response = self.recv_packet()?
        Ok(response.starts_with("S") or response.starts_with("T"))

    fn wait_for_halt(timeout_ms: u32) -> Result<HaltReason, DebugError>:
        self.socket.set_timeout(timeout_ms)
        val response = self.recv_packet()?

        self.parse_stop_reply(response)

    # === Breakpoints ===

    fn set_hw_breakpoint(index: usize, addr: u64, bp_type: BreakpointType)
        -> Result<(), DebugError>:
        val type_code = match bp_type:
            Execute: 1
            Write: 2
            Read: 3
            Access: 4

        val kind = 4  # 4 bytes for 32-bit
        val cmd = "Z{},{:x},{}".format(type_code, addr, kind)
        self.send_packet(cmd)?
        val response = self.recv_packet()?

        if response == "":
            return Err(DebugError.NotSupported("Hardware breakpoints"))
        if response != "OK":
            return Err(DebugError.BreakpointFull)

        Ok(())

    fn clear_hw_breakpoint(index: usize) -> Result<(), DebugError>:
        # GDB doesn't use index, just address
        # We need to track addresses separately
        Err(DebugError.NotSupported("Clear by index"))

    fn clear_hw_breakpoint_at(addr: u64, bp_type: BreakpointType)
        -> Result<(), DebugError>:
        val type_code = match bp_type:
            Execute: 1
            Write: 2
            Read: 3
            Access: 4

        val cmd = "z{},{:x},4".format(type_code, addr)
        self.send_packet(cmd)?
        val response = self.recv_packet()?

        if response != "OK":
            return Err(DebugError.ProtocolError("Failed to clear breakpoint"))

        Ok(())

    fn get_hw_breakpoint_count() -> usize:
        # Query from target or use default
        4

    # === Protocol Helpers ===

    fn send_packet(data: text) -> Result<(), DebugError>:
        val checksum = self.compute_checksum(data)
        val packet = "${data}#{checksum:02x}"
        self.socket.write(packet.as_bytes())?

        if self.ack_mode:
            val ack = self.socket.read(1)?
            if ack[0] != '+' as u8:
                return Err(DebugError.ProtocolError("NACK received"))

        Ok(())

    fn recv_packet() -> Result<text, DebugError>:
        # Read until '#'
        var buffer: [u8] = []
        var state = 0  # 0=wait $, 1=data, 2=checksum

        loop:
            val byte = self.socket.read(1)?[0]
            match state:
                0:
                    if byte == '$' as u8:
                        state = 1
                1:
                    if byte == '#' as u8:
                        state = 2
                    else:
                        buffer.push(byte)
                2:
                    # Read 2 checksum bytes
                    val cs1 = byte
                    val cs2 = self.socket.read(1)?[0]
                    # Verify checksum (optional)
                    break

        if self.ack_mode:
            self.socket.write(['+' as u8])?

        Ok(String.from_utf8(buffer))

    fn compute_checksum(data: text) -> u8:
        var sum: u32 = 0
        for byte in data.as_bytes():
            sum = (sum + byte as u32) % 256
        sum as u8

    fn parse_stop_reply(response: text) -> Result<HaltReason, DebugError>:
        if response.starts_with("S"):
            val signal = u8.from_hex(response[1:3])
            match signal:
                5: Ok(HaltReason.Breakpoint(0))  # SIGTRAP
                _: Ok(HaltReason.Exception(signal as u32))
        elif response.starts_with("T"):
            # Extended format: T05thread:1;
            Ok(HaltReason.Breakpoint(0))
        else:
            Err(DebugError.ProtocolError("Unknown stop reply"))
```

### 3.3 TRACE32 Implementation

```simple
class Trace32Debugger implements Debugger:
    handle: i64
    target: Architecture
    connected: bool

    # === FFI Declarations ===

    extern fn rt_t32_init(config: text) -> i64
    extern fn rt_t32_exit(handle: i64)
    extern fn rt_t32_cmd(handle: i64, cmd: text) -> i64
    extern fn rt_t32_get_state(handle: i64) -> i64
    extern fn rt_t32_read_memory(handle: i64, addr: u64, size: u32) -> [u8]
    extern fn rt_t32_write_memory(handle: i64, addr: u64, data: [u8]) -> i64
    extern fn rt_t32_read_register(handle: i64, name: text) -> u64
    extern fn rt_t32_write_register(handle: i64, name: text, value: u64) -> i64

    # === Connection ===

    fn connect(config: DebugConfig) -> Result<Self, DebugError>:
        val t32_config = "NODE={} PORT={} PACKLEN=1024".format(
            config.host, config.port
        )

        val handle = rt_t32_init(t32_config)
        if handle < 0:
            return Err(DebugError.ConnectionFailed("TRACE32 init failed"))

        var debugger = Trace32Debugger(
            handle: handle,
            target: config.target,
            connected: true
        )

        # Configure target CPU
        val cpu_cmd = match config.target:
            Architecture.Arm32: "SYStem.CPU ARM.Cortex-M4"
            Architecture.RiscV32: "SYStem.CPU RISCV"
            _: return Err(DebugError.NotSupported("Target"))

        debugger.cmd(cpu_cmd)?

        # Connect to target
        debugger.cmd("SYStem.Up")?

        Ok(debugger)

    fn disconnect():
        if self.connected:
            self.cmd("SYStem.Down")
            rt_t32_exit(self.handle)
            self.connected = false

    fn is_connected() -> bool:
        self.connected

    # === Memory Operations ===

    fn read_memory(addr: u64, size: usize) -> Result<[u8], DebugError>:
        val data = rt_t32_read_memory(self.handle, addr, size as u32)
        if data.len() != size:
            return Err(DebugError.InvalidAddress(addr))
        Ok(data)

    fn write_memory(addr: u64, data: [u8]) -> Result<(), DebugError>:
        val result = rt_t32_write_memory(self.handle, addr, data)
        if result < 0:
            return Err(DebugError.InvalidAddress(addr))
        Ok(())

    # === Register Operations ===

    fn read_register(index: usize) -> Result<u64, DebugError>:
        val name = self.register_name(index)
        val value = rt_t32_read_register(self.handle, name)
        Ok(value)

    fn write_register(index: usize, value: u64) -> Result<(), DebugError>:
        val name = self.register_name(index)
        val result = rt_t32_write_register(self.handle, name, value)
        if result < 0:
            return Err(DebugError.InvalidRegister(index))
        Ok(())

    fn read_all_registers() -> Result<[u64], DebugError>:
        val count = self.register_count()
        var regs: [u64] = []
        for i in 0..count:
            regs.push(self.read_register(i)?)
        Ok(regs)

    fn write_all_registers(values: [u64]) -> Result<(), DebugError>:
        for i in 0..values.len():
            self.write_register(i, values[i])?
        Ok(())

    # === Execution Control ===

    fn halt() -> Result<(), DebugError>:
        self.cmd("Break")?
        Ok(())

    fn resume() -> Result<(), DebugError>:
        self.cmd("Go")?
        Ok(())

    fn single_step() -> Result<(), DebugError>:
        self.cmd("Step")?
        Ok(())

    fn is_halted() -> Result<bool, DebugError>:
        val state = rt_t32_get_state(self.handle)
        # TRACE32 states: 0=down, 1=running, 2=stopped
        Ok(state == 2)

    fn wait_for_halt(timeout_ms: u32) -> Result<HaltReason, DebugError>:
        val start = time_now_ms()
        loop:
            if self.is_halted()?:
                # Query halt reason
                val pc = self.read_register(self.pc_index())?
                return Ok(HaltReason.Breakpoint(pc))

            if time_now_ms() - start > timeout_ms:
                return Err(DebugError.Timeout)

            sleep_ms(10)

    # === Breakpoints ===

    fn set_hw_breakpoint(index: usize, addr: u64, bp_type: BreakpointType)
        -> Result<(), DebugError>:
        val type_flag = match bp_type:
            Execute: "/Program /Hard"
            Read: "/Read /Hard"
            Write: "/Write /Hard"
            Access: "/Read /Write /Hard"

        val cmd = "Break.Set 0x{:X} {}".format(addr, type_flag)
        self.cmd(cmd)?
        Ok(())

    fn clear_hw_breakpoint(index: usize) -> Result<(), DebugError>:
        # TRACE32 doesn't use index, clear all or by address
        self.cmd("Break.Delete /ALL")?
        Ok(())

    fn get_hw_breakpoint_count() -> usize:
        # Query from target
        match self.target:
            Architecture.Arm32: 6
            Architecture.RiscV32: 4
            _: 4

    # === Helpers ===

    fn cmd(command: text) -> Result<(), DebugError>:
        val result = rt_t32_cmd(self.handle, command)
        if result < 0:
            return Err(DebugError.ProtocolError(command))
        Ok(())

    fn register_name(index: usize) -> text:
        match self.target:
            Architecture.Arm32:
                match index:
                    0..=12: "R{index}"
                    13: "SP"
                    14: "LR"
                    15: "PC"
                    16: "CPSR"
                    _: "R0"
            Architecture.RiscV32:
                # Use x0-x31 naming
                "x{index}"
            _: "R{index}"
```

---

## 4. Hardware Breakpoint Multiplexer

### 4.1 Breakpoint Manager

```simple
# Software breakpoint multiplexed onto single HW breakpoint
class BreakpointManager:
    debugger: Box<dyn Debugger>
    sw_breakpoints: [SoftwareBreakpoint]
    hw_bp_index: usize         # Which HW BP we're using (usually 0)
    current_hw_addr: u64?      # Currently set HW BP address
    hit_prediction: HitPredictor

    struct SoftwareBreakpoint:
        id: u32
        addr: u64
        enabled: bool
        hit_count: u32
        condition: text?

    static fn new(debugger: Box<dyn Debugger>) -> BreakpointManager:
        BreakpointManager(
            debugger: debugger,
            sw_breakpoints: [],
            hw_bp_index: 0,
            current_hw_addr: nil,
            hit_prediction: HitPredictor.new()
        )

    # === Breakpoint Management ===

    me add_breakpoint(addr: u64) -> u32:
        val id = self.next_id()
        self.sw_breakpoints.push(SoftwareBreakpoint(
            id: id,
            addr: addr,
            enabled: true,
            hit_count: 0,
            condition: nil
        ))

        # If first BP, set HW breakpoint
        if self.sw_breakpoints.len() == 1:
            self.set_hw_breakpoint(addr)

        id

    me remove_breakpoint(id: u32):
        self.sw_breakpoints = self.sw_breakpoints.filter(\bp: bp.id != id)

        # Update HW breakpoint
        self.update_hw_breakpoint()

    me enable_breakpoint(id: u32):
        for bp in self.sw_breakpoints:
            if bp.id == id:
                bp.enabled = true
        self.update_hw_breakpoint()

    me disable_breakpoint(id: u32):
        for bp in self.sw_breakpoints:
            if bp.id == id:
                bp.enabled = false
        self.update_hw_breakpoint()

    # === Execution with Breakpoint Sharing ===

    fn run_until_breakpoint() -> Result<BreakpointHit?, DebugError>:
        loop:
            # Ensure HW BP is set
            self.update_hw_breakpoint()

            # Resume execution
            self.debugger.resume()?

            # Wait for halt
            val reason = self.debugger.wait_for_halt(30000)?

            match reason:
                HaltReason.Breakpoint(addr):
                    # Check if it's a real breakpoint or just HW BP rotation
                    val hit = self.check_breakpoint_hit(addr)
                    if hit.?:
                        return Ok(hit)
                    # Not a real BP, rotate and continue
                    self.rotate_hw_breakpoint()

                HaltReason.Exception(code):
                    return Err(DebugError.TargetException(code))

                _:
                    return Err(DebugError.UnexpectedHalt)

    fn check_breakpoint_hit(addr: u64) -> BreakpointHit?:
        for bp in self.sw_breakpoints:
            if bp.addr == addr and bp.enabled:
                bp.hit_count += 1
                self.hit_prediction.record_hit(addr)

                return Some(BreakpointHit(
                    id: bp.id,
                    addr: addr,
                    hit_count: bp.hit_count
                ))

        nil

    # === HW Breakpoint Rotation ===

    me update_hw_breakpoint():
        val enabled_bps = self.sw_breakpoints.filter(\bp: bp.enabled)

        if enabled_bps.is_empty():
            self.clear_hw_breakpoint()
            return

        # Use predictor to choose next BP
        val next_addr = self.hit_prediction.predict_next(
            enabled_bps.map(\bp: bp.addr)
        )

        if Some(next_addr) != self.current_hw_addr:
            self.set_hw_breakpoint(next_addr)

    me rotate_hw_breakpoint():
        val enabled_bps = self.sw_breakpoints.filter(\bp: bp.enabled)

        if enabled_bps.len() <= 1:
            return  # No rotation needed

        # Find current index and rotate
        var current_idx = 0
        for i in 0..enabled_bps.len():
            if Some(enabled_bps[i].addr) == self.current_hw_addr:
                current_idx = i
                break

        val next_idx = (current_idx + 1) % enabled_bps.len()
        self.set_hw_breakpoint(enabled_bps[next_idx].addr)

    me set_hw_breakpoint(addr: u64):
        # Clear existing
        if self.current_hw_addr.?:
            self.debugger.clear_hw_breakpoint(self.hw_bp_index)

        # Set new
        self.debugger.set_hw_breakpoint(
            self.hw_bp_index,
            addr,
            BreakpointType.Execute
        )
        self.current_hw_addr = Some(addr)

    me clear_hw_breakpoint():
        if self.current_hw_addr.?:
            self.debugger.clear_hw_breakpoint(self.hw_bp_index)
            self.current_hw_addr = nil

struct BreakpointHit:
    id: u32
    addr: u64
    hit_count: u32
```

### 4.2 Hit Predictor

```simple
# Predicts which breakpoint will be hit next
class HitPredictor:
    history: [u64]          # Recent addresses
    hit_counts: Dict<u64, u32>
    max_history: usize

    static fn new() -> HitPredictor:
        HitPredictor(
            history: [],
            hit_counts: {},
            max_history: 100
        )

    me record_hit(addr: u64):
        self.history.push(addr)
        if self.history.len() > self.max_history:
            self.history.remove(0)

        val count = self.hit_counts.get(addr) ?? 0
        self.hit_counts[addr] = count + 1

    fn predict_next(candidates: [u64]) -> u64:
        if candidates.is_empty():
            panic("No candidates for prediction")

        if candidates.len() == 1:
            return candidates[0]

        # Strategy 1: Most frequently hit
        var best_addr = candidates[0]
        var best_count = 0

        for addr in candidates:
            val count = self.hit_counts.get(addr) ?? 0
            if count > best_count:
                best_count = count
                best_addr = addr

        # Strategy 2: If no history, use lowest address (sequential code)
        if best_count == 0:
            best_addr = candidates.min()

        best_addr

    fn predict_next_pc_relative(candidates: [u64], current_pc: u64) -> u64:
        # Strategy 3: Closest to current PC (for sequential code)
        var best_addr = candidates[0]
        var best_distance = u64.MAX

        for addr in candidates:
            val distance = if addr > current_pc:
                addr - current_pc
            else:
                current_pc - addr

            if distance < best_distance:
                best_distance = distance
                best_addr = addr

        best_addr
```

---

## 5. Remote Execution Manager

### 5.1 Core Manager

```simple
# Main entry point for remote JIT execution
class RemoteExecutionManager:
    target: Box<dyn Target>
    debugger: Box<dyn Debugger>
    bp_manager: BreakpointManager
    code_generator: Box<dyn CodeGenerator>
    memory_map: MemoryMap
    loaded_code: Dict<text, CodeInfo>

    struct CodeInfo:
        addr: u64
        size: usize
        entry_point: u64
        symbol_table: Dict<text, u64>

    struct MemoryMap:
        code_start: u64
        code_end: u64
        data_start: u64
        data_end: u64
        stack_top: u64

    static fn new(
        target: Box<dyn Target>,
        debugger: Box<dyn Debugger>,
        memory_map: MemoryMap
    ) -> RemoteExecutionManager:
        RemoteExecutionManager(
            target: target,
            debugger: debugger,
            bp_manager: BreakpointManager.new(debugger.clone()),
            code_generator: target.code_generator(),
            memory_map: memory_map,
            loaded_code: {}
        )

    # === Code Upload ===

    fn upload_code(name: text, machine_code: [u8]) -> Result<CodeInfo, Error>:
        # Find free space in code region
        val addr = self.allocate_code_space(machine_code.len())?

        # Upload to target
        self.debugger.write_memory(addr, machine_code)?

        # Create info
        val info = CodeInfo(
            addr: addr,
            size: machine_code.len(),
            entry_point: addr,
            symbol_table: {}
        )

        self.loaded_code[name] = info
        Ok(info)

    fn upload_simple_source(source: text) -> Result<CodeInfo, Error>:
        # Compile to machine code
        val machine_code = self.code_generator.compile(source)?

        # Upload
        self.upload_code("main", machine_code)

    # === Execution ===

    fn execute(name: text, args: [u64]) -> Result<u64, Error>:
        val info = self.loaded_code.get(name)?

        # Set up registers
        self.setup_call(info.entry_point, args)?

        # Set breakpoint at return
        val return_bp = self.bp_manager.add_breakpoint(
            self.get_return_address()?
        )

        # Run
        self.debugger.resume()?
        val halt = self.debugger.wait_for_halt(60000)?

        # Clean up
        self.bp_manager.remove_breakpoint(return_bp)

        # Get return value
        val result = self.debugger.read_register(
            self.target.return_register_index()
        )?

        Ok(result)

    fn execute_with_debugging(
        name: text,
        args: [u64],
        debug_callback: fn(DebugEvent) -> DebugAction
    ) -> Result<u64, Error>:
        val info = self.loaded_code.get(name)?

        # Set up
        self.setup_call(info.entry_point, args)?

        # Execution loop
        loop:
            val halt = self.bp_manager.run_until_breakpoint()?

            match halt:
                Some(bp_hit):
                    val event = DebugEvent.Breakpoint(bp_hit)
                    val action = debug_callback(event)

                    match action:
                        DebugAction.Continue:
                            continue
                        DebugAction.StepInto:
                            self.single_step_into()?
                        DebugAction.StepOver:
                            self.single_step_over()?
                        DebugAction.Stop:
                            break
                nil:
                    # Execution finished
                    break

        self.debugger.read_register(self.target.return_register_index())

    # === Call Setup ===

    fn setup_call(entry: u64, args: [u64]) -> Result<(), Error>:
        # Set PC to entry point
        self.debugger.write_register(self.target.pc_register_index(), entry)?

        # Set SP to stack top
        self.debugger.write_register(
            self.target.sp_register_index(),
            self.memory_map.stack_top
        )?

        # Set arguments
        val arg_regs = self.target.arg_registers()
        for i in 0..min(args.len(), arg_regs.len()):
            self.debugger.write_register(arg_regs[i], args[i])?

        # Push return address (trap address)
        val trap_addr = self.get_trap_address()
        self.push_stack(trap_addr)?

        Ok(())

    fn push_stack(value: u64) -> Result<(), Error>:
        # Read SP
        var sp = self.debugger.read_register(self.target.sp_register_index())?

        # Decrement SP
        sp -= self.target.register_size(0) as u64

        # Write value
        val bytes = self.encode_value(value)
        self.debugger.write_memory(sp, bytes)?

        # Update SP
        self.debugger.write_register(self.target.sp_register_index(), sp)

enum DebugEvent:
    Breakpoint(BreakpointHit)
    SingleStep(u64)  # PC
    Exception(u32)

enum DebugAction:
    Continue
    StepInto
    StepOver
    Stop
```

---

## 6. Combination Matrix

### 6.1 All Combinations

| # | Target | Debugger | Protocol | Priority | Status |
|---|--------|----------|----------|----------|--------|
| 1 | RISC-V32 | GDB | RSP/TCP | **P0** | **Implement** |
| 2 | RISC-V32 | TRACE32 | RCL/TCP | P1 | Implement |
| 3 | ARM32 | GDB | RSP/TCP | P2 | Design |
| 4 | ARM32 | TRACE32 | RCL/TCP | P2 | Design |
| 5 | RISC-V32 | GDB | RSP/Serial | P3 | Design |
| 6 | ARM32 | GDB | RSP/Serial | P3 | Design |
| 7 | RISC-V32 | OpenOCD | RSP/TCP | P3 | Design |
| 8 | ARM32 | OpenOCD | RSP/TCP | P3 | Design |

### 6.2 Implementation Order

**Phase 1: RISC-V32 + QEMU + GDB (P0)**
- Easiest to test (no hardware required)
- GDB protocol well-documented
- QEMU provides consistent behavior

**Phase 2: RISC-V32 + TRACE32 (P1)**
- Add TRACE32 backend
- Test with real hardware if available
- Share BP manager code

**Phase 3: ARM32 + GDB (P2)**
- Add ARM32 target
- Reuse GDB debugger
- Add Thumb-2 code generation

**Phase 4: ARM32 + TRACE32 (P2)**
- Combine ARM32 target + TRACE32 debugger
- Mostly configuration changes

---

## 7. File Structure

```
src/
└── remote/
    ├── mod.spl                     # Module exports
    ├── target/
    │   ├── mod.spl                 # Target trait
    │   ├── arm32.spl               # ARM32 target
    │   └── riscv32.spl             # RISC-V32 target
    ├── debugger/
    │   ├── mod.spl                 # Debugger trait
    │   ├── gdb.spl                 # GDB RSP implementation
    │   └── trace32.spl             # TRACE32 implementation
    ├── breakpoint/
    │   ├── mod.spl                 # Breakpoint manager
    │   └── predictor.spl           # Hit predictor
    ├── codegen/
    │   ├── mod.spl                 # Code generator trait
    │   ├── arm32_gen.spl           # ARM32 code generation
    │   └── riscv32_gen.spl         # RISC-V32 code generation
    └── manager.spl                 # Remote execution manager

test/
└── remote/
    ├── gdb_spec.spl                # GDB protocol tests
    ├── trace32_spec.spl            # TRACE32 tests
    ├── breakpoint_spec.spl         # BP sharing tests
    └── integration_spec.spl        # End-to-end tests

doc/
├── research/
│   └── remote_jit_execution_research.md
├── design/
│   └── remote_jit_architecture.md
└── plan/
    └── remote_jit_implementation_plan.md
```

---

## 8. API Summary

### 8.1 User-Facing API

```simple
use remote (RemoteExecutionManager, MemoryMap)
use remote.target (RiscV32Target)
use remote.debugger (GdbDebugger)

# Connect to QEMU
val debugger = GdbDebugger.connect(DebugConfig(
    host: "localhost",
    port: 1234,
    target: Architecture.RiscV32
))?

# Create manager
val manager = RemoteExecutionManager.new(
    target: Box(RiscV32Target()),
    debugger: Box(debugger),
    memory_map: MemoryMap(
        code_start: 0x80000000,
        code_end: 0x80100000,
        data_start: 0x80100000,
        data_end: 0x80200000,
        stack_top: 0x80200000
    )
)

# Upload and execute Simple code
val result = manager.execute_simple(
    "fn add(a: i64, b: i64) -> i64: return a + b",
    "add",
    [5, 3]
)?

print "Result: {result}"  # Output: 8
```

### 8.2 Debugging API

```simple
# Add breakpoints
manager.add_breakpoint(0x80000010)
manager.add_breakpoint(0x80000020)

# Execute with debugging
val result = manager.execute_with_debugging("main", [], \event:
    match event:
        DebugEvent.Breakpoint(hit):
            print "Hit BP at 0x{hit.addr:X}"
            val regs = manager.debugger.read_all_registers()?
            print "Registers: {regs}"
            DebugAction.Continue

        DebugEvent.Exception(code):
            print "Exception: {code}"
            DebugAction.Stop
)?
```
