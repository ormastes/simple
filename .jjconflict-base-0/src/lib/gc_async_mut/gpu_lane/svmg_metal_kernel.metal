// SVM-G stack-machine interpreter -- Metal Shading Language compute kernel
// (stream N3 of the Metal GPU lane).
//
// Design: doc/05_design/app/tools/metal_gpu_lane_and_vulkan_jit_notebook_architecture_2026-08-09.md
// section 5, on top of doc/05_design/runtime/gpu_remote_interpreter_architecture.md
// section 4.1/4.3/6.3.
//
// This is a PORT, not a new design. It is the THIRD device-side
// reimplementation of the host reference VM's `SvmgVm.step`/`SvmgVm.run`
// (src/lib/common/svmg/ref_vm.spl), after:
//   - src/lib/gc_async_mut/gpu_lane/svmg_cuda_kernel.ptx    (CUDA / PTX)
//   - src/lib/gc_async_mut/gpu_lane/svmg_vulkan_kernel.spvasm (Vulkan / SPIR-V)
// It implements the same 50-opcode SVM-G ISA (src/lib/common/svmg/opcodes.spl)
// against the byte-for-byte identical GMB-1 wire format
// (src/lib/common/svmg/mailbox_const.spl, src/lib/common/svmg/sgp.spl), so the
// SAME D3 conformance vector table checks all three backends and the host
// reference VM ("two implementations, one conformance suite" -- now three).
//
// Matching contracts, all deliberately identical to the two siblings:
//   * PC model: code-array-relative, opcode fetched at arena[code_off + pc].
//   * i32 wraparound: 32-bit words carry raw bit patterns; arithmetic is done
//     in `uint` and bitcast, which wraps exactly like ref_vm's `_wrap_i32`.
//   * Traps: TRAP_OOB=1, TRAP_DIV0=2, call-stack overflow=3. ref_vm *panics*
//     on call-stack overflow (a host/assembler bug), but a device cannot
//     panic, so it maps to trap value 3 -- the same convention as the CUDA
//     sibling's L_CALLSTACK_OVERFLOW and the SPIR-V sibling's %c_TRAP_CALLOF.
//   * Sentinels: 0xCAFE0000|code on clean exit, 0xCAFE007F on any trap,
//     0xDEAD0000 exactly on step-budget exhaustion, 0xCAFE00DB on a DBG-1
//     debug break.
//   * LOG/RECORD ring layout: records start at record_ring_base + 0 with NO
//     head-counter word, i.e. the D2/ref_vm convention. This is the known,
//     filed divergence from A2's gpu_mailbox.MailboxArena -- see
//     doc/08_tracking/bug/svmg_a2_record_ring_head_counter_diverges_from_d2_ref_vm_2026-08-07.md.
//   * DBG-1/PROF-1: restore at launch, breakpoint check BEFORE executing,
//     single-step break AFTER one instruction (unless that instruction
//     already halted), and save-on-every-halt when bit0 is set. `seq` and
//     `record_count` ARE persisted (mailbox_const.spl's "DELIBERATE ADDITION"
//     note) -- without them a resumed launch restarts the RECORD ring at 0 and
//     silently overwrites the records written before the breakpoint.
//
// SINGLE-BUFFER CODE/DATA CO-RESIDENCY: like CUDA's arena_ptr and Vulkan's
// single SSBO, Metal's arena is one MTLBuffer, so code and data are
// co-resident and a STORE into DATA can perturb a not-yet-fetched instruction.
// That is genuine single-buffer device behavior, already filed as
// doc/08_tracking/bug/svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07.md
// (the "mem_store_load_byte" vector). Do NOT "fix" it here -- ref_vm keeps
// code and arena as two separate host arrays, which is what diverges.
//
// Buffer binding: index 0 only -- the 128 KiB GMB-1 arena, bound by
// MetalLaneSession.dispatch_once via rt_metal_set_buffer(encoder, arena, 0, 0).
// The arena is addressed here as a `device uint*` word array with manual
// byte-level shift/mask access (read-modify-write for byte stores), exactly
// like the SPIR-V sibling, so no 8-bit-storage feature is required and the
// unaligned u32 accesses SVM-G's LOAD32/STORE32 permit are expressed
// byte-wise (matching ref_vm's `_u32_le_at`, which is also byte-wise).
//
// Unlike the two siblings, this artifact is checked in as MSL *source text*,
// not a compiled binary: MetalLaneSession.init takes `lane_msl: text` and
// compiles it on-device through rt_metal_compile_shader (there is no offline
// `metal`/`metallib` toolchain on a non-macOS build host, and Metal's runtime
// compiler is the sanctioned path). Its `.sha256` sidecar follows the same
// convention as svmg_cuda_kernel.ptx.sha256 / svmg_vulkan_kernel.spv.sha256.

#include <metal_stdlib>
using namespace metal;

// ---------------------------------------------------------------------------
// GMB-1 arena layout (mailbox_const.spl -- keep byte-identical)
// ---------------------------------------------------------------------------
constant uint ARENA_DATA_SIZE       = 0x10000u;
constant uint RAM_SENTINEL_OFFSET   = 0x08000u;
constant uint LOG_RING_BASE_OFFSET  = 0x10020u;
constant uint LOG_HEAD_OFFSET       = LOG_RING_BASE_OFFSET + 0x00u;
constant uint LOG_CAP_OFFSET        = LOG_RING_BASE_OFFSET + 0x04u;
constant uint LOG_DATA_OFFSET       = LOG_RING_BASE_OFFSET + 0x08u;
constant uint RECORD_SIZE           = 12u;

constant uint SENTINEL_EXIT_MASK    = 0xCAFE0000u;
constant uint SENTINEL_TIMEOUT      = 0xDEAD0000u;
constant uint SENTINEL_DEBUG_BREAK  = 0xCAFE00DBu;

constant uint TRAP_OOB              = 1u;
constant uint TRAP_DIV0             = 2u;
constant uint TRAP_CALLOF           = 3u;
constant uint TRAP_OOB_EXIT_CODE    = 0x7Fu;

// DBG-1 block. Lives at 0x1F000..0x20000 -- ABOVE ARENA_DATA_SIZE, so
// `bounds_ok` makes it unreachable from bytecode LOAD/STORE by construction.
// Do not move it below ARENA_DATA_SIZE: that would let a program scribble on
// its own debugger state.
constant uint DBG_BASE_OFFSET               = 0x1F000u;
constant uint DBG_MAX_BREAKPOINTS           = 16u;
constant uint DBG_FLAGS_OFFSET              = DBG_BASE_OFFSET + 0x000u;
constant uint DBG_BREAK_COUNT_OFFSET        = DBG_BASE_OFFSET + 0x004u;
constant uint DBG_BREAK_PCS_OFFSET          = DBG_BASE_OFFSET + 0x008u;
constant uint DBG_SAVED_PC_OFFSET           = DBG_BASE_OFFSET + 0x048u;
constant uint DBG_SAVED_SP_OFFSET           = DBG_BASE_OFFSET + 0x04Cu;
constant uint DBG_SAVED_CSP_OFFSET          = DBG_BASE_OFFSET + 0x050u;
constant uint DBG_STEP_COUNT_OFFSET         = DBG_BASE_OFFSET + 0x054u;
constant uint DBG_SAVED_STACK_OFFSET        = DBG_BASE_OFFSET + 0x058u;
constant uint DBG_SAVED_CALLS_OFFSET        = DBG_BASE_OFFSET + 0x458u;
constant uint DBG_SAVED_SEQ_OFFSET          = DBG_BASE_OFFSET + 0x4D8u;
constant uint DBG_SAVED_RECORD_COUNT_OFFSET = DBG_BASE_OFFSET + 0x4DCu;

constant uint DBG_FLAG_ENABLED     = 0x1u;
constant uint DBG_FLAG_RESUME      = 0x2u;
constant uint DBG_FLAG_SINGLE_STEP = 0x4u;

constant uint OPERAND_STACK_SIZE = 256u;
constant uint CALL_STACK_SIZE    = 32u;

// ---------------------------------------------------------------------------
// Opcodes (opcodes.spl -- keep byte-identical)
// ---------------------------------------------------------------------------
constant uint OP_NOP=0x00u,  OP_HALT=0x01u, OP_TRAP=0x02u;
constant uint OP_PUSHI=0x10u,OP_PUSHF=0x11u,OP_DUP=0x12u, OP_DROP=0x13u, OP_SWAP=0x14u;
constant uint OP_ADD=0x20u,  OP_SUB=0x21u,  OP_MUL=0x22u, OP_DIV=0x23u,  OP_REM=0x24u;
constant uint OP_FADD=0x28u, OP_FSUB=0x29u, OP_FMUL=0x2Au,OP_FDIV=0x2Bu;
constant uint OP_AND=0x30u,  OP_OR=0x31u,   OP_XOR=0x32u, OP_SHL=0x33u,  OP_SHR=0x34u, OP_SAR=0x35u;
constant uint OP_EQ=0x38u,   OP_NE=0x39u,   OP_LT=0x3Au,  OP_LE=0x3Bu,   OP_GT=0x3Cu,  OP_GE=0x3Du;
constant uint OP_FEQ=0x3Eu,  OP_FNE=0x3Fu,  OP_FLT=0x40u, OP_FLE=0x41u,  OP_FGT=0x42u, OP_FGE=0x43u;
constant uint OP_LOAD32=0x50u, OP_STORE32=0x51u, OP_LOAD8=0x52u, OP_STORE8=0x53u;
constant uint OP_JMP=0x60u,  OP_JZ=0x61u,   OP_JNZ=0x62u;
constant uint OP_CALL=0x68u, OP_RET=0x69u;
constant uint OP_SYS_PUTC=0x70u, OP_SYS_EXIT=0x71u, OP_SYS_RESULT=0x72u;
constant uint OP_TID=0x78u,  OP_NTID=0x79u, OP_PARFOR=0x7Au;

// ---------------------------------------------------------------------------
// Byte-level arena access over a uint32 word array.
// ---------------------------------------------------------------------------
static inline uint a_u8(device uint *arena, uint off) {
    return (arena[off >> 2] >> ((off & 3u) * 8u)) & 0xFFu;
}

static inline void a_w8(device uint *arena, uint off, uint v) {
    uint word = off >> 2;
    uint shift = (off & 3u) * 8u;
    uint mask = 0xFFu << shift;
    arena[word] = (arena[word] & ~mask) | ((v & 0xFFu) << shift);
}

// Byte-wise so unaligned offsets behave exactly like ref_vm's `_u32_le_at`.
static inline uint a_u32(device uint *arena, uint off) {
    return a_u8(arena, off)
         | (a_u8(arena, off + 1u) << 8u)
         | (a_u8(arena, off + 2u) << 16u)
         | (a_u8(arena, off + 3u) << 24u);
}

static inline void a_w32(device uint *arena, uint off, uint v) {
    a_w8(arena, off,      v          & 0xFFu);
    a_w8(arena, off + 1u, (v >> 8u)  & 0xFFu);
    a_w8(arena, off + 2u, (v >> 16u) & 0xFFu);
    a_w8(arena, off + 3u, (v >> 24u) & 0xFFu);
}

static inline uint a_u16(device uint *arena, uint off) {
    return a_u8(arena, off) | (a_u8(arena, off + 1u) << 8u);
}

// Signed 16-bit operand (JMP/JZ/JNZ rel16).
static inline int a_i16(device uint *arena, uint off) {
    uint raw = a_u16(arena, off);
    return (raw >= 0x8000u) ? (int)(raw) - 65536 : (int)(raw);
}

// operand_byte_len(operand_kind_of(opcode)) -- see opcodes.spl. Every opcode
// not listed here takes no operand.
static inline uint operand_len_of(uint opcode) {
    if (opcode == OP_HALT || opcode == OP_TRAP) { return 1u; }
    if (opcode == OP_PUSHI || opcode == OP_PUSHF) { return 4u; }
    if (opcode == OP_JMP || opcode == OP_JZ || opcode == OP_JNZ) { return 2u; }
    if (opcode == OP_CALL || opcode == OP_PARFOR) { return 2u; }
    return 0u;
}

// bounds_ok(offset, width): offset >= 0 and offset + width <= ARENA_DATA_SIZE.
// `offset` arrives as a raw i32 bit pattern, so a negative offset shows up as
// a huge unsigned -- checking the signed value is what makes "offset >= 0"
// real rather than accidentally true.
static inline bool bounds_ok(uint offset_bits, uint width) {
    int off = as_type<int>(offset_bits);
    if (off < 0) { return false; }
    return ((uint)off + width) <= ARENA_DATA_SIZE;
}

// ---------------------------------------------------------------------------
// Interpreter entry point. Single invocation (dispatch 1x1x1, threadgroup
// 1x1x1) -- mirrors the Vulkan lane's local_size_x=1 shape and the CUDA
// lane's single-thread kernel. Any extra thread returns immediately so an
// over-sized dispatch can never double-execute the program.
// ---------------------------------------------------------------------------
kernel void svmg_interpret(device uint *arena [[buffer(0)]],
                           uint gid [[thread_position_in_grid]]) {
    if (gid != 0u) { return; }

    // --- SGP header (sgp.spl: 36 bytes at arena+0, all u32 LE) ---
    uint code_off    = a_u32(arena, 8u);
    uint code_len    = a_u32(arena, 12u);
    uint step_budget = a_u32(arena, 24u);
    uint entry_pc    = a_u32(arena, 28u);

    uint log_cap  = a_u32(arena, LOG_CAP_OFFSET);
    uint rec_base = LOG_DATA_OFFSET + log_cap;

    uint stack[256];
    uint callstack[32];
    for (uint i = 0u; i < OPERAND_STACK_SIZE; i++) { stack[i] = 0u; }
    for (uint i = 0u; i < CALL_STACK_SIZE; i++) { callstack[i] = 0u; }

    uint pc = entry_pc;
    uint sp = 0u;
    uint csp = 0u;
    uint seq = 0u;
    uint record_count = 0u;
    uint steps_remaining = step_budget;
    bool halted = false;

    // --- DBG-1 launch-time restore (ref_vm.SvmgVm.new). Every branch here is
    // skipped when DBG_FLAGS == 0, which is the only state a pre-DBG-1 arena
    // can be in, so the non-debug path is byte-identical to the pre-DBG-1
    // kernel plus one already-computed boolean per iteration. ---
    uint dbg_flags = a_u32(arena, DBG_FLAGS_OFFSET);
    bool dbg_on = (dbg_flags & DBG_FLAG_ENABLED) != 0u;
    bool single_step = dbg_on && ((dbg_flags & DBG_FLAG_SINGLE_STEP) != 0u);
    bool resumed = false;
    uint step_count = 0u;
    uint dbg_break_count = 0u;
    uint dbg_breaks[16];
    for (uint i = 0u; i < DBG_MAX_BREAKPOINTS; i++) { dbg_breaks[i] = 0u; }

    if (dbg_on) {
        dbg_break_count = a_u32(arena, DBG_BREAK_COUNT_OFFSET);
        // ref_vm PANICS when the table is over-full; a device cannot panic,
        // so clamp -- and the host-side `dbg_set_breakpoints` already refuses
        // to install more than DBG_MAX_BREAKPOINTS, so an over-full table can
        // only arrive from a hand-poked arena.
        if (dbg_break_count > DBG_MAX_BREAKPOINTS) { dbg_break_count = DBG_MAX_BREAKPOINTS; }
        for (uint i = 0u; i < dbg_break_count; i++) {
            dbg_breaks[i] = a_u32(arena, DBG_BREAK_PCS_OFFSET + i * 4u);
        }
        step_count = a_u32(arena, DBG_STEP_COUNT_OFFSET);
        if ((dbg_flags & DBG_FLAG_RESUME) != 0u) {
            resumed = true;
            // seq/record_count MUST be restored -- see the header note.
            seq          = a_u32(arena, DBG_SAVED_SEQ_OFFSET);
            record_count = a_u32(arena, DBG_SAVED_RECORD_COUNT_OFFSET);
            pc  = a_u32(arena, DBG_SAVED_PC_OFFSET);
            sp  = a_u32(arena, DBG_SAVED_SP_OFFSET);
            csp = a_u32(arena, DBG_SAVED_CSP_OFFSET);
            for (uint i = 0u; i < OPERAND_STACK_SIZE; i++) {
                stack[i] = a_u32(arena, DBG_SAVED_STACK_OFFSET + i * 4u);
            }
            for (uint i = 0u; i < CALL_STACK_SIZE; i++) {
                callstack[i] = a_u32(arena, DBG_SAVED_CALLS_OFFSET + i * 4u);
            }
        }
    }

    bool trapped = false;
    bool timed_out = false;
    bool debug_break = false;
    bool first_instruction = true;

    while (!halted) {
        if (steps_remaining == 0u) {
            a_w32(arena, RAM_SENTINEL_OFFSET, SENTINEL_TIMEOUT);
            timed_out = true;
            halted = true;
            break;
        }
        if (pc >= code_len) {
            // exit_clean(0)
            a_w32(arena, RAM_SENTINEL_OFFSET, SENTINEL_EXIT_MASK);
            seq++;
            halted = true;
            break;
        }
        if (dbg_on && !(first_instruction && resumed)) {
            bool hit = false;
            for (uint i = 0u; i < dbg_break_count; i++) {
                if (dbg_breaks[i] == pc) { hit = true; }
            }
            if (hit) {
                a_w32(arena, RAM_SENTINEL_OFFSET, SENTINEL_DEBUG_BREAK);
                debug_break = true;
                halted = true;
                break;
            }
        }
        steps_remaining--;

        // ---------------- step() ----------------
        uint opcode  = a_u8(arena, code_off + pc);
        uint oplen   = operand_len_of(opcode);
        uint pc_next = pc + 1u + oplen;
        bool did_trap = false;
        uint trap_value = 0u;

        if (opcode == OP_NOP) {
            pc = pc_next;
        } else if (opcode == OP_HALT) {
            a_w32(arena, RAM_SENTINEL_OFFSET,
                  SENTINEL_EXIT_MASK | (a_u8(arena, code_off + pc + 1u) & 0xFFFFu));
            seq++;
            halted = true;
        } else if (opcode == OP_TRAP) {
            did_trap = true;
            trap_value = a_u8(arena, code_off + pc + 1u);
        } else if (opcode == OP_PUSHI || opcode == OP_PUSHF) {
            stack[sp & 255u] = a_u32(arena, code_off + pc + 1u);
            sp++;
            pc = pc_next;
        } else if (opcode == OP_DUP) {
            uint v = stack[(sp - 1u) & 255u];
            stack[sp & 255u] = v;
            sp++;
            pc = pc_next;
        } else if (opcode == OP_DROP) {
            sp--;
            pc = pc_next;
        } else if (opcode == OP_SWAP) {
            uint y = stack[(sp - 1u) & 255u];
            uint x = stack[(sp - 2u) & 255u];
            stack[(sp - 2u) & 255u] = y;
            stack[(sp - 1u) & 255u] = x;
            pc = pc_next;
        } else if (opcode >= OP_ADD && opcode <= OP_REM) {
            uint b = stack[(sp - 1u) & 255u];
            uint a = stack[(sp - 2u) & 255u];
            sp -= 2u;
            uint r = 0u;
            if (opcode == OP_ADD) {
                r = a + b;                       // uint add wraps == _wrap_i32
            } else if (opcode == OP_SUB) {
                r = a - b;
            } else if (opcode == OP_MUL) {
                r = a * b;
            } else {
                int ia = as_type<int>(a);
                int ib = as_type<int>(b);
                if (ib == 0) {
                    did_trap = true;
                    trap_value = TRAP_DIV0;
                } else if (ia == (-2147483647 - 1) && ib == -1) {
                    // INT_MIN / -1 overflows; ref_vm computes 2147483648 in
                    // i64 then _wrap_i32's it back to INT_MIN, and REM is 0.
                    r = (opcode == OP_DIV) ? 0x80000000u : 0u;
                } else {
                    r = as_type<uint>((opcode == OP_DIV) ? (ia / ib) : (ia % ib));
                }
            }
            if (!did_trap) {
                stack[sp & 255u] = r;
                sp++;
                pc = pc_next;
            }
        } else if (opcode >= OP_FADD && opcode <= OP_FDIV) {
            float b = as_type<float>(stack[(sp - 1u) & 255u]);
            float a = as_type<float>(stack[(sp - 2u) & 255u]);
            sp -= 2u;
            float r = (opcode == OP_FADD) ? (a + b)
                    : (opcode == OP_FSUB) ? (a - b)
                    : (opcode == OP_FMUL) ? (a * b)
                                          : (a / b);
            stack[sp & 255u] = as_type<uint>(r);
            sp++;
            pc = pc_next;
        } else if (opcode >= OP_AND && opcode <= OP_SAR) {
            uint b = stack[(sp - 1u) & 255u];
            uint a = stack[(sp - 2u) & 255u];
            sp -= 2u;
            uint sh = b & 31u;
            uint r = (opcode == OP_AND) ? (a & b)
                   : (opcode == OP_OR)  ? (a | b)
                   : (opcode == OP_XOR) ? (a ^ b)
                   : (opcode == OP_SHL) ? (a << sh)
                   : (opcode == OP_SHR) ? (a >> sh)                       // logical
                                        : as_type<uint>(as_type<int>(a) >> sh); // SAR, arithmetic
            stack[sp & 255u] = r;
            sp++;
            pc = pc_next;
        } else if (opcode >= OP_EQ && opcode <= OP_GE) {
            int b = as_type<int>(stack[(sp - 1u) & 255u]);
            int a = as_type<int>(stack[(sp - 2u) & 255u]);
            sp -= 2u;
            bool c = (opcode == OP_EQ) ? (a == b)
                   : (opcode == OP_NE) ? (a != b)
                   : (opcode == OP_LT) ? (a <  b)
                   : (opcode == OP_LE) ? (a <= b)
                   : (opcode == OP_GT) ? (a >  b)
                                       : (a >= b);
            stack[sp & 255u] = c ? 1u : 0u;
            sp++;
            pc = pc_next;
        } else if (opcode >= OP_FEQ && opcode <= OP_FGE) {
            float b = as_type<float>(stack[(sp - 1u) & 255u]);
            float a = as_type<float>(stack[(sp - 2u) & 255u]);
            sp -= 2u;
            bool c = (opcode == OP_FEQ) ? (a == b)
                   : (opcode == OP_FNE) ? (a != b)
                   : (opcode == OP_FLT) ? (a <  b)
                   : (opcode == OP_FLE) ? (a <= b)
                   : (opcode == OP_FGT) ? (a >  b)
                                        : (a >= b);
            stack[sp & 255u] = c ? 1u : 0u;
            sp++;
            pc = pc_next;
        } else if (opcode == OP_LOAD32) {
            uint offset = stack[(sp - 1u) & 255u];
            sp--;
            if (!bounds_ok(offset, 4u)) {
                did_trap = true;
                trap_value = TRAP_OOB;
            } else {
                stack[sp & 255u] = a_u32(arena, offset);
                sp++;
                pc = pc_next;
            }
        } else if (opcode == OP_STORE32) {
            uint value  = stack[(sp - 1u) & 255u];
            uint offset = stack[(sp - 2u) & 255u];
            sp -= 2u;
            if (!bounds_ok(offset, 4u)) {
                did_trap = true;
                trap_value = TRAP_OOB;
            } else {
                a_w32(arena, offset, value);
                pc = pc_next;
            }
        } else if (opcode == OP_LOAD8) {
            uint offset = stack[(sp - 1u) & 255u];
            sp--;
            if (!bounds_ok(offset, 1u)) {
                did_trap = true;
                trap_value = TRAP_OOB;
            } else {
                stack[sp & 255u] = a_u8(arena, offset);
                sp++;
                pc = pc_next;
            }
        } else if (opcode == OP_STORE8) {
            uint value  = stack[(sp - 1u) & 255u];
            uint offset = stack[(sp - 2u) & 255u];
            sp -= 2u;
            if (!bounds_ok(offset, 1u)) {
                did_trap = true;
                trap_value = TRAP_OOB;
            } else {
                a_w8(arena, offset, value);
                pc = pc_next;
            }
        } else if (opcode == OP_JMP) {
            pc = (uint)((int)pc_next + a_i16(arena, code_off + pc + 1u));
        } else if (opcode == OP_JZ || opcode == OP_JNZ) {
            int rel = a_i16(arena, code_off + pc + 1u);
            uint cond = stack[(sp - 1u) & 255u];
            sp--;
            bool take = (opcode == OP_JZ) ? (cond == 0u) : (cond != 0u);
            pc = take ? (uint)((int)pc_next + rel) : pc_next;
        } else if (opcode == OP_CALL) {
            uint target = a_u16(arena, code_off + pc + 1u);
            if (csp >= CALL_STACK_SIZE) {
                // ref_vm panics here (host/assembler bug); a device maps it to
                // a representable trap -- same as the CUDA/SPIR-V siblings.
                did_trap = true;
                trap_value = TRAP_CALLOF;
            } else {
                callstack[csp] = pc_next;
                csp++;
                pc = target;
            }
        } else if (opcode == OP_RET) {
            if (csp == 0u) {
                a_w32(arena, RAM_SENTINEL_OFFSET, SENTINEL_EXIT_MASK);
                seq++;
                halted = true;
            } else {
                csp--;
                pc = callstack[csp];
            }
        } else if (opcode == OP_SYS_PUTC) {
            uint ch = stack[(sp - 1u) & 255u];
            sp--;
            uint head = a_u32(arena, LOG_HEAD_OFFSET);
            a_w8(arena, LOG_DATA_OFFSET + (head % log_cap), ch);
            a_w32(arena, LOG_HEAD_OFFSET, head + 1u);
            seq++;
            pc = pc_next;
        } else if (opcode == OP_SYS_EXIT) {
            uint code_val = stack[(sp - 1u) & 255u];
            sp--;
            a_w32(arena, RAM_SENTINEL_OFFSET, SENTINEL_EXIT_MASK | (code_val & 0xFFFFu));
            seq++;
            halted = true;
        } else if (opcode == OP_SYS_RESULT) {
            uint value    = stack[(sp - 1u) & 255u];
            uint pass_val = stack[(sp - 2u) & 255u];
            sp -= 2u;
            uint off = rec_base + record_count * RECORD_SIZE;
            a_w32(arena, off,      seq);
            a_w32(arena, off + 4u, pass_val);
            a_w32(arena, off + 8u, value);
            record_count++;
            seq++;
            pc = pc_next;
        } else if (opcode == OP_TID) {
            stack[sp & 255u] = 0u; sp++; pc = pc_next;
        } else if (opcode == OP_NTID) {
            stack[sp & 255u] = 1u; sp++; pc = pc_next;
        } else if (opcode == OP_PARFOR) {
            // Single invocation == the whole workgroup: the fanned region is
            // just the next instructions, executed once as thread 0 (same as
            // ref_vm's single-host-thread treatment).
            pc = pc_next;
        } else {
            // ref_vm panics on an unimplemented opcode. A device cannot; the
            // nearest honest device behavior is a trap, never a silent NOP
            // fallthrough (which would let a corrupt program "succeed").
            did_trap = true;
            trap_value = TRAP_OOB;
        }

        if (did_trap) {
            // trap(): write_record(0, trap_value), sentinel EXIT|0x7F, halt.
            uint off = rec_base + record_count * RECORD_SIZE;
            a_w32(arena, off,      seq);
            a_w32(arena, off + 4u, 0u);
            a_w32(arena, off + 8u, trap_value);
            record_count++;
            seq++;
            a_w32(arena, RAM_SENTINEL_OFFSET, SENTINEL_EXIT_MASK | TRAP_OOB_EXIT_CODE);
            trapped = true;
            halted = true;
        }
        // -------------- end step() --------------

        if (dbg_on) {
            step_count++;
            // Single-step stops AFTER one instruction, but only if that
            // instruction did not already halt the VM (HALT/TRAP/SYS_EXIT):
            // a program that ENDED is not "stopped at a breakpoint", and
            // reporting it as one makes resume-to-completion loop forever.
            if (single_step && !halted) {
                a_w32(arena, RAM_SENTINEL_OFFSET, SENTINEL_DEBUG_BREAK);
                debug_break = true;
                halted = true;
            }
        }
        first_instruction = false;
    }

    if (dbg_on) {
        a_w32(arena, DBG_SAVED_PC_OFFSET, pc);
        a_w32(arena, DBG_SAVED_SP_OFFSET, sp);
        a_w32(arena, DBG_SAVED_CSP_OFFSET, csp);
        a_w32(arena, DBG_STEP_COUNT_OFFSET, step_count);
        a_w32(arena, DBG_SAVED_SEQ_OFFSET, seq);
        a_w32(arena, DBG_SAVED_RECORD_COUNT_OFFSET, record_count);
        for (uint i = 0u; i < OPERAND_STACK_SIZE; i++) {
            a_w32(arena, DBG_SAVED_STACK_OFFSET + i * 4u, stack[i]);
        }
        for (uint i = 0u; i < CALL_STACK_SIZE; i++) {
            a_w32(arena, DBG_SAVED_CALLS_OFFSET + i * 4u, callstack[i]);
        }
    }

    // `trapped`/`timed_out`/`debug_break` are not written anywhere beyond the
    // sentinel: the host decodes all three from RAM_SENTINEL (see
    // metal_vm_executor.spl's `_decode_sentinel` / `debug_break_of`), exactly
    // like the CUDA and Vulkan lanes.
    (void)trapped; (void)timed_out; (void)debug_break;
}
