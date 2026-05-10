//! Target spec for `x86_64-unknown-simpleos`.
//!
//! Mirrors `src/os/toolchain/rust/x86_64-unknown-simpleos.json` from the
//! Simple tree. Keep this file in sync with that JSON — they must not drift.

use crate::spec::{
    Cc, CodeModel, LinkSelfContainedDefault, LinkerFlavor, Lld, PanicStrategy, RelocModel,
    StackProbeType, Target, TargetMetadata, TargetOptions,
};

pub(crate) fn target() -> Target {
    let options = TargetOptions {
        os: "simpleos".into(),
        env: "".into(),
        vendor: "unknown".into(),
        linker_flavor: LinkerFlavor::Gnu(Cc::Yes, Lld::Yes),
        linker: Some("clang".into()),
        executables: true,
        has_thread_local: false,
        panic_strategy: PanicStrategy::Abort,
        disable_redzone: true,
        dynamic_linking: false,
        position_independent_executables: false,
        static_position_independent_executables: false,
        relocation_model: RelocModel::Static,
        code_model: Some(CodeModel::Kernel),
        crt_static_default: true,
        crt_static_respected: true,
        singlethread: true,
        max_atomic_width: Some(64),
        features: "-mmx,-sse,-sse2,-sse3,-ssse3,-sse4.1,-sse4.2,-avx,-avx2,+soft-float".into(),
        stack_probes: StackProbeType::None,
        eh_frame_header: false,
        emit_debug_gdb_scripts: false,
        exe_suffix: "".into(),
        pre_link_args: TargetOptions::link_args(
            LinkerFlavor::Gnu(Cc::Yes, Lld::Yes),
            &[
                "-target",
                "x86_64-unknown-none-elf",
                "-nostdlib",
                "-static",
                "-ffreestanding",
                "-fuse-ld=lld",
                "-T",
                "simpleos.ld",
                "crt0.o",
            ],
        ),
        late_link_args: TargetOptions::link_args(
            LinkerFlavor::Gnu(Cc::Yes, Lld::Yes),
            &["-lsimpleos_c"],
        ),
        link_self_contained: LinkSelfContainedDefault::with_linker(),
        ..Default::default()
    };

    Target {
        llvm_target: "x86_64-unknown-none-elf".into(),
        metadata: TargetMetadata {
            description: Some("SimpleOS (x86_64, static ELF, libsimpleos_c)".into()),
            tier: Some(3),
            host_tools: Some(false),
            std: Some(false),
        },
        pointer_width: 64,
        data_layout:
            "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128".into(),
        arch: "x86_64".into(),
        options,
    }
}
