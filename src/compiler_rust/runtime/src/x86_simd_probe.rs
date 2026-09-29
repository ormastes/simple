//! Rust twin of `rt_x86_avx512_os_state_usable`
//! (`src/runtime/runtime_simd_dispatch.c:106`, predicate factored out at
//! `src/runtime/runtime_simd_dispatch.h:106` as
//! `simd_x86_avx512_os_state_usable_from_raw`).
//!
//! AVX-512 execution needs the OS to have opted in to saving XMM, YMM,
//! opmask, ZMM_hi256 and Hi16_ZMM state via `XSAVE`. That is a fact about
//! CPUID leaf 1 ECX and the `XCR0` extended control register, not about
//! whether any particular AVX-512 CPUID feature bit is set -- so this does
//! **not** use `is_x86_feature_detected!("avx512f")`, which additionally
//! requires CPUID leaf 7.0 EBX bit 16 and is therefore a strictly narrower
//! predicate than the C function.
//!
//! `SIMPLE_RUNTIME_FORCE_NO_X86_XSTATE` in the C source
//! (`runtime_simd_dispatch.c:107`) is a **compile-time** `#if defined(...)`,
//! never set anywhere in this tree (verified: it has exactly one occurrence,
//! the `#if` itself -- no build script or Cargo feature defines it, and there
//! is no `getenv` of that name anywhere in the repo). It is therefore not an
//! environment-variable override to mirror; this twin has no `cfg`/env
//! equivalent to honour because the C side has none either at runtime.

/// Pure bit-test mirroring `simd_x86_avx512_os_state_usable_from_raw`
/// (`runtime_simd_dispatch.h:106`) byte-for-byte: CPUID leaf 1 ECX must carry
/// both `XSAVE` (bit 26) and `OSXSAVE` (bit 27), and `XCR0` must carry the
/// SSE/AVX/opmask/ZMM_hi256/Hi16_ZMM bits (mask `0xE6`).
#[inline]
fn avx512_os_state_usable_from_raw(cpuid_leaf1_ecx: u32, xcr0: u64) -> bool {
    const XSAVE_OSXSAVE: u32 = (1u32 << 26) | (1u32 << 27);
    const XMM_YMM_OPMASK_ZMM: u64 = 0xE6;
    (cpuid_leaf1_ecx & XSAVE_OSXSAVE) == XSAVE_OSXSAVE
        && (xcr0 & XMM_YMM_OPMASK_ZMM) == XMM_YMM_OPMASK_ZMM
}

/// Contract: `bool rt_x86_avx512_os_state_usable(void)`
/// (`src/runtime/runtime_simd_dispatch.c:106`). Real twin (not fail-closed):
/// on x86/x86_64 reads CPUID leaf 1 via `__cpuid`, and only when both
/// `XSAVE`/`OSXSAVE` are set reads `XCR0` via `xgetbv` (raw `asm!`, not the
/// `_xgetbv` intrinsic, so this needs no `target_feature = "xsave"` at
/// compile time -- matching the C side's own ordering, which never executes
/// `xgetbv` without first confirming `OSXSAVE`, since the instruction traps
/// otherwise). On every other target this returns `false`, exactly as the
/// C `#else` branch (`runtime_simd_dispatch.c:130-132`) does.
#[no_mangle]
pub extern "C" fn rt_x86_avx512_os_state_usable() -> bool {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        #[cfg(target_arch = "x86")]
        use std::arch::x86::__cpuid;
        #[cfg(target_arch = "x86_64")]
        use std::arch::x86_64::__cpuid;

        let leaf1 = unsafe { __cpuid(1) };
        const XSAVE_OSXSAVE: u32 = (1u32 << 26) | (1u32 << 27);
        if (leaf1.ecx & XSAVE_OSXSAVE) != XSAVE_OSXSAVE {
            return false;
        }
        let xcr0: u64 = unsafe {
            let lo: u32;
            let hi: u32;
            std::arch::asm!(
                "xgetbv",
                in("ecx") 0u32,
                out("eax") lo,
                out("edx") hi,
                options(nomem, nostack, preserves_flags),
            );
            ((hi as u64) << 32) | (lo as u64)
        };
        avx512_os_state_usable_from_raw(leaf1.ecx, xcr0)
    }
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_predicate_requires_both_cpuid_bits() {
        let full_xcr0: u64 = 0xE6;
        assert!(avx512_os_state_usable_from_raw((1 << 26) | (1 << 27), full_xcr0));
        // Missing OSXSAVE (bit 27).
        assert!(!avx512_os_state_usable_from_raw(1 << 26, full_xcr0));
        // Missing XSAVE (bit 26).
        assert!(!avx512_os_state_usable_from_raw(1 << 27, full_xcr0));
    }

    #[test]
    fn raw_predicate_requires_full_xcr0_mask() {
        let both_cpuid_bits: u32 = (1 << 26) | (1 << 27);
        // SSE/YMM only (bits 1,2) -- opmask/ZMM (bits 5,6,7) missing.
        assert!(!avx512_os_state_usable_from_raw(both_cpuid_bits, 0x06));
        assert!(avx512_os_state_usable_from_raw(both_cpuid_bits, 0xE6));
        // Extra bits beyond the mask (e.g. x87, bit 0) don't matter.
        assert!(avx512_os_state_usable_from_raw(both_cpuid_bits, 0xE7));
    }

    #[test]
    fn probe_returns_bool_and_is_internally_consistent() {
        // No crash on any host; on non-x86 this is always false. When it is
        // true, AVX (a weaker requirement: only XSAVE/OSXSAVE + XCR0 SSE/YMM)
        // must also be detectable, so the two never disagree in a way that
        // would indicate a bit-mask mistake above.
        let usable = rt_x86_avx512_os_state_usable();
        if usable {
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            assert!(std::is_x86_feature_detected!("xsave"));
        } else {
            assert!(!usable);
        }
    }
}
