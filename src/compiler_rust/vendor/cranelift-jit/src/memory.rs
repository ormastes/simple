use cranelift_module::{ModuleError, ModuleResult};

#[cfg(all(not(target_os = "windows"), feature = "selinux-fix"))]
use memmap2::MmapMut;

#[cfg(not(any(feature = "selinux-fix", windows)))]
use std::alloc;
use std::ffi::c_void;
use std::io;
use std::mem;
use std::ptr;
use wasmtime_jit_icache_coherence as icache_coherence;

/// A simple struct consisting of a pointer and length.
struct PtrLen {
    #[cfg(all(not(target_os = "windows"), feature = "selinux-fix"))]
    map: Option<MmapMut>,

    ptr: *mut u8,
    len: usize,

    /// True when `ptr` points into the shared AArch64 code arena below rather
    /// than into memory obtained from the process allocator. Such a chunk must
    /// never be handed to `dealloc`.
    from_arena: bool,
}

impl PtrLen {
    /// Create a new empty `PtrLen`.
    fn new() -> Self {
        Self {
            #[cfg(all(not(target_os = "windows"), feature = "selinux-fix"))]
            map: None,

            ptr: ptr::null_mut(),
            len: 0,
            from_arena: false,
        }
    }

    /// Create a new `PtrLen` pointing to at least `size` bytes of memory,
    /// suitably sized and aligned for memory protection.
    #[cfg(all(not(target_os = "windows"), feature = "selinux-fix"))]
    fn with_size(size: usize) -> io::Result<Self> {
        let alloc_size = region::page::ceil(size as *const ()) as usize;
        MmapMut::map_anon(alloc_size).map(|mut mmap| {
            // The order here is important; we assign the pointer first to get
            // around compile time borrow errors.
            Self {
                ptr: mmap.as_mut_ptr(),
                map: Some(mmap),
                len: alloc_size,
                from_arena: false,
            }
        })
    }

    #[cfg(all(not(target_os = "windows"), not(feature = "selinux-fix")))]
    fn with_size(size: usize) -> io::Result<Self> {
        assert_ne!(size, 0);
        let page_size = region::page::size();
        let alloc_size = region::page::ceil(size as *const ()) as usize;
        let layout = alloc::Layout::from_size_align(alloc_size, page_size).unwrap();
        // Safety: We assert that the size is non-zero above.
        let ptr = unsafe { alloc::alloc(layout) };

        if !ptr.is_null() {
            Ok(Self {
                ptr,
                len: alloc_size,
                from_arena: false,
            })
        } else {
            Err(io::Error::from(io::ErrorKind::OutOfMemory))
        }
    }

    #[cfg(target_os = "windows")]
    fn with_size(size: usize) -> io::Result<Self> {
        use windows_sys::Win32::System::Memory::{
            VirtualAlloc, MEM_COMMIT, MEM_RESERVE, PAGE_READWRITE,
        };

        // VirtualAlloc always rounds up to the next multiple of the page size
        let ptr = unsafe {
            VirtualAlloc(
                ptr::null_mut(),
                size,
                MEM_COMMIT | MEM_RESERVE,
                PAGE_READWRITE,
            )
        };
        if !ptr.is_null() {
            Ok(Self {
                ptr: ptr as *mut u8,
                len: region::page::ceil(size as *const ()) as usize,
                from_arena: false,
            })
        } else {
            Err(io::Error::last_os_error())
        }
    }
}

// `MMapMut` from `cfg(feature = "selinux-fix")` already deallocates properly.
#[cfg(all(not(target_os = "windows"), not(feature = "selinux-fix")))]
impl Drop for PtrLen {
    fn drop(&mut self) {
        // Arena-backed chunks are carved out of one big `mmap`; they are not
        // owned by the process allocator and are deliberately leaked with the
        // arena so that already-published function pointers stay valid.
        if !self.ptr.is_null() && !self.from_arena {
            let page_size = region::page::size();
            let layout = alloc::Layout::from_size_align(self.len, page_size).unwrap();
            unsafe {
                region::protect(self.ptr, self.len, region::Protection::READ_WRITE)
                    .expect("unable to unprotect memory");
                alloc::dealloc(self.ptr, layout)
            }
        }
    }
}

// TODO: add a `Drop` impl for `cfg(target_os = "windows")`

// ---------------------------------------------------------------------------
// AArch64 far-call support  (LOCAL PATCH to vendored cranelift-jit)
//
// WHY:
//   On AArch64 a direct `bl` (`Reloc::Arm64Call`) encodes a *26-bit signed word*
//   displacement, i.e. a reach of only +/-128 MiB. Upstream cranelift-jit hands
//   out JIT code pages from the process allocator (`alloc::alloc` above), which
//   mixes brk-heap and mmap'd blocks; on this host those routinely land
//   gigabytes apart, so two functions of the *same* JIT module could not reach
//   each other. Symptoms, both observed:
//     * `assert!((diff >> 26 == -1) || (diff >> 26 == 0))` in compiled_blob.rs
//       aborting `JITModule::finalize_definitions`, and
//     * a plain SIGSEGV in JIT code, because that assert is one bit too loose
//       (it admits +/-256 MiB) so a displacement in the 128..256 MiB band was
//       silently truncated into a wrong branch target. compiled_blob.rs now
//       checks the true limit; this module makes the situation not arise.
//   See doc/08_tracking/bug/jit_aarch64_branch_relocation_out_of_range_abort_2026-09-05.md
//
// FIX:
//   Back the *code* `Memory` of each `JITModule` with a single contiguous
//   reservation of exactly 2^27 bytes -- exactly the reach of a `bl`, so *any*
//   two addresses inside it are within range of each other by construction.
//   Veneers (long-branch thunks, as a real linker emits) are carved downwards
//   from the top of the same arena and cover the residual case of a colocated
//   target that lives outside the arena.
//
//   Cap: 128 MiB of JIT code per JITModule. The reservation is lazy, PROT_NONE
//   in effect until touched (MAP_NORESERVE), so an unused module costs only
//   address space. If a module exceeds the cap the allocator falls back to the
//   old heap path and the pre-existing hazard returns -- but with an explicit
//   warning and, in compiled_blob.rs, a descriptive panic instead of a bare
//   assert. `SIMPLE_JIT_ARENA_STATS=1` prints the high-water mark.
//
//   This is a local patch: upstream cranelift-jit's allocator has no notion of
//   branch reach. The right upstream change is the same one (a contiguous
//   per-module code region) plus the compiled_blob.rs range-check fix, and both
//   should be proposed there rather than carried here forever.
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", target_os = "linux", not(feature = "selinux-fix")))]
pub(crate) const CODE_ARENA_ENABLED: bool = true;
#[cfg(not(all(target_arch = "aarch64", target_os = "linux", not(feature = "selinux-fix"))))]
pub(crate) const CODE_ARENA_ENABLED: bool = false;

#[cfg(all(target_arch = "aarch64", target_os = "linux", not(feature = "selinux-fix")))]
pub(crate) mod aarch64_arena {
    use std::ffi::c_void;
    use std::io;
    use std::ptr;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Mutex, OnceLock};
    use wasmtime_jit_icache_coherence as icache_coherence;

    /// Exactly the byte reach of an AArch64 `bl`/`b`: any two addresses inside a
    /// region this size differ by at most 2^27 - 4, which fits the 26-bit signed
    /// word immediate.
    const ARENA_SIZE: usize = 1 << 27;
    /// Minimum chunk handed back to `Memory`, so that many small functions share
    /// one chunk instead of burning a whole page each.
    const MIN_CHUNK: usize = 64 * 1024;
    /// `ldr x16, #8 ; br x16 ; .quad target`
    const VENEER_SIZE: usize = 16;

    fn page_size() -> usize {
        region::page::size()
    }
    fn align_up(v: usize, a: usize) -> usize {
        (v + a - 1) & !(a - 1)
    }
    fn align_down(v: usize, a: usize) -> usize {
        v & !(a - 1)
    }

    struct Arena {
        base: usize,
        size: usize,
        /// code bump, offset from `base`, grows up
        low: usize,
        /// veneer bump, offset from `base`, grows down
        high: usize,
    }

    impl Arena {
        fn new() -> io::Result<Self> {
            let size = ARENA_SIZE;
            let p = unsafe {
                libc::mmap(
                    ptr::null_mut(),
                    size,
                    libc::PROT_READ | libc::PROT_WRITE,
                    libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
                    -1,
                    0,
                )
            };
            if p == libc::MAP_FAILED {
                return Err(io::Error::last_os_error());
            }
            Ok(Self {
                base: p as usize,
                size,
                low: 0,
                high: size,
            })
        }

        fn contains(&self, p: usize) -> bool {
            p >= self.base && p < self.base + self.size
        }

        /// Returns the chunk pointer *and* its true length; the caller must not
        /// recompute the length, or the two can desync and `Memory` would hand
        /// out bytes belonging to the next chunk.
        fn alloc_code(&mut self, want: usize) -> Option<(*mut u8, usize)> {
            let ps = page_size();
            let len = align_up(want.max(MIN_CHUNK), ps);
            let start = align_up(self.low, ps);
            if start.checked_add(len)? > align_down(self.high, ps) {
                return None;
            }
            self.low = start + len;
            Some(((self.base + start) as *mut u8, len))
        }

        fn alloc_veneer(&mut self) -> Option<*mut u8> {
            let ps = page_size();
            let new_high = align_down(self.high.checked_sub(VENEER_SIZE)?, VENEER_SIZE);
            if new_high < align_up(self.low, ps) {
                return None;
            }
            self.high = new_high;
            Some((self.base + new_high) as *mut u8)
        }

        /// Make every veneer written so far executable. Called from
        /// `Memory::set_readable_and_executable`, i.e. after relocations.
        fn publish_veneers(&mut self) {
            if self.high >= self.size {
                return;
            }
            let ps = page_size();
            let start = align_down(self.high, ps);
            let len = self.size - start;
            let p = (self.base + start) as *const u8;
            unsafe {
                icache_coherence::clear_cache(p as *const c_void, len)
                    .expect("failed to clear icache for JIT far-call veneers");
                region::protect(p, len, region::Protection::READ_EXECUTE)
                    .expect("unable to make JIT far-call veneers readable+executable");
            }
            icache_coherence::pipeline_flush_mt().expect("failed pipeline flush");
            // Never write into a page that has already been published: a later
            // `finalize_definitions` may add veneers while another thread is
            // executing one from this page, and un-protecting it back to R+W
            // would fault that thread. Snapping the bump pointer down to the
            // page boundary costs at most one page per round and keeps every
            // published veneer permanently R+X, matching how the code chunks
            // above are treated.
            self.high = start;
        }
    }

    // `Arena` stores addresses as `usize`, so it is `Send` without an unsafe impl.
    static ARENAS: Mutex<Vec<Arena>> = Mutex::new(Vec::new());
    static WARNED: AtomicBool = AtomicBool::new(false);

    fn warn_once(msg: &str) {
        if !WARNED.swap(true, Ordering::Relaxed) {
            log::warn!("{msg}");
            eprintln!("cranelift-jit: {msg}");
        }
    }

    pub(crate) fn new_arena() -> Option<usize> {
        match Arena::new() {
            Ok(a) => {
                let mut g = ARENAS.lock().unwrap();
                g.push(a);
                Some(g.len() - 1)
            }
            Err(e) => {
                warn_once(&format!(
                    "could not reserve the 128 MiB AArch64 JIT code arena ({e}); \
                     falling back to the heap allocator, where a direct `bl` between \
                     two JIT functions may be out of its +/-128 MiB range"
                ));
                None
            }
        }
    }

    pub(crate) fn alloc_code(idx: usize, want: usize) -> Option<(*mut u8, usize)> {
        let r = ARENAS.lock().unwrap().get_mut(idx)?.alloc_code(want);
        if r.is_none() {
            warn_once(
                "AArch64 JIT code arena exhausted (cap: 128 MiB of code per JIT module); \
                 falling back to the heap allocator, where a direct `bl` between two JIT \
                 functions may be out of its +/-128 MiB range",
            );
        }
        r
    }

    pub(crate) fn publish_veneers(idx: usize) {
        if let Some(a) = ARENAS.lock().unwrap().get_mut(idx) {
            a.publish_veneers();
            if stats_enabled() {
                eprintln!(
                    "cranelift-jit: arena[{idx}] code high-water {} KiB, veneers {} B, cap {} KiB",
                    a.low / 1024,
                    a.size - a.high,
                    a.size / 1024
                );
            }
        }
    }

    fn stats_enabled() -> bool {
        static S: OnceLock<bool> = OnceLock::new();
        *S.get_or_init(|| match std::env::var_os("SIMPLE_JIT_ARENA_STATS") {
            Some(v) => v != "0",
            None => false,
        })
    }

    /// Debug knob: route *every* `Reloc::Arm64Call` through a veneer, so the
    /// veneer path is exercised by ordinary runs instead of only by the rare
    /// out-of-range case.
    pub(crate) fn force_veneers() -> bool {
        static F: OnceLock<bool> = OnceLock::new();
        *F.get_or_init(|| match std::env::var_os("SIMPLE_JIT_FORCE_VENEERS") {
            Some(v) => v != "0",
            None => false,
        })
    }

    /// Allocate a long-branch veneer inside the same arena as the call site `at`
    /// and point it at `target`. Returns the veneer address, which is always
    /// within `bl` range of `at` because both live in the same 128 MiB arena.
    ///
    /// The veneer is the standard PLT-shaped thunk:
    ///     ldr x16, #8      ; load the 64-bit target that follows
    ///     br  x16          ; BTI-safe: `br x16` may land on a `bti c` pad
    ///     .quad target
    pub(crate) fn install_far_call_veneer(at: *const u8, target: *const u8) -> Option<*const u8> {
        let mut g = ARENAS.lock().unwrap();
        let arena = g.iter_mut().find(|a| a.contains(at as usize))?;
        let v = arena.alloc_veneer()?;
        unsafe {
            (v as *mut u32).write_unaligned(0x5800_0050); // ldr x16, #8
            (v.add(4) as *mut u32).write_unaligned(0xd61f_0200); // br x16
            (v.add(8) as *mut u64).write_unaligned(target as u64);
        }
        Some(v as *const u8)
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", not(feature = "selinux-fix")))]
pub(crate) use aarch64_arena::{force_veneers, install_far_call_veneer};

/// No-op stubs on targets whose direct-call relocation has enough reach (or that
/// do not use `Reloc::Arm64Call` at all).
#[cfg(not(all(target_arch = "aarch64", target_os = "linux", not(feature = "selinux-fix"))))]
pub(crate) fn install_far_call_veneer(_at: *const u8, _target: *const u8) -> Option<*const u8> {
    None
}
#[cfg(not(all(target_arch = "aarch64", target_os = "linux", not(feature = "selinux-fix"))))]
pub(crate) fn force_veneers() -> bool {
    false
}

/// Type of branch protection to apply to executable memory.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum BranchProtection {
    /// No protection.
    None,
    /// Use the Branch Target Identification extension of the Arm architecture.
    BTI,
}

/// JIT memory manager. This manages pages of suitably aligned and
/// accessible memory. Memory will be leaked by default to have
/// function pointers remain valid for the remainder of the
/// program's life.
pub(crate) struct Memory {
    allocations: Vec<PtrLen>,
    already_protected: usize,
    current: PtrLen,
    position: usize,
    branch_protection: BranchProtection,

    /// Index into the AArch64 code-arena registry; `Some` once this `Memory`
    /// has reserved one. Only the *code* `Memory` of a `JITModule` uses an
    /// arena -- data has no branch-reach constraint.
    #[allow(dead_code)]
    arena: Option<usize>,
    #[allow(dead_code)]
    use_arena: bool,
}

unsafe impl Send for Memory {}

impl Memory {
    pub(crate) fn new(branch_protection: BranchProtection) -> Self {
        Self {
            allocations: Vec::new(),
            already_protected: 0,
            current: PtrLen::new(),
            position: 0,
            branch_protection,
            arena: None,
            use_arena: false,
        }
    }

    /// Same as `new`, but for the region that holds executable code: on AArch64
    /// its chunks are carved out of one contiguous 128 MiB arena so that every
    /// direct `bl` between two functions of this module is in range. See the
    /// `aarch64_arena` comment block above.
    pub(crate) fn new_code(branch_protection: BranchProtection) -> Self {
        let mut m = Self::new(branch_protection);
        m.use_arena = CODE_ARENA_ENABLED;
        m
    }

    fn new_chunk(&mut self, size: usize) -> io::Result<PtrLen> {
        #[cfg(all(
            target_arch = "aarch64",
            target_os = "linux",
            not(feature = "selinux-fix")
        ))]
        {
            if self.use_arena {
                if self.arena.is_none() {
                    self.arena = aarch64_arena::new_arena();
                    if self.arena.is_none() {
                        self.use_arena = false;
                    }
                }
                if let Some(idx) = self.arena {
                    let want = region::page::ceil(size as *const ()) as usize;
                    if let Some((ptr, len)) = aarch64_arena::alloc_code(idx, want) {
                        return Ok(PtrLen {
                            ptr,
                            len,
                            from_arena: true,
                        });
                    }
                    // Arena exhausted: fall through to the heap allocator. The
                    // warning was already emitted by `alloc_code`.
                    self.use_arena = false;
                }
            }
        }
        PtrLen::with_size(size)
    }

    fn finish_current(&mut self) {
        self.allocations
            .push(mem::replace(&mut self.current, PtrLen::new()));
        self.position = 0;
    }

    pub(crate) fn allocate(&mut self, size: usize, align: u64) -> io::Result<*mut u8> {
        let align = usize::try_from(align).expect("alignment too big");
        if self.position % align != 0 {
            self.position += align - self.position % align;
            debug_assert!(self.position % align == 0);
        }

        if size <= self.current.len - self.position {
            // TODO: Ensure overflow is not possible.
            let ptr = unsafe { self.current.ptr.add(self.position) };
            self.position += size;
            return Ok(ptr);
        }

        self.finish_current();

        // TODO: Allocate more at a time.
        self.current = self.new_chunk(size)?;
        self.position = size;

        Ok(self.current.ptr)
    }

    /// Set all memory allocated in this `Memory` up to now as readable and executable.
    pub(crate) fn set_readable_and_executable(&mut self) -> ModuleResult<()> {
        self.finish_current();

        // Clear all the newly allocated code from cache if the processor requires it
        //
        // Do this before marking the memory as R+X, technically we should be able to do it after
        // but there are some CPU's that have had errata about doing this with read only memory.
        for &PtrLen { ptr, len, .. } in self.non_protected_allocations_iter() {
            unsafe {
                icache_coherence::clear_cache(ptr as *const c_void, len)
                    .expect("Failed cache clear")
            };
        }

        let set_region_readable_and_executable = |ptr, len| -> ModuleResult<()> {
            if self.branch_protection == BranchProtection::BTI {
                #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
                if std::arch::is_aarch64_feature_detected!("bti") {
                    let prot = libc::PROT_EXEC | libc::PROT_READ | /* PROT_BTI */ 0x10;

                    unsafe {
                        if libc::mprotect(ptr as *mut libc::c_void, len, prot) < 0 {
                            return Err(ModuleError::Backend(
                                anyhow::Error::new(io::Error::last_os_error())
                                    .context("unable to make memory readable+executable"),
                            ));
                        }
                    }

                    return Ok(());
                }
            }

            unsafe {
                region::protect(ptr, len, region::Protection::READ_EXECUTE).map_err(|e| {
                    ModuleError::Backend(
                        anyhow::Error::new(e).context("unable to make memory readable+executable"),
                    )
                })?;
            }
            Ok(())
        };

        for &PtrLen { ptr, len, .. } in self.non_protected_allocations_iter() {
            set_region_readable_and_executable(ptr, len)?;
        }

        // Flush any in-flight instructions from the pipeline
        icache_coherence::pipeline_flush_mt().expect("Failed pipeline flush");

        // Long-branch veneers live at the top of the same arena and are written
        // during relocation, i.e. just before this call; publish them too.
        #[cfg(all(
            target_arch = "aarch64",
            target_os = "linux",
            not(feature = "selinux-fix")
        ))]
        if let Some(idx) = self.arena {
            aarch64_arena::publish_veneers(idx);
        }

        self.already_protected = self.allocations.len();
        Ok(())
    }

    /// Set all memory allocated in this `Memory` up to now as readonly.
    pub(crate) fn set_readonly(&mut self) -> ModuleResult<()> {
        self.finish_current();

        for &PtrLen { ptr, len, .. } in self.non_protected_allocations_iter() {
            unsafe {
                region::protect(ptr, len, region::Protection::READ).map_err(|e| {
                    ModuleError::Backend(
                        anyhow::Error::new(e).context("unable to make memory readonly"),
                    )
                })?;
            }
        }

        self.already_protected = self.allocations.len();
        Ok(())
    }

    /// Iterates non protected memory allocations that are of not zero bytes in size.
    fn non_protected_allocations_iter(&self) -> impl Iterator<Item = &PtrLen> {
        let iter = self.allocations[self.already_protected..].iter();

        #[cfg(all(not(target_os = "windows"), feature = "selinux-fix"))]
        return iter.filter(|&PtrLen { ref map, len, .. }| *len != 0 && map.is_some());

        #[cfg(any(target_os = "windows", not(feature = "selinux-fix")))]
        return iter.filter(|&PtrLen { len, .. }| *len != 0);
    }

    /// Frees all allocated memory regions that would be leaked otherwise.
    /// Likely to invalidate existing function pointers, causing unsafety.
    pub(crate) unsafe fn free_memory(&mut self) {
        self.allocations.clear();
        self.already_protected = 0;
    }
}

impl Drop for Memory {
    fn drop(&mut self) {
        // leak memory to guarantee validity of function pointers
        mem::replace(&mut self.allocations, Vec::new())
            .into_iter()
            .for_each(mem::forget);
    }
}
