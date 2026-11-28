//! Privilege drop + privilege-dropping spawn: Rust twin of
//! `src/runtime/runtime_privdrop_v1.c`. The ABI, step codes, drop order and
//! verification are identical; see `src/runtime/runtime_privdrop_v1.h`.
//!
//! Every fallible call returns `>= 0` or `-(step * 65536 + errno)`.
//! Handles are owner tokens (`Box::into_raw`), freed exactly once.

pub const STEP_INVALID: i64 = 1;
pub const STEP_LOOKUP: i64 = 2;
pub const STEP_SETSID: i64 = 3;
pub const STEP_CGROUP_OPEN: i64 = 4;
pub const STEP_CGROUP_WRITE: i64 = 5;
pub const STEP_SETGROUPS: i64 = 6;
pub const STEP_SETGID: i64 = 7;
pub const STEP_SETUID: i64 = 8;
pub const STEP_VERIFY: i64 = 9;
pub const STEP_EXEC: i64 = 10;
pub const STEP_FORK: i64 = 11;
pub const STEP_PIPE: i64 = 12;
pub const STEP_NOMEM: i64 = 13;
pub const STEP_UNSUPPORTED: i64 = 14;
pub const STEP_FDS: i64 = 15;
pub const STEP_WAIT: i64 = 16;

#[inline]
pub const fn err(step: i64, errno: i64) -> i64 {
    -((step << 16) + errno)
}

#[cfg(any(target_os = "linux", target_os = "freebsd"))]
mod imp {
    use super::*;
    use std::ffi::CString;
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// Upper bound for the per-signal reset in the child: covers Linux (64)
    /// and FreeBSD (128); numbers the host does not have are skipped.
    const NSIG: libc::c_int = 129;

    const CRED_MAGIC: u64 = 0x5052_4956_4352_4544;
    const SPAWN_MAGIC: u64 = 0x5052_4956_5350_4e57;
    const MAX_GROUPS: usize = 4096;
    const MAX_ITEMS: usize = 65536;
    const EINVAL: i64 = libc::EINVAL as i64;

    #[derive(Clone)]
    pub struct Cred {
        magic: u64,
        uid: libc::uid_t,
        gid: libc::gid_t,
        groups: Vec<libc::gid_t>,
    }

    pub struct Spawn {
        magic: u64,
        path: CString,
        argv: Vec<CString>,
        envp: Vec<CString>,
        cred: Option<Cred>,
        new_session: bool,
        procs: Option<(libc::c_int, CString)>,
    }

    fn errno() -> i64 {
        std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO) as i64
    }

    // Live-handle registry: a handle is dereferenced only while registered,
    // so forged, stale or double-freed integers are refused. Lockless (CAS).
    const LIVE_SLOTS: usize = 256;
    // One registry per handle kind: a credential handle is never live as a spawn.
    static LIVE_CRED: [AtomicUsize; LIVE_SLOTS] = [const { AtomicUsize::new(0) }; LIVE_SLOTS];
    static LIVE_SPAWN: [AtomicUsize; LIVE_SLOTS] = [const { AtomicUsize::new(0) }; LIVE_SLOTS];

    fn register(live: &[AtomicUsize], p: usize) -> bool {
        live.iter().any(|s| s.compare_exchange(0, p, Ordering::SeqCst, Ordering::SeqCst).is_ok())
    }

    fn is_live(live: &[AtomicUsize], h: i64) -> bool {
        h > 0 && live.iter().any(|s| s.load(Ordering::SeqCst) == h as usize)
    }

    /// Unregister before free; only the caller that wins the CAS may free.
    fn unregister(live: &[AtomicUsize], p: usize) -> bool {
        live.iter().any(|s| s.compare_exchange(p, 0, Ordering::SeqCst, Ordering::SeqCst).is_ok())
    }

    unsafe fn cred_ref<'a>(h: i64) -> Option<&'a mut Cred> {
        if !is_live(&LIVE_CRED, h) {
            return None;
        }
        let c = &mut *(h as *mut Cred);
        (c.magic == CRED_MAGIC).then_some(c)
    }

    unsafe fn spawn_ref<'a>(h: i64) -> Option<&'a mut Spawn> {
        if !is_live(&LIVE_SPAWN, h) {
            return None;
        }
        let s = &mut *(h as *mut Spawn);
        (s.magic == SPAWN_MAGIC).then_some(s)
    }

    /// NUL-free owned copy of a byte span.
    unsafe fn cstr(p: *const u8, n: u64) -> Option<CString> {
        if n > 65536 || (p.is_null() && n != 0) {
            return None;
        }
        let bytes = if n == 0 { &[][..] } else { std::slice::from_raw_parts(p, n as usize) };
        CString::new(bytes).ok()
    }

    pub fn cred_new(uid: i64, gid: i64) -> i64 {
        if uid <= 0 || gid <= 0 || uid > 0x7fff_ffff || gid > 0x7fff_ffff {
            return err(STEP_INVALID, EINVAL);
        }
        let c = Box::new(Cred { magic: CRED_MAGIC, uid: uid as libc::uid_t, gid: gid as libc::gid_t, groups: Vec::new() });
        let p = Box::into_raw(c);
        if !register(&LIVE_CRED, p as usize) {
            // SAFETY: p came from Box::into_raw above and was never shared.
            drop(unsafe { Box::from_raw(p) });
            return err(STEP_NOMEM, libc::EMFILE as i64);
        }
        p as i64
    }

    pub unsafe fn cred_from_user(name: *const u8, len: u64) -> i64 {
        let user = match cstr(name, len) {
            Some(u) if !u.as_bytes().is_empty() => u,
            _ => return err(STEP_INVALID, EINVAL),
        };
        let mut pw: libc::passwd = std::mem::zeroed();
        let mut found: *mut libc::passwd = std::ptr::null_mut();
        let mut buf = vec![0 as libc::c_char; 16384];
        let rc = libc::getpwnam_r(user.as_ptr(), &mut pw, buf.as_mut_ptr(), buf.len(), &mut found);
        if rc != 0 || found.is_null() {
            return err(STEP_LOOKUP, if rc != 0 { rc as i64 } else { libc::ENOENT as i64 });
        }
        let h = cred_new(pw.pw_uid as i64, pw.pw_gid as i64);
        if h < 0 {
            return h;
        }
        let c = cred_ref(h).unwrap();
        let mut groups = vec![0 as libc::gid_t; MAX_GROUPS];
        let mut n = MAX_GROUPS as libc::c_int;
        if libc::getgrouplist(user.as_ptr(), pw.pw_gid as _, groups.as_mut_ptr() as *mut _, &mut n) < 0 {
            cred_free(h);
            return err(STEP_LOOKUP, libc::E2BIG as i64);
        }
        groups.truncate(n as usize);
        c.groups = groups;
        h
    }

    pub unsafe fn cred_add_group(h: i64, gid: i64) -> i64 {
        let Some(c) = cred_ref(h) else { return err(STEP_INVALID, EINVAL) };
        if !(0..=0x7fff_ffff).contains(&gid) {
            return err(STEP_INVALID, EINVAL);
        }
        if c.groups.len() >= MAX_GROUPS {
            return err(STEP_INVALID, libc::E2BIG as i64);
        }
        c.groups.push(gid as libc::gid_t);
        0
    }

    pub unsafe fn cred_uid(h: i64) -> i64 {
        cred_ref(h).map_or(err(STEP_INVALID, EINVAL), |c| c.uid as i64)
    }
    pub unsafe fn cred_gid(h: i64) -> i64 {
        cred_ref(h).map_or(err(STEP_INVALID, EINVAL), |c| c.gid as i64)
    }
    pub unsafe fn cred_group_count(h: i64) -> i64 {
        cred_ref(h).map_or(err(STEP_INVALID, EINVAL), |c| c.groups.len() as i64)
    }
    pub unsafe fn cred_group_at(h: i64, i: i64) -> i64 {
        match cred_ref(h) {
            Some(c) if i >= 0 && (i as usize) < c.groups.len() => c.groups[i as usize] as i64,
            _ => err(STEP_INVALID, EINVAL),
        }
    }
    pub unsafe fn cred_free(h: i64) -> i64 {
        let Some(c) = cred_ref(h) else { return err(STEP_INVALID, EINVAL) };
        if !unregister(&LIVE_CRED, h as usize) {
            return err(STEP_INVALID, EINVAL);
        }
        c.magic = 0;
        drop(Box::from_raw(c as *mut Cred));
        0
    }

    /// The fixed drop sequence; async-signal-safe (no allocation), so it is
    /// also the forked child's sequence.
    unsafe fn apply(c: &Cred) -> i64 {
        if libc::setgroups(c.groups.len() as _, c.groups.as_ptr()) != 0 {
            return err(STEP_SETGROUPS, errno());
        }
        if libc::setresgid(c.gid, c.gid, c.gid) != 0 {
            return err(STEP_SETGID, errno());
        }
        if libc::setresuid(c.uid, c.uid, c.uid) != 0 {
            return err(STEP_SETUID, errno());
        }
        let (mut ru, mut eu, mut su) = (0, 0, 0);
        let (mut rg, mut eg, mut sg) = (0, 0, 0);
        if libc::getresuid(&mut ru, &mut eu, &mut su) != 0 || libc::getresgid(&mut rg, &mut eg, &mut sg) != 0 {
            return err(STEP_VERIFY, errno());
        }
        if [ru, eu, su] != [c.uid; 3] || [rg, eg, sg] != [c.gid; 3] {
            return err(STEP_VERIFY, libc::EPERM as i64);
        }
        let mut now = [0 as libc::gid_t; MAX_GROUPS];
        let n = libc::getgroups(MAX_GROUPS as libc::c_int, now.as_mut_ptr());
        if n < 0 {
            return err(STEP_VERIFY, errno());
        }
        let now = &now[..n as usize];
        // Set equality modulo the primary gid (Linux sorts; FreeBSD < 14 keeps egid in slot 0).
        if !now.iter().all(|g| *g == c.gid || c.groups.contains(g)) || !c.groups.iter().all(|g| now.contains(g)) {
            return err(STEP_VERIFY, libc::EPERM as i64);
        }
        if libc::setresuid(0, 0, 0) == 0 || libc::setresgid(0, 0, 0) == 0 || libc::setuid(0) == 0 {
            return err(STEP_VERIFY, libc::EPERM as i64);
        }
        0
    }

    pub unsafe fn cred_drop_self(h: i64) -> i64 {
        match cred_ref(h) {
            Some(c) => apply(c),
            None => err(STEP_INVALID, EINVAL),
        }
    }

    pub unsafe fn spawn_new(p: *const u8, n: u64) -> i64 {
        let Some(path) = cstr(p, n) else { return err(STEP_INVALID, EINVAL) };
        if path.as_bytes().first() != Some(&b'/') {
            return err(STEP_INVALID, EINVAL);
        }
        let s = Box::new(Spawn {
            magic: SPAWN_MAGIC,
            argv: vec![path.clone()],
            path,
            envp: Vec::new(),
            cred: None,
            new_session: false,
            procs: None,
        });
        let p = Box::into_raw(s);
        if !register(&LIVE_SPAWN, p as usize) {
            drop(Box::from_raw(p));
            return err(STEP_NOMEM, libc::EMFILE as i64);
        }
        p as i64
    }

    pub unsafe fn spawn_arg(h: i64, p: *const u8, n: u64) -> i64 {
        let Some(s) = spawn_ref(h) else { return err(STEP_INVALID, EINVAL) };
        if s.argv.len() >= MAX_ITEMS {
            return err(STEP_INVALID, libc::E2BIG as i64);
        }
        match cstr(p, n) {
            Some(a) => {
                s.argv.push(a);
                0
            }
            None => err(STEP_INVALID, EINVAL),
        }
    }

    pub unsafe fn spawn_env(h: i64, p: *const u8, n: u64) -> i64 {
        let Some(s) = spawn_ref(h) else { return err(STEP_INVALID, EINVAL) };
        if s.envp.len() >= MAX_ITEMS {
            return err(STEP_INVALID, libc::E2BIG as i64);
        }
        match cstr(p, n) {
            Some(e) if e.as_bytes().first() != Some(&b'=') && e.as_bytes().contains(&b'=') => {
                s.envp.push(e);
                0
            }
            _ => err(STEP_INVALID, EINVAL),
        }
    }

    pub unsafe fn spawn_cred(h: i64, c: i64) -> i64 {
        match (spawn_ref(h), cred_ref(c)) {
            (Some(s), Some(c)) => {
                s.cred = Some(c.clone()); // copied: never aliases the caller's handle
                0
            }
            _ => err(STEP_INVALID, EINVAL),
        }
    }

    pub unsafe fn spawn_join_procs(h: i64, dir_fd: i64, p: *const u8, n: u64) -> i64 {
        let Some(s) = spawn_ref(h) else { return err(STEP_INVALID, EINVAL) };
        if !(0..=0x7fff_ffff).contains(&dir_fd) {
            return err(STEP_INVALID, EINVAL);
        }
        match cstr(p, n) {
            Some(leaf) if !leaf.as_bytes().is_empty() && !leaf.as_bytes().contains(&b'/') && leaf.as_bytes() != b"." && leaf.as_bytes() != b".." => {
                s.procs = Some((dir_fd as libc::c_int, leaf));
                0
            }
            _ => err(STEP_INVALID, EINVAL),
        }
    }

    pub unsafe fn spawn_new_session(h: i64) -> i64 {
        match spawn_ref(h) {
            Some(s) => {
                s.new_session = true;
                0
            }
            None => err(STEP_INVALID, EINVAL),
        }
    }

    unsafe fn report(fd: libc::c_int, code: i64) -> ! {
        let bytes = code.to_ne_bytes();
        let mut off = 0usize;
        while off < bytes.len() {
            let w = libc::write(fd, bytes.as_ptr().add(off) as *const _, bytes.len() - off);
            if w < 0 && *errno_location() == libc::EINTR {
                continue;
            }
            if w <= 0 {
                break;
            }
            off += w as usize;
        }
        libc::_exit(127)
    }

    #[cfg(target_os = "linux")]
    unsafe fn errno_location() -> *mut libc::c_int {
        libc::__errno_location()
    }
    #[cfg(target_os = "freebsd")]
    unsafe fn errno_location() -> *mut libc::c_int {
        libc::__error()
    }
    fn raw_errno() -> i64 {
        unsafe { *errno_location() as i64 }
    }

    unsafe fn cloexec_from3() -> libc::c_int {
        #[cfg(target_os = "linux")]
        {
            if libc::syscall(libc::SYS_close_range, 3u32, !0u32, 4u32 /* CLOSE_RANGE_CLOEXEC */) == 0 {
                return 0;
            }
        }
        let mut max = libc::sysconf(libc::_SC_OPEN_MAX);
        if !(0..=1_048_576).contains(&max) {
            max = 1_048_576;
        }
        for fd in 3..max as libc::c_int {
            let flags = libc::fcntl(fd, libc::F_GETFD);
            if flags >= 0 && libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC) != 0 {
                return -1;
            }
        }
        0
    }

    pub unsafe fn spawn_run(h: i64) -> i64 {
        let Some(s) = spawn_ref(h) else { return err(STEP_INVALID, EINVAL) };
        let Some(cred) = s.cred.as_ref() else { return err(STEP_INVALID, EINVAL) };
        // Everything the child touches is prepared before fork.
        let mut argv: Vec<*const libc::c_char> = s.argv.iter().map(|a| a.as_ptr()).collect();
        argv.push(std::ptr::null());
        let mut envp: Vec<*const libc::c_char> = s.envp.iter().map(|e| e.as_ptr()).collect();
        envp.push(std::ptr::null());
        let mut fds = [0 as libc::c_int; 2];
        if libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) != 0 {
            return err(STEP_PIPE, errno());
        }
        // Block every signal across fork so no parent handler can run in the
        // still-privileged child before its dispositions are reset.
        let mut all: libc::sigset_t = std::mem::zeroed();
        let mut saved: libc::sigset_t = std::mem::zeroed();
        libc::sigfillset(&mut all);
        libc::pthread_sigmask(libc::SIG_SETMASK, &all, &mut saved);
        let pid = libc::fork();
        if pid < 0 {
            let e = errno();
            libc::pthread_sigmask(libc::SIG_SETMASK, &saved, std::ptr::null_mut());
            libc::close(fds[0]);
            libc::close(fds[1]);
            return err(STEP_FORK, e);
        }
        if pid == 0 {
            // Child: async-signal-safe calls only, in the fixed order. Reset
            // every caught handler (and SIGPIPE) to default, then unblock.
            for sig in 1..NSIG {
                if sig == libc::SIGKILL || sig == libc::SIGSTOP {
                    continue;
                }
                let mut old: libc::sigaction = std::mem::zeroed();
                if libc::sigaction(sig, std::ptr::null(), &mut old) != 0 {
                    continue;
                }
                if sig == libc::SIGPIPE || (old.sa_sigaction != libc::SIG_IGN && old.sa_sigaction != libc::SIG_DFL) {
                    let mut dfl: libc::sigaction = std::mem::zeroed();
                    dfl.sa_sigaction = libc::SIG_DFL;
                    libc::sigemptyset(&mut dfl.sa_mask);
                    libc::sigaction(sig, &dfl, std::ptr::null_mut());
                }
            }
            let mut none: libc::sigset_t = std::mem::zeroed();
            libc::sigemptyset(&mut none);
            libc::sigprocmask(libc::SIG_SETMASK, &none, std::ptr::null_mut());
            if s.new_session && libc::setsid() < 0 {
                report(fds[1], err(STEP_SETSID, raw_errno()));
            }
            if let Some((dir_fd, leaf)) = s.procs.as_ref() {
                let fd = libc::openat(*dir_fd, leaf.as_ptr(), libc::O_WRONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NOCTTY);
                if fd < 0 {
                    report(fds[1], err(STEP_CGROUP_OPEN, raw_errno()));
                }
                let mut rev = [0u8; 24];
                let mut digits = [0u8; 24];
                let mut len = 0usize;
                let mut v = libc::getpid() as i64;
                loop {
                    rev[len] = b'0' + (v % 10) as u8;
                    len += 1;
                    v /= 10;
                    if v == 0 {
                        break;
                    }
                }
                for i in 0..len {
                    digits[i] = rev[len - 1 - i];
                }
                let w = libc::write(fd, digits.as_ptr() as *const _, len);
                let e = raw_errno();
                libc::close(fd);
                if w != len as isize {
                    report(fds[1], err(STEP_CGROUP_WRITE, if w < 0 { e } else { libc::EIO as i64 }));
                }
            }
            if cloexec_from3() != 0 {
                report(fds[1], err(STEP_FDS, raw_errno()));
            }
            let drop_rc = apply(cred);
            if drop_rc != 0 {
                report(fds[1], drop_rc);
            }
            libc::execve(s.path.as_ptr(), argv.as_ptr(), envp.as_ptr());
            report(fds[1], err(STEP_EXEC, raw_errno()));
        }
        libc::pthread_sigmask(libc::SIG_SETMASK, &saved, std::ptr::null_mut());
        libc::close(fds[1]);
        let mut buf = [0u8; 8];
        let mut got = 0usize;
        while got < 8 {
            let r = libc::read(fds[0], buf.as_mut_ptr().add(got) as *mut _, 8 - got);
            if r < 0 && raw_errno() == libc::EINTR as i64 {
                continue;
            }
            if r <= 0 {
                break;
            }
            got += r as usize;
        }
        libc::close(fds[0]);
        if got == 0 {
            return pid as i64; // exec succeeded: pipe closed by CLOEXEC
        }
        let mut status = 0;
        while libc::waitpid(pid, &mut status, 0) < 0 && raw_errno() == libc::EINTR as i64 {}
        let code = i64::from_ne_bytes(buf);
        if got == 8 && code < 0 {
            code
        } else {
            err(STEP_EXEC, libc::EIO as i64)
        }
    }

    pub unsafe fn spawn_free(h: i64) -> i64 {
        let Some(s) = spawn_ref(h) else { return err(STEP_INVALID, EINVAL) };
        if !unregister(&LIVE_SPAWN, h as usize) {
            return err(STEP_INVALID, EINVAL);
        }
        s.magic = 0;
        drop(Box::from_raw(s as *mut Spawn));
        0
    }

    pub fn spawn_wait(pid: i64) -> i64 {
        if pid <= 0 || pid > 0x7fff_ffff {
            return err(STEP_INVALID, EINVAL);
        }
        let mut status: libc::c_int = 0;
        loop {
            let r = unsafe { libc::waitpid(pid as libc::pid_t, &mut status, 0) };
            if r as i64 == pid {
                return status as u32 as i64;
            }
            if r < 0 && raw_errno() == libc::EINTR as i64 {
                continue;
            }
            return err(STEP_WAIT, if r < 0 { raw_errno() } else { libc::ECHILD as i64 });
        }
    }
}

#[cfg(not(any(target_os = "linux", target_os = "freebsd")))]
mod imp {
    use super::*;
    const U: i64 = -(STEP_UNSUPPORTED << 16);
    pub fn cred_new(_: i64, _: i64) -> i64 { U }
    pub unsafe fn cred_from_user(_: *const u8, _: u64) -> i64 { U }
    pub unsafe fn cred_add_group(_: i64, _: i64) -> i64 { U }
    pub unsafe fn cred_uid(_: i64) -> i64 { U }
    pub unsafe fn cred_gid(_: i64) -> i64 { U }
    pub unsafe fn cred_group_count(_: i64) -> i64 { U }
    pub unsafe fn cred_group_at(_: i64, _: i64) -> i64 { U }
    pub unsafe fn cred_drop_self(_: i64) -> i64 { U }
    pub unsafe fn cred_free(_: i64) -> i64 { U }
    pub unsafe fn spawn_new(_: *const u8, _: u64) -> i64 { U }
    pub unsafe fn spawn_arg(_: i64, _: *const u8, _: u64) -> i64 { U }
    pub unsafe fn spawn_env(_: i64, _: *const u8, _: u64) -> i64 { U }
    pub unsafe fn spawn_cred(_: i64, _: i64) -> i64 { U }
    pub unsafe fn spawn_join_procs(_: i64, _: i64, _: *const u8, _: u64) -> i64 { U }
    pub unsafe fn spawn_new_session(_: i64) -> i64 { U }
    pub unsafe fn spawn_run(_: i64) -> i64 { U }
    pub unsafe fn spawn_free(_: i64) -> i64 { U }
    pub fn spawn_wait(_: i64) -> i64 { U }
}

#[no_mangle]
pub extern "C" fn rt_privcred_new_v1(uid: i64, gid: i64) -> i64 {
    imp::cred_new(uid, gid)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privcred_from_user_v1(name: *const u8, len: u64) -> i64 {
    imp::cred_from_user(name, len)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privcred_add_group_v1(cred: i64, gid: i64) -> i64 {
    imp::cred_add_group(cred, gid)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privcred_uid_v1(cred: i64) -> i64 {
    imp::cred_uid(cred)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privcred_gid_v1(cred: i64) -> i64 {
    imp::cred_gid(cred)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privcred_group_count_v1(cred: i64) -> i64 {
    imp::cred_group_count(cred)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privcred_group_at_v1(cred: i64, index: i64) -> i64 {
    imp::cred_group_at(cred, index)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privcred_drop_self_v1(cred: i64) -> i64 {
    imp::cred_drop_self(cred)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privcred_free_v1(cred: i64) -> i64 {
    imp::cred_free(cred)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privspawn_new_v1(path: *const u8, len: u64) -> i64 {
    imp::spawn_new(path, len)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privspawn_arg_v1(spawn: i64, arg: *const u8, len: u64) -> i64 {
    imp::spawn_arg(spawn, arg, len)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privspawn_env_v1(spawn: i64, entry: *const u8, len: u64) -> i64 {
    imp::spawn_env(spawn, entry, len)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privspawn_cred_v1(spawn: i64, cred: i64) -> i64 {
    imp::spawn_cred(spawn, cred)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privspawn_join_procs_v1(spawn: i64, dir_fd: i64, name: *const u8, len: u64) -> i64 {
    imp::spawn_join_procs(spawn, dir_fd, name, len)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privspawn_new_session_v1(spawn: i64) -> i64 {
    imp::spawn_new_session(spawn)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privspawn_run_v1(spawn: i64) -> i64 {
    imp::spawn_run(spawn)
}
#[no_mangle]
pub unsafe extern "C" fn rt_privspawn_free_v1(spawn: i64) -> i64 {
    imp::spawn_free(spawn)
}
#[no_mangle]
pub extern "C" fn rt_privspawn_wait_v1(pid: i64) -> i64 {
    imp::spawn_wait(pid)
}


#[cfg(all(test, any(target_os = "linux", target_os = "freebsd")))]
mod tests {
    use super::*;

    #[test]
    fn rejects_root_target_and_bad_handles() {
        assert_eq!(rt_privcred_new_v1(0, 0), err(STEP_INVALID, libc::EINVAL as i64));
        unsafe {
            assert_eq!(rt_privcred_drop_self_v1(0), err(STEP_INVALID, libc::EINVAL as i64));
            assert_eq!(rt_privspawn_new_v1(b"rel".as_ptr(), 3), err(STEP_INVALID, libc::EINVAL as i64));
        }
        // a root *group* target can never pass the "root unrecoverable" check
        assert_eq!(rt_privcred_new_v1(65534, 0), err(STEP_INVALID, libc::EINVAL as i64));
    }

    #[test]
    fn forged_stale_and_double_freed_handles_are_refused_not_dereferenced() {
        let inval = err(STEP_INVALID, libc::EINVAL as i64);
        let local = 7u64;
        let forged = &local as *const u64 as i64; // a real address that is not a handle
        unsafe {
            assert_eq!(rt_privcred_uid_v1(forged), inval);
            assert_eq!(rt_privspawn_run_v1(forged), inval);
            assert_eq!(rt_privcred_free_v1(forged), inval);
            let c = rt_privcred_new_v1(65534, 65534);
            assert!(c > 0);
            // a credential handle is not accepted where a spawn handle is expected
            assert_eq!(rt_privspawn_free_v1(c), inval);
            assert_eq!(rt_privcred_free_v1(c), 0);
            assert_eq!(rt_privcred_uid_v1(c), inval); // stale
            assert_eq!(rt_privcred_free_v1(c), inval); // double free
        }
    }

    #[test]
    fn non_root_drop_is_refused_at_setgroups() {
        if unsafe { libc::geteuid() } == 0 {
            return; // the root path is covered by the spec run under root
        }
        let c = rt_privcred_new_v1(65534, 65534);
        assert!(c > 0);
        unsafe {
            assert_eq!(rt_privcred_drop_self_v1(c), err(STEP_SETGROUPS, libc::EPERM as i64));
            assert_eq!(rt_privcred_free_v1(c), 0);
        }
    }

    #[test]
    fn join_procs_rejects_multi_component_names() {
        unsafe {
            let s = rt_privspawn_new_v1(b"/bin/true".as_ptr(), 9);
            assert!(s > 0);
            assert!(rt_privspawn_join_procs_v1(s, 3, b"a/b".as_ptr(), 3) < 0);
            assert!(rt_privspawn_join_procs_v1(s, 3, b"..".as_ptr(), 2) < 0);
            assert_eq!(rt_privspawn_join_procs_v1(s, 3, b"cgroup.procs".as_ptr(), 12), 0);
            assert_eq!(rt_privspawn_free_v1(s), 0);
        }
    }
}

#[cfg(all(test, not(any(target_os = "linux", target_os = "freebsd"))))]
mod unsupported_tests {
    use super::*;

    #[test]
    fn every_entry_point_is_typed_unsupported() {
        let u = -(STEP_UNSUPPORTED << 16);
        assert_eq!(rt_privcred_new_v1(65534, 65534), u);
        unsafe {
            assert_eq!(rt_privcred_from_user_v1(b"nobody".as_ptr(), 6), u);
            assert_eq!(rt_privcred_drop_self_v1(1), u);
            assert_eq!(rt_privspawn_new_v1(b"/bin/true".as_ptr(), 9), u);
            assert_eq!(rt_privspawn_run_v1(1), u);
        }
    }
}
