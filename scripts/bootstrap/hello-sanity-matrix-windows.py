"""Native Windows aggregate memory containment for the common matrix owner.

Each command also runs under the repository's existing bounded Windows Job
collector for wall time, log limits and descendant cleanup. No launcher for the
tested program is synthesized here.
"""


def install_memory_budget(max_bytes):
    import ctypes as ct
    from ctypes import wintypes as wt

    if ct.sizeof(ct.c_void_p) != 8:
        raise RuntimeError("matrix memory containment requires native 64-bit Python")

    class BasicLimit(ct.Structure):
        _fields_ = [("process_time", ct.c_longlong), ("job_time", ct.c_longlong),
                    ("flags", wt.DWORD), ("min_working", ct.c_size_t),
                    ("max_working", ct.c_size_t), ("active_limit", wt.DWORD),
                    ("affinity", ct.c_size_t), ("priority", wt.DWORD),
                    ("scheduling", wt.DWORD)]

    class ExtendedLimit(ct.Structure):
        _fields_ = [("basic", BasicLimit), ("io", ct.c_ulonglong * 6),
                    ("process_memory", ct.c_size_t), ("job_memory", ct.c_size_t),
                    ("peak_process_memory", ct.c_size_t), ("peak_job_memory", ct.c_size_t)]

    kernel = ct.WinDLL("kernel32", use_last_error=True)
    create = kernel.CreateJobObjectW
    create.argtypes = [ct.c_void_p, wt.LPCWSTR]
    create.restype = wt.HANDLE
    configure = kernel.SetInformationJobObject
    configure.argtypes = [wt.HANDLE, ct.c_int, ct.c_void_p, wt.DWORD]
    configure.restype = wt.BOOL
    assign = kernel.AssignProcessToJobObject
    assign.argtypes = [wt.HANDLE, wt.HANDLE]
    assign.restype = wt.BOOL
    current = kernel.GetCurrentProcess
    current.argtypes = []
    current.restype = wt.HANDLE
    close = kernel.CloseHandle
    close.argtypes = [wt.HANDLE]
    close.restype = wt.BOOL
    job = create(None, None)
    if not job:
        raise ct.WinError(ct.get_last_error())
    limits = ExtendedLimit()
    limits.basic.flags = 0x2000 | 0x200  # kill-on-close; aggregate job memory.
    limits.job_memory = max_bytes
    if not configure(job, 9, ct.byref(limits), ct.sizeof(limits)):
        error = ct.get_last_error()
        close(job)
        raise ct.WinError(error)
    if not assign(job, current()):
        error = ct.get_last_error()
        close(job)
        raise RuntimeError("Windows parent does not permit nested Job containment: " + str(ct.WinError(error)))
    # The process owns the handle until exit. Closing it while this process is
    # still assigned would kill the owner before final evidence is flushed.
    return job
