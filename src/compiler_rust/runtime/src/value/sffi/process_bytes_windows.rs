//! Job ownership for strict byte capture. A child cannot execute before it
//! belongs to the job; closing the job also closes descendant pipe writers.
use std::os::windows::{io::AsRawHandle, process::CommandExt};
use windows::Win32::Foundation::{CloseHandle, HANDLE};
use windows::Win32::System::Diagnostics::ToolHelp::{
    CreateToolhelp32Snapshot, Thread32First, Thread32Next, THREADENTRY32, TH32CS_SNAPTHREAD,
};
use windows::Win32::System::JobObjects::{
    AssignProcessToJobObject, CreateJobObjectW, SetInformationJobObject,
    TerminateJobObject, JobObjectExtendedLimitInformation, JOBOBJECT_EXTENDED_LIMIT_INFORMATION,
    JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE,
};
use windows::Win32::System::Threading::{OpenThread, ResumeThread, CREATE_SUSPENDED, THREAD_SUSPEND_RESUME};

pub(super) struct CaptureJob(HANDLE);

impl CaptureJob {
    pub(super) fn terminate(&self) -> std::io::Result<()> {
        unsafe { TerminateJobObject(self.0, 1).map_err(std::io::Error::other) }
    }
}

impl Drop for CaptureJob {
    fn drop(&mut self) {
        unsafe {
            let _ = TerminateJobObject(self.0, 1);
            let _ = CloseHandle(self.0);
        }
    }
}

unsafe fn resume_primary(pid: u32) -> std::io::Result<()> {
    let snapshot = CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0).map_err(std::io::Error::other)?;
    let mut entry = THREADENTRY32 { dwSize: std::mem::size_of::<THREADENTRY32>() as u32, ..Default::default() };
    let mut found = Thread32First(snapshot, &mut entry).is_ok();
    let mut result = Err(std::io::Error::other("suspended child thread not found"));
    while found {
        if entry.th32OwnerProcessID == pid {
            result = match OpenThread(THREAD_SUSPEND_RESUME, false, entry.th32ThreadID) {
                Ok(thread) => {
                    let count = ResumeThread(thread);
                    let error = std::io::Error::last_os_error();
                    let _ = CloseHandle(thread);
                    if count == u32::MAX { Err(error) } else { Ok(()) }
                }
                Err(error) => Err(std::io::Error::other(error)),
            };
            break;
        }
        found = Thread32Next(snapshot, &mut entry).is_ok();
    }
    let _ = CloseHandle(snapshot);
    result
}

pub(super) fn spawn(command: &mut std::process::Command) -> std::io::Result<(std::process::Child, CaptureJob)> {
    unsafe {
        let job = CaptureJob(CreateJobObjectW(None, None).map_err(std::io::Error::other)?);
        let mut limits = JOBOBJECT_EXTENDED_LIMIT_INFORMATION::default();
        limits.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
        SetInformationJobObject(job.0, JobObjectExtendedLimitInformation,
            &limits as *const _ as _, std::mem::size_of_val(&limits) as u32).map_err(std::io::Error::other)?;
        command.creation_flags(CREATE_SUSPENDED.0);
        let mut child = command.spawn()?;
        let admitted = AssignProcessToJobObject(job.0, HANDLE(child.as_raw_handle() as _))
            .map_err(std::io::Error::other)
            .and_then(|_| resume_primary(child.id()));
        if let Err(error) = admitted {
            let _ = child.kill();
            let _ = child.wait();
            return Err(error);
        }
        Ok((child, job))
    }
}
