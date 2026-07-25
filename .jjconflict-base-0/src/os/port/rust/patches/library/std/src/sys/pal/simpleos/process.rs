//! No `fork`/`exec` on SimpleOS yet — every entry point returns Unsupported.

use crate::ffi::OsStr;
use crate::fmt;
use crate::io;
use crate::num::NonZero;
use crate::path::Path;
use crate::sys::pal::simpleos::pipe::AnonPipe;

pub use crate::ffi::OsString as EnvKey;

pub struct Command {
    program: crate::ffi::OsString,
}

#[rustfmt::skip]
impl Command {
    pub fn new(program: &OsStr) -> Command {
        Command { program: program.to_os_string() }
    }
    pub fn arg(&mut self, _a: &OsStr)             {}
    pub fn env_mut(&mut self) -> &mut CommandEnv  { &mut DUMMY_ENV }
    pub fn cwd(&mut self, _dir: &OsStr)           {}
    pub fn stdin(&mut self, _s: Stdio)            {}
    pub fn stdout(&mut self, _s: Stdio)           {}
    pub fn stderr(&mut self, _s: Stdio)           {}
    pub fn get_program(&self) -> &OsStr           { &self.program }
    pub fn get_args(&self) -> CommandArgs<'_>     { CommandArgs { _p: core::marker::PhantomData } }
    pub fn get_envs(&self) -> CommandEnvs<'_>     { CommandEnvs { _p: core::marker::PhantomData } }
    pub fn get_current_dir(&self) -> Option<&Path> { None }

    pub fn spawn(&mut self, _d: Stdio, _s: bool) -> io::Result<(Process, StdioPipes)> {
        Err(io::Error::from(io::ErrorKind::Unsupported))
    }
    pub fn output(&mut self) -> io::Result<(ExitStatus, Vec<u8>, Vec<u8>)> {
        Err(io::Error::from(io::ErrorKind::Unsupported))
    }
}

impl fmt::Debug for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Command").field("program", &self.program).finish()
    }
}

pub struct CommandEnv;
static mut DUMMY_ENV: CommandEnv = CommandEnv;

pub struct CommandArgs<'a> { _p: core::marker::PhantomData<&'a ()> }
pub struct CommandEnvs<'a> { _p: core::marker::PhantomData<&'a ()> }

#[rustfmt::skip]
impl<'a> Iterator for CommandArgs<'a> {
    type Item = &'a OsStr;
    fn next(&mut self) -> Option<Self::Item> { None }
}
#[rustfmt::skip]
impl<'a> Iterator for CommandEnvs<'a> {
    type Item = (&'a OsStr, Option<&'a OsStr>);
    fn next(&mut self) -> Option<Self::Item> { None }
}

pub struct StdioPipes {
    pub stdin: Option<AnonPipe>,
    pub stdout: Option<AnonPipe>,
    pub stderr: Option<AnonPipe>,
}

pub enum Stdio { Inherit, Null, MakePipe }

pub struct Process(!);

#[rustfmt::skip]
impl Process {
    pub fn id(&self) -> u32                              { self.0 }
    pub fn kill(&mut self) -> io::Result<()>             { self.0 }
    pub fn wait(&mut self) -> io::Result<ExitStatus>     { self.0 }
    pub fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> { self.0 }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct ExitStatus(i32);

#[rustfmt::skip]
impl ExitStatus {
    pub fn exit_ok(&self) -> Result<(), ExitStatusError> {
        NonZero::new(self.0).map(ExitStatusError).map_or(Ok(()), Err)
    }
    pub fn code(&self) -> Option<i32> { Some(self.0) }
}

impl fmt::Display for ExitStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "exit code: {}", self.0)
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct ExitStatusError(NonZero<i32>);

#[rustfmt::skip]
impl Into<ExitStatus> for ExitStatusError {
    fn into(self) -> ExitStatus { ExitStatus(self.0.get()) }
}
#[rustfmt::skip]
impl ExitStatusError {
    pub fn code(self) -> Option<NonZero<i32>> { Some(self.0) }
}

pub struct ExitCode(u8);

#[rustfmt::skip]
impl ExitCode {
    pub const SUCCESS: ExitCode = ExitCode(0);
    pub const FAILURE: ExitCode = ExitCode(1);
    pub fn as_i32(&self) -> i32 { self.0 as i32 }
}
#[rustfmt::skip]
impl From<u8> for ExitCode {
    fn from(b: u8) -> Self { ExitCode(b) }
}
