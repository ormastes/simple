#![deny(unsafe_op_in_unsafe_fn)]

use core::ffi::c_void;
use core::marker::PhantomData;
use core::mem::size_of;
use core::ptr::{null, null_mut};

pub const ABI_V1: u32 = 1;
pub const PLUGIN_ENTRY_V1: &str = "simple_kpf_plugin_v1";

pub type StatusCode = i32;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(i32)]
pub enum Status {
    Ok = 0,
    Pending = 1,
    WouldBlock = 2,
    NeedMore = 3,
    Cancelled = 4,
    DeadlineExceeded = 5,
    CapacityExceeded = 6,
    Rejected = 7,
    StaleHandle = 8,
    InvalidArgument = 9,
    Failed = 10,
}

impl Status {
    pub fn from_code(code: StatusCode) -> Result<Self, StatusCode> {
        match code {
            0 => Ok(Self::Ok),
            1 => Ok(Self::Pending),
            2 => Ok(Self::WouldBlock),
            3 => Ok(Self::NeedMore),
            4 => Ok(Self::Cancelled),
            5 => Ok(Self::DeadlineExceeded),
            6 => Ok(Self::CapacityExceeded),
            7 => Ok(Self::Rejected),
            8 => Ok(Self::StaleHandle),
            9 => Ok(Self::InvalidArgument),
            10 => Ok(Self::Failed),
            other => Err(other),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
#[repr(C)]
pub struct Id128 {
    pub hi: u64,
    pub lo: u64,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
#[repr(C)]
pub struct Digest256 {
    pub words: [u64; 4],
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct BorrowedBytesV1 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub data: *const u8,
    pub size: u64,
    pub reserved0: u64,
}

impl BorrowedBytesV1 {
    pub fn new(bytes: &[u8]) -> Self {
        Self {
            abi_version: ABI_V1,
            struct_size: size_of::<Self>() as u32,
            data: if bytes.is_empty() {
                null()
            } else {
                bytes.as_ptr()
            },
            size: bytes.len() as u64,
            reserved0: 0,
        }
    }
}

#[derive(Debug)]
#[repr(C)]
pub struct OutputBufferV1 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub data: *mut u8,
    pub capacity: u64,
    pub used: u64,
    pub required: u64,
    pub reserved0: u64,
}

impl OutputBufferV1 {
    pub fn new(bytes: &mut [u8]) -> Self {
        Self {
            abi_version: ABI_V1,
            struct_size: size_of::<Self>() as u32,
            data: if bytes.is_empty() {
                null_mut()
            } else {
                bytes.as_mut_ptr()
            },
            capacity: bytes.len() as u64,
            used: 0,
            required: 0,
            reserved0: 0,
        }
    }

    pub fn used<'a>(&self, storage: &'a [u8]) -> Result<&'a [u8], Status> {
        let used = usize::try_from(self.used).map_err(|_| Status::Failed)?;
        if used > storage.len() || self.used > self.capacity {
            return Err(Status::Failed);
        }
        Ok(&storage[..used])
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct InterfaceQueryV1 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub interface_id: Id128,
    pub interface_major: u32,
    pub minimum_minor: u32,
    pub schema_digest: Digest256,
    pub required_operation_mask: u64,
    pub required_capability_mask: u64,
    pub reserved: [u64; 2],
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct InterfaceAnswerV1 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub operation_count: u32,
    pub flags: u32,
    pub operation_table: *const OperationTableV1,
    pub provided_operation_mask: u64,
    pub provided_capability_mask: u64,
    pub schema_digest: Digest256,
    pub reserved: [u64; 2],
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
#[repr(C)]
pub struct CallHeaderV1 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub generation: u64,
    pub session: u64,
    pub request: u64,
    pub interface_slot: u32,
    pub operation_slot: u32,
    pub deadline_ns: u64,
    pub flags: u64,
    pub reserved: [u64; 2],
}

pub type OpenSessionFnV1 =
    unsafe extern "C" fn(u64, *const BorrowedBytesV1, *mut u64) -> StatusCode;
pub type SubmitBatchFnV1 = unsafe extern "C" fn(
    u64,
    *const CallHeaderV1,
    *const BorrowedBytesV1,
    *mut OutputBufferV1,
) -> StatusCode;
pub type PollFnV1 = unsafe extern "C" fn(u64, u64, *mut OutputBufferV1) -> StatusCode;
pub type CancelFnV1 = unsafe extern "C" fn(u64, *const CallHeaderV1) -> StatusCode;
pub type QuiesceFnV1 = unsafe extern "C" fn(u64, u64, u64, u64) -> StatusCode;
pub type CloseSessionFnV1 = unsafe extern "C" fn(u64, u64) -> StatusCode;

#[derive(Clone, Copy)]
#[repr(C)]
pub struct OperationTableV1 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub operation_count: u32,
    pub flags: u32,
    pub open_session: Option<OpenSessionFnV1>,
    pub submit_batch: Option<SubmitBatchFnV1>,
    pub poll: Option<PollFnV1>,
    pub cancel: Option<CancelFnV1>,
    pub quiesce: Option<QuiesceFnV1>,
    pub close_session: Option<CloseSessionFnV1>,
    pub reserved: [u64; 2],
}

pub type PluginEntryFnV1 =
    unsafe extern "C" fn(*const InterfaceQueryV1, *mut InterfaceAnswerV1) -> StatusCode;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RequestHandle {
    pub generation: u64,
    pub session: u64,
    pub request: u64,
}

pub struct Provider<'table> {
    context: u64,
    operations: &'table OperationTableV1,
}

impl<'table> Provider<'table> {
    pub fn new(context: u64, operations: &'table OperationTableV1) -> Result<Self, Status> {
        if operations.abi_version != ABI_V1
            || operations.struct_size < size_of::<OperationTableV1>() as u32
            || operations.open_session.is_none()
            || operations.submit_batch.is_none()
            || operations.poll.is_none()
            || operations.cancel.is_none()
            || operations.quiesce.is_none()
            || operations.close_session.is_none()
        {
            return Err(Status::Rejected);
        }
        Ok(Self {
            context,
            operations,
        })
    }

    pub fn open_session<'provider>(
        &'provider self,
        configuration: &[u8],
    ) -> Result<Session<'provider, 'table>, StatusCode> {
        let mut raw_session = 0;
        let configuration = BorrowedBytesV1::new(configuration);
        let open = self
            .operations
            .open_session
            .ok_or(Status::Rejected as StatusCode)?;
        let code = unsafe { open(self.context, &configuration, &mut raw_session) };
        if code != Status::Ok as StatusCode {
            return Err(code);
        }
        Ok(Session {
            provider: self,
            raw: raw_session,
            quiesced: false,
            closed: false,
            _not_send: PhantomData,
        })
    }
}

pub struct Session<'provider, 'table> {
    provider: &'provider Provider<'table>,
    raw: u64,
    quiesced: bool,
    closed: bool,
    _not_send: PhantomData<*mut c_void>,
}

impl Session<'_, '_> {
    pub fn raw_handle(&self) -> u64 {
        self.raw
    }

    #[allow(clippy::too_many_arguments)]
    pub fn submit(
        &self,
        generation: u64,
        request: u64,
        interface_slot: u32,
        operation_slot: u32,
        deadline_ns: u64,
        flags: u64,
        input: &[u8],
        output: &mut [u8],
    ) -> Result<(RequestHandle, usize, usize), StatusCode> {
        let call = CallHeaderV1 {
            abi_version: ABI_V1,
            struct_size: size_of::<CallHeaderV1>() as u32,
            generation,
            session: self.raw,
            request,
            interface_slot,
            operation_slot,
            deadline_ns,
            flags,
            reserved: [0; 2],
        };
        let input = BorrowedBytesV1::new(input);
        let mut output_wire = OutputBufferV1::new(output);
        let submit = self
            .provider
            .operations
            .submit_batch
            .ok_or(Status::Rejected as StatusCode)?;
        let code = unsafe { submit(self.provider.context, &call, &input, &mut output_wire) };
        match Status::from_code(code) {
            Ok(Status::Ok | Status::Pending | Status::WouldBlock | Status::NeedMore) => {
                let used =
                    usize::try_from(output_wire.used).map_err(|_| Status::Failed as StatusCode)?;
                let required = usize::try_from(output_wire.required)
                    .map_err(|_| Status::Failed as StatusCode)?;
                if used > output.len() || output_wire.used > output_wire.capacity {
                    return Err(Status::Failed as StatusCode);
                }
                Ok((
                    RequestHandle {
                        generation,
                        session: self.raw,
                        request,
                    },
                    used,
                    required,
                ))
            }
            _ => Err(code),
        }
    }

    pub fn poll(&self, completions: &mut [u8]) -> Result<(Status, usize, usize), StatusCode> {
        let mut output = OutputBufferV1::new(completions);
        let poll = self
            .provider
            .operations
            .poll
            .ok_or(Status::Rejected as StatusCode)?;
        let code = unsafe { poll(self.provider.context, self.raw, &mut output) };
        let status = Status::from_code(code).map_err(|code| code)?;
        let used = usize::try_from(output.used).map_err(|_| Status::Failed as StatusCode)?;
        let required =
            usize::try_from(output.required).map_err(|_| Status::Failed as StatusCode)?;
        if used > completions.len() || output.used > output.capacity {
            return Err(Status::Failed as StatusCode);
        }
        Ok((status, used, required))
    }

    pub fn cancel(
        &self,
        request: RequestHandle,
        interface_slot: u32,
        operation_slot: u32,
    ) -> Result<Status, StatusCode> {
        if request.session != self.raw {
            return Ok(Status::StaleHandle);
        }
        let call = CallHeaderV1 {
            abi_version: ABI_V1,
            struct_size: size_of::<CallHeaderV1>() as u32,
            generation: request.generation,
            session: request.session,
            request: request.request,
            interface_slot,
            operation_slot,
            deadline_ns: 0,
            flags: 0,
            reserved: [0; 2],
        };
        let cancel = self
            .provider
            .operations
            .cancel
            .ok_or(Status::Rejected as StatusCode)?;
        Status::from_code(unsafe { cancel(self.provider.context, &call) })
    }

    pub fn quiesce(&mut self, deadline_ns: u64, flags: u64) -> Result<Status, StatusCode> {
        let quiesce = self
            .provider
            .operations
            .quiesce
            .ok_or(Status::Rejected as StatusCode)?;
        let status = Status::from_code(unsafe {
            quiesce(self.provider.context, self.raw, deadline_ns, flags)
        })?;
        if status == Status::Ok {
            self.quiesced = true;
        }
        Ok(status)
    }

    pub fn close(mut self) -> Result<(), StatusCode> {
        if !self.quiesced {
            return Err(Status::Rejected as StatusCode);
        }
        let close = self
            .provider
            .operations
            .close_session
            .ok_or(Status::Rejected as StatusCode)?;
        let code = unsafe { close(self.provider.context, self.raw) };
        if code == Status::Ok as StatusCode {
            self.closed = true;
            Ok(())
        } else {
            Err(code)
        }
    }
}

impl Drop for Session<'_, '_> {
    fn drop(&mut self) {
        if !self.closed {
            if !self.quiesced {
                let Some(quiesce) = self.provider.operations.quiesce else {
                    return;
                };
                if unsafe { quiesce(self.provider.context, self.raw, 0, 0) }
                    != Status::Ok as StatusCode
                {
                    return;
                }
                self.quiesced = true;
            }
            if let Some(close) = self.provider.operations.close_session {
                if unsafe { close(self.provider.context, self.raw) } == Status::Ok as StatusCode {
                    self.closed = true;
                }
            }
        }
    }
}
