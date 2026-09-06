use core::mem::{align_of, offset_of, size_of};
use simple_kernel_plugin::*;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn layouts_match_canonical_c_header() {
    assert_eq!((size_of::<Id128>(), align_of::<Id128>()), (16, 8));
    assert_eq!((size_of::<Digest256>(), align_of::<Digest256>()), (32, 8));
    assert_eq!(size_of::<BorrowedBytesV1>(), 32);
    assert_eq!(offset_of!(BorrowedBytesV1, data), 8);
    assert_eq!(offset_of!(BorrowedBytesV1, reserved0), 24);
    assert_eq!(size_of::<OutputBufferV1>(), 48);
    assert_eq!(offset_of!(OutputBufferV1, data), 8);
    assert_eq!(offset_of!(OutputBufferV1, required), 32);
    assert_eq!(size_of::<InterfaceQueryV1>(), 96);
    assert_eq!(offset_of!(InterfaceQueryV1, schema_digest), 32);
    assert_eq!(offset_of!(InterfaceQueryV1, reserved), 80);
    assert_eq!(size_of::<InterfaceAnswerV1>(), 88);
    assert_eq!(offset_of!(InterfaceAnswerV1, operation_table), 16);
    assert_eq!(size_of::<CallHeaderV1>(), 72);
    assert_eq!(offset_of!(CallHeaderV1, interface_slot), 32);
    assert_eq!(offset_of!(CallHeaderV1, reserved), 56);
    assert_eq!(size_of::<OperationTableV1>(), 80);
    assert_eq!(offset_of!(OperationTableV1, open_session), 16);
    assert_eq!(offset_of!(OperationTableV1, close_session), 56);
}

static CLOSES: AtomicUsize = AtomicUsize::new(0);
static LAST_SESSION: AtomicUsize = AtomicUsize::new(0);
static LAST_REQUEST: AtomicUsize = AtomicUsize::new(0);
static SHUTDOWN_ORDER: AtomicUsize = AtomicUsize::new(0);

unsafe extern "C" fn open(_: u64, _: *const BorrowedBytesV1, out: *mut u64) -> i32 {
    unsafe { *out = 41 };
    Status::Ok as i32
}
unsafe extern "C" fn submit(
    _: u64,
    call: *const CallHeaderV1,
    input: *const BorrowedBytesV1,
    output: *mut OutputBufferV1,
) -> i32 {
    let call = unsafe { &*call };
    let input = unsafe { &*input };
    let output = unsafe { &mut *output };
    if call.session != 41 || input.size != 3 {
        return Status::InvalidArgument as i32;
    }
    LAST_REQUEST.store(call.request as usize, Ordering::SeqCst);
    output.used = 2;
    output.required = 2;
    Status::Pending as i32
}
unsafe extern "C" fn poll(_: u64, session: u64, output: *mut OutputBufferV1) -> i32 {
    LAST_SESSION.store(session as usize, Ordering::SeqCst);
    unsafe { (*output).used = 1 };
    Status::Ok as i32
}
unsafe extern "C" fn cancel(_: u64, call: *const CallHeaderV1) -> i32 {
    LAST_REQUEST.store(unsafe { (*call).request as usize }, Ordering::SeqCst);
    Status::Cancelled as i32
}
unsafe extern "C" fn quiesce(_: u64, session: u64, _: u64, _: u64) -> i32 {
    LAST_SESSION.store(session as usize, Ordering::SeqCst);
    SHUTDOWN_ORDER
        .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |order| {
            Some(order.saturating_mul(10).saturating_add(1))
        })
        .ok();
    Status::Ok as i32
}
unsafe extern "C" fn close(_: u64, session: u64) -> i32 {
    LAST_SESSION.store(session as usize, Ordering::SeqCst);
    CLOSES.fetch_add(1, Ordering::SeqCst);
    SHUTDOWN_ORDER
        .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |order| {
            Some(order.saturating_mul(10).saturating_add(2))
        })
        .ok();
    Status::Ok as i32
}

fn table() -> OperationTableV1 {
    OperationTableV1 {
        abi_version: ABI_V1,
        struct_size: size_of::<OperationTableV1>() as u32,
        operation_count: 6,
        flags: 0,
        open_session: Some(open),
        submit_batch: Some(submit),
        poll: Some(poll),
        cancel: Some(cancel),
        quiesce: Some(quiesce),
        close_session: Some(close),
        reserved: [0; 2],
    }
}

#[test]
fn safe_facade_drives_lifecycle_without_double_close() {
    CLOSES.store(0, Ordering::SeqCst);
    SHUTDOWN_ORDER.store(0, Ordering::SeqCst);
    let operations = table();
    let provider = Provider::new(9, &operations).expect("valid table");
    let mut session = provider.open_session(b"config").expect("open");
    let mut output = [0; 8];
    let (request, used, required) = session
        .submit(3, 7, 2, 4, 99, 0, b"abc", &mut output)
        .expect("submit");
    assert_eq!((request.session, used, required), (41, 2, 2));
    assert_eq!(session.poll(&mut output).expect("poll"), (Status::Ok, 1, 0));
    assert_eq!(
        session.cancel(request, 2, 4).expect("cancel"),
        Status::Cancelled
    );
    assert_eq!(session.quiesce(100, 0).expect("quiesce"), Status::Ok);
    session.close().expect("close");
    assert_eq!(CLOSES.load(Ordering::SeqCst), 1);
    assert_eq!(LAST_SESSION.load(Ordering::SeqCst), 41);
    assert_eq!(LAST_REQUEST.load(Ordering::SeqCst), 7);
    assert_eq!(SHUTDOWN_ORDER.load(Ordering::SeqCst), 12);
}

#[test]
fn drop_closes_and_stale_request_is_not_forwarded() {
    CLOSES.store(0, Ordering::SeqCst);
    SHUTDOWN_ORDER.store(0, Ordering::SeqCst);
    let operations = table();
    let provider = Provider::new(0, &operations).expect("valid table");
    {
        let session = provider.open_session(&[]).expect("open");
        let stale = RequestHandle {
            generation: 1,
            session: 99,
            request: 7,
        };
        assert_eq!(
            session.cancel(stale, 0, 0).expect("typed stale"),
            Status::StaleHandle
        );
    }
    assert_eq!(CLOSES.load(Ordering::SeqCst), 1);
    assert_eq!(SHUTDOWN_ORDER.load(Ordering::SeqCst), 12);
}

#[test]
fn close_before_quiesce_is_rejected_then_drop_quiesces_and_closes() {
    CLOSES.store(0, Ordering::SeqCst);
    SHUTDOWN_ORDER.store(0, Ordering::SeqCst);
    let operations = table();
    let provider = Provider::new(0, &operations).expect("valid table");
    let session = provider.open_session(&[]).expect("open");
    assert_eq!(session.close(), Err(Status::Rejected as i32));
    assert_eq!(CLOSES.load(Ordering::SeqCst), 1);
    assert_eq!(SHUTDOWN_ORDER.load(Ordering::SeqCst), 12);
}

#[test]
fn rejects_incomplete_operation_table() {
    let mut operations = table();
    operations.poll = None;
    assert!(matches!(
        Provider::new(0, &operations),
        Err(Status::Rejected)
    ));
}
