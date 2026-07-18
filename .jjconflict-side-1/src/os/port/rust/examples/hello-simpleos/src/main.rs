#![no_std]
#![no_main]

use core::panic::PanicInfo;

extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn _exit(code: i32) -> !;
}

const MSG: &[u8] = b"hello from rust on simpleos\n";

#[no_mangle]
pub extern "C" fn _start() -> ! {
    unsafe {
        write(1, MSG.as_ptr(), MSG.len());
        _exit(0);
    }
}

#[panic_handler]
fn on_panic(_info: &PanicInfo) -> ! {
    unsafe {
        let msg: &[u8] = b"rust panic\n";
        write(2, msg.as_ptr(), msg.len());
        _exit(101);
    }
}
