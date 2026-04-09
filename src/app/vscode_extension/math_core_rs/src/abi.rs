use core::alloc::Layout;

#[no_mangle]
pub extern "C" fn rt_alloc(size: usize) -> *mut u8 {
    if size == 0 {
        return core::ptr::null_mut();
    }

    let layout = Layout::from_size_align(size, 8).ok();
    match layout {
        Some(layout) => unsafe { std::alloc::alloc_zeroed(layout) },
        None => core::ptr::null_mut(),
    }
}

#[no_mangle]
pub extern "C" fn rt_free(ptr: *mut u8, size: usize) {
    if ptr.is_null() || size == 0 {
        return;
    }

    if let Ok(layout) = Layout::from_size_align(size, 8) {
        unsafe {
            std::alloc::dealloc(ptr, layout);
        }
    }
}
