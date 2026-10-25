//! Storage cleanup consumes unique canonical retirement authority. Registry and
//! pin locks are already released; disposal never unregisters a second time.
use super::*;

pub(crate) fn dispose_claimed(allocation: ClaimedAllocation) {
    unsafe {
        match allocation.kind {
            HeapObjectType::Array => {
                let array = allocation.ptr as *mut RuntimeArray;
                if !(*array).data.is_null() {
                    let layout = if (*array).is_byte_packed() {
                        byte_array_data_layout((*array).capacity)
                    } else {
                        array_data_layout((*array).capacity)
                    };
                    note_aux_free(HeapObjectType::Array as u8, layout.size() as u64);
                    std::alloc::dealloc((*array).data as *mut u8, layout);
                }
            }
            HeapObjectType::Dict => {
                let dict = allocation.ptr as *mut RuntimeDict;
                super::super::dict::dict_free_slots((*dict).data, (*dict).capacity);
            }
            _ => {}
        }
        let layout =
            std::alloc::Layout::from_size_align(allocation.size, 8).expect("registered heap allocation layout");
        std::alloc::dealloc(allocation.ptr as *mut u8, layout);
    }
}
