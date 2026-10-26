//! Typed Windows file boundary for the bootstrap interpreter.
//! This is not a generic DLL resolver. The supported unsafe SPL owners retain
//! their policies; this adapter validates ABI widths and interpreter-owned
//! buffer/handle provenance before forwarding to the real kernel.
use crate::{error::CompileError, value::Value};

pub fn dispatch(name: &str, args: &[Value]) -> Option<Result<Value, CompileError>> {
    let arity = match name {
        "GetProcessHeap" | "GetLastError" => 0,
        "HeapAlloc" | "HeapFree" => 3,
        "CreateFileW" => 7,
        "CloseHandle" | "GetFileAttributesW" | "GetFileType" | "FlushFileBuffers" => 1,
        "GetFinalPathNameByHandleW" | "GetFileInformationByHandleEx" |
        "SetFilePointerEx" | "SetFileInformationByHandle" => 4,
        "ReadFile" | "WriteFile" | "NtSetInformationFile" => 5,
        _ => return None,
    };
    Some((|| {
        if args.len() != arity { return Err(err("argument count")); }
        let values: Vec<i64> = args.iter().map(|v| match v {
            Value::Int(n) => Ok(*n), _ => Err(err("integer ABI argument required")),
        }).collect::<Result<_,_>>()?;
        #[cfg(all(windows,target_pointer_width="64"))]
        { windows::invoke(name, &values) }
        #[cfg(not(all(windows,target_pointer_width="64")))]
        { let _ = values; Err(err("Win64 host required")) }
    })())
}

fn err(reason: &str) -> CompileError {
    CompileError::runtime(format!("Windows file ABI: {reason}"))
}

#[cfg(all(windows,target_pointer_width="64"))]
mod windows {
    use super::*;
    use std::{cell::RefCell, collections::{BTreeMap, HashSet}, ffi::c_void};
    type Handle = *mut c_void;
    const MAX_ALLOC: usize = 64 * 1024 * 1024;
    const MAX_TOTAL: usize = 128 * 1024 * 1024;
    const MAX_OWNERS: usize = 4096;
    #[derive(Default)]
    struct Owners { allocations: BTreeMap<usize,usize>, handles: HashSet<i64>, bytes: usize, error: u32 }
    impl Drop for Owners {
        fn drop(&mut self) {
            // Thread-owned resources cannot be handed to another interpreter
            // worker. Close leaked native owners on thread teardown as well.
            unsafe {
                for &h in &self.handles { CloseHandle(h as Handle); }
                let heap=GetProcessHeap();
                if !heap.is_null() {
                    for &p in self.allocations.keys() { HeapFree(heap,0,p as *mut c_void); }
                }
            }
        }
    }
    thread_local! { static OWNERS: RefCell<Owners> = RefCell::new(Owners::default()); }

    #[link(name="kernel32")]
    unsafe extern "system" {
        fn GetProcessHeap() -> Handle;
        fn HeapAlloc(heap: Handle, flags: u32, size: usize) -> *mut c_void;
        fn HeapFree(heap: Handle, flags: u32, memory: *mut c_void) -> i32;
        fn CreateFileW(path: *const u16, access: u32, sharing: u32, security: *const c_void,
            disposition: u32, flags: u32, template: Handle) -> Handle;
        fn CloseHandle(handle: Handle) -> i32;
        fn GetLastError() -> u32;
        fn GetFinalPathNameByHandleW(handle: Handle, buffer: *mut u16, size: u32, flags: u32) -> u32;
        fn GetFileAttributesW(path: *const u16) -> u32;
        fn GetFileType(handle: Handle) -> u32;
        fn GetFileInformationByHandleEx(handle: Handle, class: i32, info: *mut c_void, size: u32) -> i32;
        fn ReadFile(handle: Handle, buffer: *mut c_void, size: u32, count: *mut u32, overlap: *mut c_void) -> i32;
        fn WriteFile(handle: Handle, buffer: *const c_void, size: u32, count: *mut u32, overlap: *mut c_void) -> i32;
        fn SetFilePointerEx(handle: Handle, distance: i64, position: *mut i64, method: u32) -> i32;
        fn FlushFileBuffers(handle: Handle) -> i32;
        fn SetFileInformationByHandle(handle: Handle, class: i32, info: *const c_void, size: u32) -> i32;
    }
    #[repr(C)]
    struct IoStatusBlock { status_or_pointer: usize, information: usize }
    const _: [();16] = [();std::mem::size_of::<IoStatusBlock>()];
    const _: [();8] = [();std::mem::align_of::<IoStatusBlock>()];
    #[link(name="ntdll")]
    unsafe extern "system" {
        fn NtSetInformationFile(handle: Handle, status: *mut IoStatusBlock,
            info: *const c_void, size: u32, class: i32) -> i32;
    }
    fn u32_arg(value: i64) -> Result<u32,CompileError> { u32::try_from(value).map_err(|_|err("u32 range")) }
    fn i32_arg(value: i64) -> Result<i32,CompileError> { i32::try_from(value).map_err(|_|err("i32 range")) }
    fn extent(o: &Owners, pointer: i64, length: usize) -> Result<usize,CompileError> {
        let start=usize::try_from(pointer).map_err(|_|err("pointer range"))?;
        let (&base,&size)=o.allocations.range(..=start).next_back().ok_or_else(||err("unowned buffer"))?;
        let offset=start.checked_sub(base).ok_or_else(||err("buffer offset"))?;
        if offset >= size || length > size-offset { return Err(err("buffer extent")); }
        Ok(start)
    }
    fn wide(o: &Owners, pointer: i64) -> Result<*const u16,CompileError> {
        let start=extent(o,pointer,2)?;
        if start%2!=0 { return Err(err("UTF16 alignment")); }
        let (&base,&size)=o.allocations.range(..=start).next_back().unwrap();
        let units=((size-(start-base))/2).min(32768);
        // SAFETY: extent belongs to this thread's live HeapAlloc; bound is exact.
        if !(0..units).any(|i|unsafe { *(start as *const u16).add(i)==0 }) {
            return Err(err("unterminated UTF16 path"));
        }
        Ok(start as *const u16)
    }
    fn handle(o: &Owners, value: i64) -> Result<Handle,CompileError> {
        if !o.handles.contains(&value) { return Err(err("unowned file handle")); }
        Ok(value as Handle)
    }
    fn heap(value: i64) -> Result<Handle,CompileError> {
        let actual=unsafe { GetProcessHeap() };
        if actual.is_null() || value!=actual as i64 { return Err(err("process heap identity")); }
        Ok(actual)
    }
    pub(super) fn invoke(name: &str,a: &[i64]) -> Result<Value,CompileError> {
        OWNERS.with(|cell| {
            let mut o=cell.borrow_mut();
            if name=="GetLastError" { return Ok(Value::Int(o.error as i64)); }
            // All borrowed pointers below are checked against retained allocation
            // extents. File handles must have been opened by this same thread.
            let result: i64 = unsafe { match name {
                "GetProcessHeap" => GetProcessHeap() as i64,
                "HeapAlloc" => {
                    let h=heap(a[0])?; let flags=u32_arg(a[1])?;
                    // Later UTF16/rename validation reads initialized bytes.
                    // Actual SPL owners request HEAP_ZERO_MEMORY; flags=0 is
                    // outside this bounded adapter's supported contract.
                    if flags != 8 { return Err(err("zero-initialized heap storage required")); }
                    let size=usize::try_from(a[2]).map_err(|_|err("allocation range"))?;
                    if size==0 || size>MAX_ALLOC || size>MAX_TOTAL-o.bytes || o.allocations.len()>=MAX_OWNERS {
                        return Err(err("allocation budget"));
                    }
                    let pointer=HeapAlloc(h,flags,size); o.error=GetLastError();
                    if !pointer.is_null() { o.allocations.insert(pointer as usize,size); o.bytes+=size; }
                    return Ok(Value::Int(pointer as i64));
                }
                "HeapFree" => {
                    let h=heap(a[0])?;
                    if a[1]!=0 { return Err(err("unsupported heap free flags")); }
                    let pointer=usize::try_from(a[2]).map_err(|_|err("pointer range"))?;
                    let size=*o.allocations.get(&pointer).ok_or_else(||err("unowned allocation base"))?;
                    let result=HeapFree(h,0,pointer as *mut c_void); o.error=GetLastError();
                    if result!=0 { o.allocations.remove(&pointer); o.bytes-=size; }
                    return Ok(Value::Int(result as i64));
                }
                "CreateFileW" => {
                    let path=wide(&o,a[0])?; let access=u32_arg(a[1])?; let sharing=u32_arg(a[2])?;
                    let disposition=u32_arg(a[4])?; let flags=u32_arg(a[5])?;
                    if a[3]!=0 || a[6]!=0 || flags & 0x40000000 != 0 {
                        return Err(err("only synchronous null-security/template files supported"));
                    }
                    if o.handles.len()>=MAX_OWNERS { return Err(err("handle budget")); }
                    let h=CreateFileW(path,access,sharing,std::ptr::null(),disposition,flags,std::ptr::null_mut());
                    o.error=GetLastError();
                    if !h.is_null() && h as i64 != -1 { o.handles.insert(h as i64); }
                    return Ok(Value::Int(h as i64));
                }
                "CloseHandle" => {
                    let h=handle(&o,a[0])?;
                    let result=CloseHandle(h); o.error=GetLastError();
                    if result!=0 { o.handles.remove(&a[0]); }
                    return Ok(Value::Int(result as i64));
                }
                "GetFileAttributesW" => GetFileAttributesW(wide(&o,a[0])?) as i64,
                "GetFinalPathNameByHandleW" => {
                    let h=handle(&o,a[0])?; let count=u32_arg(a[2])?; let flags=u32_arg(a[3])?;
                    let bytes=(count as usize).checked_mul(2).ok_or_else(||err("path buffer overflow"))?;
                    let p=extent(&o,a[1],bytes)?;
                    if p%2!=0 || count==0 { return Err(err("path buffer alignment/capacity")); }
                    GetFinalPathNameByHandleW(h,p as *mut u16,count,flags) as i64
                }
                "GetFileType" => GetFileType(handle(&o,a[0])?) as i64,
                "FlushFileBuffers" => FlushFileBuffers(handle(&o,a[0])?) as i64,
                "GetFileInformationByHandleEx" => {
                    let h=handle(&o,a[0])?; let class=i32_arg(a[1])?; let count=u32_arg(a[3])?;
                    let p=extent(&o,a[2],count as usize)?;
                    GetFileInformationByHandleEx(h,class,p as *mut c_void,count) as i64
                }
                "ReadFile" | "WriteFile" => {
                    let h=handle(&o,a[0])?; let count=u32_arg(a[2])?;
                    let p=extent(&o,a[1],count as usize)?;
                    let out=extent(&o,a[3],4)?;
                    if a[4]!=0 { return Err(err("OVERLAPPED unsupported")); }
                    if name=="ReadFile" { ReadFile(h,p as *mut c_void,count,out as *mut u32,std::ptr::null_mut()) as i64 }
                    else { WriteFile(h,p as *const c_void,count,out as *mut u32,std::ptr::null_mut()) as i64 }
                }
                "SetFilePointerEx" => {
                    let h=handle(&o,a[0])?; let method=u32_arg(a[3])?;
                    let out=if a[2]==0 { std::ptr::null_mut() } else { extent(&o,a[2],8)? as *mut i64 };
                    SetFilePointerEx(h,a[1],out,method) as i64
                }
                "NtSetInformationFile" => {
                    let h=handle(&o,a[0])?;
                    let iosb=extent(&o,a[1],16)?;
                    let count=u32_arg(a[3])?;
                    let class=i32_arg(a[4])?;
                    let p=extent(&o,a[2],count as usize)?;
                    if class!=10 || count<24 || p%8!=0 || iosb%8!=0 {
                        return Err(err("only aligned native FileRenameInformation supported"));
                    }
                    if iosb < p + count as usize && p < iosb + 16 {
                        return Err(err("native rename/status buffers overlap"));
                    }
                    if std::ptr::read_unaligned(p as *const u32)!=0 {
                        return Err(err("only no-replace publication supported"));
                    }
                    let root=std::ptr::read_unaligned((p+8) as *const i64);
                    let name_bytes=std::ptr::read_unaligned((p+16) as *const u32) as usize;
                    if root==0 { return Err(err("retained destination directory required")); }
                    handle(&o,root)?;
                    if name_bytes==0 || name_bytes%2!=0 || name_bytes>count as usize-24 {
                        return Err(err("native rename filename extent"));
                    }
                    // NtSetInformationFile is synchronous. Its signed status
                    // is authoritative; it does not define Win32 last-error.
                    let status=NtSetInformationFile(h,iosb as *mut IoStatusBlock,
                        p as *const c_void,count,class);
                    return Ok(Value::Int(status as i64));
                }
                "SetFileInformationByHandle" => {
                    let h=handle(&o,a[0])?; let class=i32_arg(a[1])?; let count=u32_arg(a[3])?;
                    let p=extent(&o,a[2],count as usize)?;
                    if class!=3 || count<20 { return Err(err("only bounded FileRenameInfo supported")); }
                    if std::ptr::read_unaligned(p as *const u32)!=0 {
                        return Err(err("only no-replace publication supported"));
                    }
                    let root=std::ptr::read_unaligned((p+8) as *const i64);
                    let name_bytes=std::ptr::read_unaligned((p+16) as *const u32) as usize;
                    if root==0 { return Err(err("retained destination directory required")); }
                    handle(&o,root)?;
                    if name_bytes==0 || name_bytes%2!=0 || name_bytes>count as usize-20 {
                        return Err(err("rename filename extent"));
                    }
                    SetFileInformationByHandle(h,class,p as *const c_void,count) as i64
                }
                _ => unreachable!(),
            }};
            // Capture before any Value conversion or allocator/native activity.
            o.error=unsafe { GetLastError() };
            Ok(Value::Int(result))
        })
    }
}

#[cfg(all(test,windows,target_pointer_width="64"))]
mod tests {
    use super::*;
    fn call(name:&str,values:&[i64])->Result<i64,CompileError> {
        match dispatch(name,&values.iter().copied().map(Value::Int).collect::<Vec<_>>()).unwrap()? {
            Value::Int(n)=>Ok(n), _=>panic!("integer ABI result"),
        }
    }
    struct Buffer { heap:i64, pointer:i64 }
    impl Buffer {
        fn new(size:i64)->Self {
            let heap=call("GetProcessHeap",&[]).unwrap();
            let pointer=call("HeapAlloc",&[heap,8,size]).unwrap();
            assert_ne!(pointer,0); Self{heap,pointer}
        }
        fn wide(path:&std::path::Path)->Self {
            use std::os::windows::ffi::OsStrExt;
            let text:Vec<u16>=path.as_os_str().encode_wide().chain([0]).collect();
            let buffer=Self::new((text.len()*2) as i64);
            unsafe { std::ptr::copy_nonoverlapping(text.as_ptr(),buffer.pointer as *mut u16,text.len()); }
            buffer
        }
    }
    impl Drop for Buffer { fn drop(&mut self) { assert_eq!(call("HeapFree",&[self.heap,0,self.pointer]).unwrap(),1); } }
    struct File(i64);
    impl File {
        fn open(path:&std::path::Path,access:i64,flags:i64)->Self {
            let wide=Buffer::wide(path);
            let h=call("CreateFileW",&[wide.pointer,access,7,0,3,flags,0]).unwrap();
            assert_ne!(h,-1); assert_ne!(h,0); Self(h)
        }
    }
    impl Drop for File { fn drop(&mut self) { assert_eq!(call("CloseHandle",&[self.0]).unwrap(),1); } }
    #[test]
    fn windows_file_abi_actual_interpreter_dispatch_uses_typed_owner() {
        let mut env=crate::value::Env::new();
        let result=super::super::call_extern_function_with_values("GetProcessHeap",&[],
            &mut env,&mut Default::default(),&mut Default::default(),
            &Default::default(),&Default::default()).unwrap();
        match result { Value::Int(pointer)=>assert_ne!(pointer,0), _=>panic!("wrong heap ABI") }
    }
    #[test]
    fn windows_file_abi_rejects_wrong_arity_types_widths_and_unknown() {
        assert!(dispatch("other_unknown",&[]).is_none());
        assert!(dispatch("GetProcessHeap",&[Value::Int(1)]).unwrap().is_err());
        assert!(dispatch("HeapAlloc",&[Value::Int(0),Value::Bool(false),Value::Int(8)]).unwrap().is_err());
        let b=Buffer::new(8);
        assert!(call("HeapAlloc",&[b.heap,1i64<<32,8]).is_err());
        assert!(call("HeapAlloc",&[b.heap,0,8]).is_err());
        assert!(call("HeapAlloc",&[b.heap,8,65*1024*1024]).is_err());
        assert!(call("HeapAlloc",&[b.heap,8,-1]).is_err());
    }
    #[test]
    fn windows_file_abi_rejects_unowned_interior_free_and_use_after_free() {
        let heap=call("GetProcessHeap",&[]).unwrap();
        let p=call("HeapAlloc",&[heap,8,8]).unwrap();
        assert!(call("HeapFree",&[heap,0,p+1]).is_err());
        assert_eq!(call("HeapFree",&[heap,0,p]).unwrap(),1);
        assert!(call("HeapFree",&[heap,0,p]).is_err());
        assert!(call("GetFileAttributesW",&[p]).is_err());
        assert!(call("CloseHandle",&[123]).is_err());
    }
    #[test]
    fn windows_file_abi_rejects_unterminated_and_misaligned_paths() {
        let b=Buffer::new(8);
        unsafe { std::ptr::write_bytes(b.pointer as *mut u8,65,8); }
        assert!(call("GetFileAttributesW",&[b.pointer]).is_err());
        assert!(call("GetFileAttributesW",&[b.pointer+1]).is_err());
        assert!(call("GetFileAttributesW",&[b.pointer+8]).is_err());
    }
    #[test]
    fn windows_file_abi_rejects_cross_thread_resources() {
        let b=Buffer::new(8); let p=b.pointer; let h=b.heap;
        std::thread::spawn(move||{
            assert!(call("HeapFree",&[h,0,p]).is_err());
            assert!(call("GetFileAttributesW",&[p]).is_err());
        }).join().unwrap();
    }
    #[test]
    fn windows_file_abi_reads_binary_unicode_file_and_exact_identity() {
        let dir=tempfile::tempdir().unwrap(); let path=dir.path().join("file-한글-🦀.bin");
        let bytes=[0,255,13,10,65]; std::fs::write(&path,bytes).unwrap();
        let file=File::open(&path,0x80000000,0x00200000);
        assert_eq!(call("GetFileType",&[file.0]).unwrap(),1);
        let b=Buffer::new(128);
        assert_eq!(call("GetFileInformationByHandleEx",&[file.0,18,b.pointer,24]).unwrap(),1);
        assert_eq!(call("ReadFile",&[file.0,b.pointer,5,b.pointer+64,0]).unwrap(),1);
        unsafe {
            assert_eq!(std::ptr::read_unaligned((b.pointer+64) as *const u32),5);
            assert_eq!(std::slice::from_raw_parts(b.pointer as *const u8,5),bytes);
        }
        assert_eq!(call("SetFilePointerEx",&[file.0,0,0,0]).unwrap(),1);
        assert!(call("ReadFile",&[file.0,b.pointer,129,b.pointer+64,0]).is_err());
        assert!(call("ReadFile",&[file.0,b.pointer,5,b.pointer+127,0]).is_err());
        assert!(call("ReadFile",&[file.0,b.pointer,5,b.pointer+64,1]).is_err());
    }
    #[test]
    fn windows_file_abi_queries_bounded_final_path_and_preserves_missing_error() {
        let dir=tempfile::tempdir().unwrap(); let file=File::open(dir.path(),128,0x02000000);
        let b=Buffer::new(65536);
        assert!(call("GetFinalPathNameByHandleW",&[file.0,b.pointer,32768,1]).unwrap()>0);
        assert!(call("GetFinalPathNameByHandleW",&[file.0,b.pointer,32769,1]).is_err());
        let missing=Buffer::wide(&dir.path().join("absent"));
        assert_eq!(call("GetFileAttributesW",&[missing.pointer]).unwrap(),u32::MAX as i64);
        assert_eq!(call("GetLastError",&[]).unwrap(),2);
        assert!(!dir.path().join("absent").exists());
    }
    #[test]
    fn windows_file_abi_writes_and_syncs_without_truncating_other_bytes() {
        let dir=tempfile::tempdir().unwrap(); let path=dir.path().join("write.bin");
        std::fs::write(&path,[1,2,3,4]).unwrap();
        let file=File::open(&path,0xC0000000,0);
        let b=Buffer::new(16); unsafe { *(b.pointer as *mut u8)=9; }
        assert_eq!(call("SetFilePointerEx",&[file.0,2,0,0]).unwrap(),1);
        assert_eq!(call("WriteFile",&[file.0,b.pointer,1,b.pointer+8,0]).unwrap(),1);
        assert_eq!(call("FlushFileBuffers",&[file.0]).unwrap(),1);
        drop(file); assert_eq!(std::fs::read(path).unwrap(),[1,2,9,4]);
    }
    #[test]
    fn windows_file_abi_rejects_malformed_rename_without_touching_files() {
        let dir=tempfile::tempdir().unwrap(); let path=dir.path().join("keep.bin");
        std::fs::write(&path,[1,2,3]).unwrap();
        let file=File::open(&path,0x00010000,0);
        let b=Buffer::new(32);
        unsafe { std::ptr::write_unaligned((b.pointer+16) as *mut u32,13); }
        assert!(call("SetFileInformationByHandle",&[file.0,3,b.pointer,32]).is_err());
        assert!(call("SetFileInformationByHandle",&[file.0,3,b.pointer,19]).is_err());
        drop(file); assert_eq!(std::fs::read(path).unwrap(),[1,2,3]);
    }
    #[test]
    fn windows_file_abi_same_retained_file_identity_detects_hardlinks() {
        let dir=tempfile::tempdir().unwrap(); let first=dir.path().join("first");
        let second=dir.path().join("second");
        std::fs::write(&first,[1,2,3]).unwrap(); std::fs::hard_link(&first,&second).unwrap();
        let a=File::open(&first,0x80000000,0x00200000);
        let b=File::open(&second,0x80000000,0x00200000);
        let x=Buffer::new(24); let y=Buffer::new(24);
        assert_eq!(call("GetFileInformationByHandleEx",&[a.0,18,x.pointer,24]).unwrap(),1);
        assert_eq!(call("GetFileInformationByHandleEx",&[b.0,18,y.pointer,24]).unwrap(),1);
        unsafe { assert_eq!(std::slice::from_raw_parts(x.pointer as *const u8,24),
                           std::slice::from_raw_parts(y.pointer as *const u8,24)); }
    }
    #[test]
    fn windows_file_abi_no_replace_rename_uses_retained_directory() {
        use std::os::windows::ffi::OsStrExt;
        let dir=tempfile::tempdir().unwrap(); let source=dir.path().join("source");
        let destination=dir.path().join("taken");
        std::fs::write(&source,[1,2,3]).unwrap(); std::fs::write(&destination,[4,5]).unwrap();
        let source_path=Buffer::wide(&source);
        let file=File(call("CreateFileW",&[source_path.pointer,0xC0010080,1,0,3,0x00200080,0]).unwrap());
        assert_ne!(file.0,-1);
        let directory_path=Buffer::wide(dir.path());
        let root=File(call("CreateFileW",&[directory_path.pointer,128,1,0,3,0x02200000,0]).unwrap());
        assert_ne!(root.0,-1);
        let name:Vec<u16>=std::ffi::OsStr::new("taken").encode_wide().collect();
        let extent=24+name.len()*2;
        let b=Buffer::new(extent as i64);
        let iosb=Buffer::new(16);
        unsafe {
            std::ptr::write_unaligned((b.pointer+8) as *mut i64,root.0);
            std::ptr::write_unaligned((b.pointer+16) as *mut u32,(name.len()*2) as u32);
            std::ptr::copy_nonoverlapping(name.as_ptr(),(b.pointer+20) as *mut u16,name.len());
        }
        let refused=call("NtSetInformationFile",&[file.0,iosb.pointer,b.pointer,extent as i64,10]).unwrap();
        assert!(refused<0, "existing destination must be refused: {refused:#x}");
        assert_eq!(std::fs::read(&source).unwrap(),[1,2,3]);
        assert_eq!(std::fs::read(&destination).unwrap(),[4,5]);
        std::fs::remove_file(&destination).unwrap();
        assert_eq!(call("NtSetInformationFile",&[file.0,iosb.pointer,b.pointer,extent as i64,10]).unwrap(),0);
        assert!(!source.exists()); assert_eq!(std::fs::read(destination).unwrap(),[1,2,3]);
    }
    #[test]
    fn windows_file_abi_thread_teardown_closes_unreleased_handles() {
        let dir=tempfile::tempdir().unwrap(); let path=dir.path().join("exclusive");
        std::fs::write(&path,[1]).unwrap(); let child_path=path.clone();
        std::thread::spawn(move||{
            let b=Buffer::wide(&child_path);
            let h=call("CreateFileW",&[b.pointer,0x80000000,0,0,3,0,0]).unwrap();
            assert_ne!(h,-1);
            let heap=call("GetProcessHeap",&[]).unwrap();
            assert_ne!(call("HeapAlloc",&[heap,8,32]).unwrap(),0);
            // Deliberately leave both to the real TLS owner destructor.
        }).join().unwrap();
        assert_eq!(std::fs::read(&path).unwrap(),[1]);
        std::fs::remove_file(path).unwrap();
    }
    #[test]
    fn windows_file_abi_unaligned_count_matches_retained_spl_layout() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("unaligned-count.bin");
        std::fs::write(&path, [0, 255, 13, 10, 65]).unwrap();
        let file = File::open(&path, 0xC0000000, 0x00200000);
        let buffer = Buffer::new(16);
        // RetainedFile.read(maximum=5) places its DWORD immediately after
        // the five-byte payload. Validate the real Windows call at offset5.
        assert_eq!(call("ReadFile", &[file.0, buffer.pointer, 5, buffer.pointer + 5, 0]).unwrap(), 1);
        unsafe {
            assert_eq!(std::ptr::read_unaligned((buffer.pointer + 5) as *const u32), 5);
            assert_eq!(std::slice::from_raw_parts(buffer.pointer as *const u8, 5), [0, 255, 13, 10, 65]);
            *(buffer.pointer as *mut u8) = 9;
        }
        assert_eq!(call("SetFilePointerEx", &[file.0, 0, 0, 0]).unwrap(), 1);
        // RetainedFile.write(one byte) uses an equally valid DWORD at offset1.
        assert_eq!(call("WriteFile", &[file.0, buffer.pointer, 1, buffer.pointer + 1, 0]).unwrap(), 1);
        unsafe {
            assert_eq!(std::ptr::read_unaligned((buffer.pointer + 1) as *const u32), 1);
        }
        assert_eq!(call("FlushFileBuffers", &[file.0]).unwrap(), 1);
        drop(file);
        assert_eq!(std::fs::read(path).unwrap(), [9, 255, 13, 10, 65]);
    }
}
