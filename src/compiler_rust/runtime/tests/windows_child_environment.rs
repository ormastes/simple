#![cfg(windows)]
use simple_runtime::value::RuntimeValue;
use simple_runtime::{rt_array_new,rt_array_push,rt_string_new,rt_string_len,rt_string_data};
use simple_runtime::value::sffi::env_process::{rt_process_run_bounded_environment_tuple_v1,rt_process_spawn_async_environment_v1,rt_process_wait,rt_process_is_running};

fn array(items:&[&str])->RuntimeValue {
    let result=rt_array_new(items.len() as u64);
    for item in items {assert!(rt_array_push(result,rt_string_new(item.as_ptr(),item.len() as u64)));}result
}
unsafe fn capture(exe:&str,args:&[&str],env:&[&str],timeout:i64,cap:i64)->(String,String,i64,i64) {
    let argv=array(args);let environment=array(env);
    let ptr=rt_process_run_bounded_environment_tuple_v1(exe.as_ptr(),exe.len() as u64,argv,environment,1,timeout,cap);
    assert!(!ptr.is_null());
    // Copy all borrowed words before any allocator/provider call.
    let words=[*ptr,*ptr.add(1),*ptr.add(2),*ptr.add(3)];
    let string=|raw:i64| {let v=RuntimeValue::from_raw(raw as u64);let n=rt_string_len(v);assert!(n>=0);String::from_utf8(std::slice::from_raw_parts(rt_string_data(v),n as usize).to_vec()).unwrap()};
    (string(words[0]),string(words[1]),words[2],words[3])
}
fn handles()->u32 {
    use windows::Win32::System::Threading::{GetCurrentProcess,GetProcessHandleCount};
    let mut count=0;unsafe{GetProcessHandleCount(GetCurrentProcess(),&mut count).unwrap();}count
}

#[test]
fn actual_windows_private_environment_rust_provider() {
    let exe=std::env::var("SIMPLE_CHILD_ENV_OBSERVER").expect("real compiled Unicode Win32 observer path required");
    let directory=std::path::PathBuf::from(std::env::var_os("SIMPLE_CHILD_ENV_EVIDENCE").expect("fresh private evidence dir required"));
    assert!(!directory.exists());std::fs::create_dir(&directory).unwrap();
    let before=std::env::vars_os().collect::<Vec<_>>();
    assert_eq!(std::env::var("PARENT_ONLY").unwrap(),"parent-sentinel");
    let exact=["SERIAL_CASE=first","EMPTY=","Δ变量=Grüße 한글 😀","=C:=C:\\"];
    unsafe {
        let (out,err,status,flags)=capture(&exe,&["--observe","first","exact"],&exact,5000,8192);
        assert_eq!((status,flags),(0,0),"{err}");
        for value in ["Grüße 한글 😀","hidden_drive: true","sorted: true","empty_present: true","parent_only_present: false","unexpected: false"] {assert!(out.contains(value),"{out}");}
        let (out,_,status,flags)=capture(&exe,&["--empty"],&[],5000,8192);assert_eq!((status,flags),(0,0));assert!(out.contains("empty_block: true"));
        for invalid in [&["É=one","é=two"][..],&["ΔKEY=one","δkey=two"][..],&["=BAD=value"][..]] {
            let (_,_,status,flags)=capture(&exe,&["--empty"],invalid,5000,8192);assert_eq!(status,-1);assert_eq!(flags&8,8);
        }
        let (_,_,status,flags)=capture(&exe,&[],&exact,5000,8192);assert_eq!(status,90);assert_eq!(flags,0);
        let (_,_,status,flags)=capture(&exe,&["--sleep"],&exact,30,8192);assert_eq!(flags&1,1);assert_eq!(status,-1);
        let (out,err,_,flags)=capture(&exe,&["--flood"],&exact,5000,128);assert_eq!(flags&2,2);assert!(out.is_empty()&&err.is_empty());
        let marker=directory.join("grandchild-ready.sdn").to_str().unwrap().to_owned();
        let (_,_,_,flags)=capture(&exe,&["--spawn-grandchild",&marker],&exact,2000,8192);assert_eq!(flags&1,1);assert!(std::path::Path::new(&marker).exists());
        let gate=directory.join("release.sdn").to_str().unwrap().to_owned();
        let one=directory.join("one.sdn").to_str().unwrap().to_owned();let two=directory.join("two.sdn").to_str().unwrap().to_owned();
        let env1=array(&["SERIAL_CASE=first","EMPTY=","Δ变量=Grüße 한글 😀"]);
        let env2=array(&["serial_case=second","EMPTY=","Δ变量=Grüße 한글 😀"]);
        let p1=rt_process_spawn_async_environment_v1(exe.as_ptr(),exe.len() as u64,array(&["--hold","first","overlay",&one,&gate]),env1,0);
        let p2=rt_process_spawn_async_environment_v1(exe.as_ptr(),exe.len() as u64,array(&["--hold","second","overlay",&two,&gate]),env2,0);
        assert!(p1>0&&p2>0&&p1!=p2);assert!(rt_process_is_running(p1)&&rt_process_is_running(p2));
        assert_eq!(std::env::vars_os().collect::<Vec<_>>(),before);
        std::fs::write(&gate,b"release").unwrap();assert_eq!(rt_process_wait(p1,5000),0);assert_eq!(rt_process_wait(p2,5000),0);
        assert!(std::fs::read_to_string(one).unwrap().contains("case: \"first\""));assert!(std::fs::read_to_string(two).unwrap().contains("case: \"second\""));
        let _=capture(&exe,&["--parent-handles"],&exact,5000,8192);std::thread::sleep(std::time::Duration::from_millis(50));let baseline=handles();
        for _ in 0..16 {let (_,_,status,flags)=capture(&exe,&["--parent-handles"],&exact,5000,8192);assert_eq!((status,flags),(0,0));}
        std::thread::sleep(std::time::Duration::from_millis(50));assert_eq!(handles(),baseline);
    }
    assert_eq!(std::env::vars_os().collect::<Vec<_>>(),before);
    // Receipt TLS initializes before its first replacement initializes the
    // optional heap-free cache. Its final strings must be really freed even
    // when that later TLS dependency has already been destroyed at exit.
    let observer=exe.clone();
    let last=std::thread::spawn(move||unsafe {
        let args=array(&["--empty"]);let env=array(&[]);
        let one=rt_process_run_bounded_environment_tuple_v1(observer.as_ptr(),observer.len() as u64,args,env,1,5000,8192);
        assert!(!one.is_null()&&*one.add(2)==0&&*one.add(3)==0);
        let two=rt_process_run_bounded_environment_tuple_v1(observer.as_ptr(),observer.len() as u64,args,env,1,5000,8192);
        assert!(!two.is_null()&&*two.add(2)==0&&*two.add(3)==0);
        let last=RuntimeValue::from_raw(*two as u64);
        assert!(rt_string_len(last)>0,"receipt's final output must be live nonempty text before teardown");
        last
    }).join().expect("receipt destructor must complete without TLS panic");
    assert_eq!(rt_string_len(last),-1,"thread receipt's last string must be unregistered, not leaked");
}
