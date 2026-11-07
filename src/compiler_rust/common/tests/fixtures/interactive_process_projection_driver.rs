// Shared REAL-provider client assertions; implementations below each invoke
// the native RuntimeValue export or actual interpreter extern dispatch.
use std::time::{Duration,Instant};
pub type Receipt=[u64;32];
pub struct Poll{pub stdout:Vec<u8>,pub stderr:Vec<u8>,pub receipt:Receipt}
pub trait Projection{
 fn capabilities()->Vec<u64>;
 fn deadline(ms:i64)->[u64;8];
 fn start(command:&str,args:&[&str],deadline:[u64;8],input_cap:i64)->Receipt;
 fn write(handle:i64,data:&[u8],offset:i64,max:i64,expected:u64,deadline:[u64;8])->Receipt;
 fn poll(handle:i64,deadline:[u64;8],wait:i64,out:i64,err:i64)->Poll;
 fn close(handle:i64,deadline:[u64;8])->Receipt;
 fn cancel(handle:i64,deadline:[u64;8])->Receipt;
 fn collect(handle:i64,deadline:[u64;8],discard:bool)->Receipt;
 fn release(handle:i64)->Receipt;
}
fn supported<P:Projection>(){
 let c=P::capabilities();assert_eq!(c.len(),16);assert_eq!(&c[..3],&[1,128,0]);
 assert_eq!(c[3]&4095,4095,"Unavailable must NEVER satisfy this Windows functional gate");
 assert_eq!(c[4],128);assert_eq!(c[8],4096);assert_eq!(c[9],65536);assert_eq!(c[10],250);assert_eq!(c[12],1);assert_eq!(c[15],0);
}
fn clock<P:Projection>(ms:i64)->[u64;8]{let d=P::deadline(ms);assert_eq!(d[0],1);assert_eq!(d[1],32);assert_eq!(d[2],1);assert_eq!(d[4],0);assert_eq!(d[7],0);d}
fn receipt(r:Receipt)->Receipt{
 assert_eq!(&r[..2],&[1,256]);assert_eq!(&r[28..],&[0,0,0,0],"private transaction ticket leaked");
 assert_eq!(r[25]&(2|4|4096),0,"unresolved publication/delivery cannot be usable");r
}
fn peer()->String{
 let p=std::env::var("SIMPLE_INTERACTIVE_TEST_PEER").expect("admitted shared C peer path must be pinned by verification runner");
 assert!(std::path::Path::new(&p).is_absolute());assert!(std::path::Path::new(&p).is_file());p
}
struct Lease<P:Projection>{handle:i64,active:bool,kind:std::marker::PhantomData<P>}
impl<P:Projection> Drop for Lease<P>{fn drop(&mut self){
 if !self.active{return;} // Bounded best-effort cleanup on an assertion failure.
 let d=P::deadline(1500);let _=P::cancel(self.handle,d);
 for _ in 0..64{let c=P::collect(self.handle,d,true);if c[5]==6{let r=P::release(self.handle);if r[5]==7{self.active=false;break;}}let _=P::poll(self.handle,d,10,256,256);}
}}
fn start_peer<P:Projection>()->(Lease<P>,[u64;8]){
 let path=peer();let d=clock::<P>(1000);let until=Instant::now()+Duration::from_secs(5);
 loop{let r=receipt(P::start(&path,&["--interactive-child"],d,2));
  if r[2]==2{assert_eq!(r[3],0);assert!(Instant::now()<until);std::thread::yield_now();continue;}
  assert_ne!(r[3]&1,0);assert_ne!(r[4],0);let lease=Lease{handle:r[4]as i64,active:true,kind:std::marker::PhantomData};
  assert!(r[2]==0||r[2]==1,"actual start rejected: {r:?}");return(lease,d);
 }
}
fn ready<P:Projection>(h:i64)->(Vec<u8>,Vec<u8>){
 let mut out=Vec::with_capacity(64);let mut err=Vec::with_capacity(16);let until=Instant::now()+Duration::from_secs(8);
 while out.len()<8||err.len()<6{
  assert!(Instant::now()<until,"child did not publish real startup bytes");let p=P::poll(h,clock::<P>(1000),25,64,64);let r=receipt(p.receipt);
  assert!(r[2]==0||r[2]==1||r[2]==2);out.extend(p.stdout);err.extend(p.stderr);assert_eq!(r[9],0,"EOF is not child completion");
 }
 assert_eq!(out,&[0xff,0,0x80,b'r',b'e',b'a',b'd',b'y']);assert_eq!(err,b"noise!");(out,err)
}
fn collect_and_release<P:Projection>(lease:&mut Lease<P>,discard:bool)->Receipt{
 let until=Instant::now()+Duration::from_secs(8);
 loop{assert!(Instant::now()<until,"owner did not prove actual collection");let r=receipt(P::collect(lease.handle,clock::<P>(1000),discard));
  if r[5]==6{
   assert_eq!(r[25]&(16|64|128),16|64|128,"resource closure/tree-empty/reap must all be observed");
   loop{assert!(Instant::now()<until);let released=receipt(P::release(lease.handle));if released[2]==2||released[2]==9{std::thread::yield_now();continue;}
    assert_eq!(released[2],0);assert_eq!(released[5],7);lease.active=false;
    let stale=P::release(lease.handle);assert_eq!(stale[2],6);assert_eq!(stale[3]&1,0);return r;
   }
  }
  assert!(r[2]==0||r[2]==1||r[2]==2||r[2]==9);let _=P::poll(lease.handle,clock::<P>(1000),10,256,256);
 }
}
pub fn availability_and_clock<P:Projection>(){supported::<P>();let _=clock::<P>(1000);let invalid=P::deadline(-1);assert_eq!(invalid[4],12);}
pub fn invalid_ranges_and_stale<P:Projection>(){
 supported::<P>();let d=clock::<P>(1000);let r=receipt(P::start("C:\\__simple_invalid__\\missing.exe",&[],d,0));assert_eq!(r[2],12);assert_eq!(r[3]&1,0);
 let p=P::poll(-1,d,0,-1,0);assert!(p.stdout.is_empty()&&p.stderr.is_empty());assert_eq!(receipt(p.receipt)[2],12);
 let r=receipt(P::write(-1,b"ACK\n",0,4097,0,d));assert_eq!(r[2],12);assert_eq!(r[3]&1,0);
 let r=receipt(P::release(-1));assert_eq!(r[2],6);assert_eq!(r[3]&1,0);
}
pub fn expired_start_is_unowned<P:Projection>(){
 supported::<P>();let r=receipt(P::start("C:\\__simple_invalid__\\missing.exe",&[],clock::<P>(0),2));
 assert_eq!(r[2],3);assert_eq!(r[3],0);assert_eq!(r[25]&1,0);
}
pub fn wrong_clock_is_unowned<P:Projection>(){
 supported::<P>();let mut d=clock::<P>(1000);d[2]=0x7fff;let r=receipt(P::start("C:\\__simple_invalid__\\missing.exe",&[],d,2));assert_eq!(r[2],12);assert_eq!(r[3]&1,0);
}
pub fn persistent_exchange<P:Projection>(){
 supported::<P>();let(mut lease,start_deadline)=start_peer::<P>();
 // Malformed poll uses a REAL live owner. It must neither change shape nor
 // consume the pending startup bytes, subsequently compared byte-for-byte.
 let malformed=P::poll(lease.handle,clock::<P>(1000),0,-1,64);
 assert!(malformed.stdout.is_empty()&&malformed.stderr.is_empty());let invalid=receipt(malformed.receipt);assert_eq!(invalid[2],12);assert_eq!(invalid[3]&1,0);
 let(mut out,mut err)=ready::<P>(lease.handle);
 let until=Instant::now()+Duration::from_secs(8);
 // Prove startup expiry is NOT the persistent child's lifetime deadline.
 while clock::<P>(0)[3]<=start_deadline[3]{assert!(Instant::now()<until);let p=P::poll(lease.handle,clock::<P>(1000),25,64,64);assert_eq!(p.receipt[9],0);out.extend(p.stdout);err.extend(p.stderr);}
 let live=receipt(P::release(lease.handle));assert_eq!(live[2],9,"live release must retain authority");
 let first=receipt(P::write(lease.handle,b"ACK\n",0,4,0,clock::<P>(1000)));assert_eq!(first[2],0);assert_eq!(first[13],2);assert_eq!(first[14],2);
 let conflict=receipt(P::write(lease.handle,b"ACK\n",0,4,0,clock::<P>(1000)));assert_eq!(conflict[2],4);assert_eq!(conflict[13],0);
 let mut accepted=2u64;
 while accepted<4{assert!(Instant::now()<until);let r=receipt(P::write(lease.handle,b"ACK\n",accepted as i64,4,accepted,clock::<P>(1000)));
  assert!(r[2]==0||r[2]==2);assert!(r[13]<=4-accepted);accepted+=r[13];if r[3]&64!=0{assert_eq!(r[14],accepted);}std::thread::yield_now();}
 let _=receipt(P::close(lease.handle,clock::<P>(1000)));
 loop{assert!(Instant::now()<until,"real EOF/exit never observed");let p=P::poll(lease.handle,clock::<P>(1000),25,64,64);let r=receipt(p.receipt);out.extend(p.stdout);err.extend(p.stderr);
  if r[7]==2&&r[8]==2&&r[9]!=0{assert_eq!(r[9],1);assert_eq!(r[10],0);assert_eq!(r[15],4);assert_eq!(r[19],31);assert_eq!(r[20],6);break;}
 }
 let mut expected=vec![0xff,0,0x80,b'r',b'e',b'a',b'd',b'y'];expected.extend_from_slice(b"Content-Length: 2\r\n\r\n{}");assert_eq!(out,expected);assert_eq!(err,b"noise!");
 let finality=collect_and_release::<P>(&mut lease,false);assert_eq!(finality[23],0);assert_eq!(finality[24],0);
}
pub fn cancel_collects_real_owner<P:Projection>(){
 supported::<P>();let(mut lease,_)=start_peer::<P>();let _=ready::<P>(lease.handle);
 let canceled=receipt(P::cancel(lease.handle,clock::<P>(1000)));assert!(canceled[2]==0||canceled[2]==1);assert_ne!(canceled[25]&512,0);
 let finality=collect_and_release::<P>(&mut lease,true);assert_ne!(finality[9],0,"collection cannot invent pending exit as final");
}
