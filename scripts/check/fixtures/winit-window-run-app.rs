#![deny(deprecated)]
use winit::{event::{Event, WindowEvent as WinitWindowEvent}, event_loop::{EventLoop, ActiveEventLoop, ControlFlow}, window::Window};
use std::sync::{Arc, Mutex, mpsc};
include!("owner.rs");
#[derive(Debug)] enum Request { Create, Stop, Deadline }
struct DropSignal(mpsc::Sender<&'static str>);
impl Drop for DropSignal { fn drop(&mut self) { self.0.send("captures dropped").unwrap(); } }
fn main() {
    assert!(matches!(convert_window_event(9, WinitWindowEvent::Resized(winit::dpi::PhysicalSize::new(320, 240))), Some(WindowEvent::Resized { window: 9, width: 320, height: 240 })));
    assert!(matches!(convert_window_event(9, WinitWindowEvent::Focused(false)), Some(WindowEvent::Focused { window: 9, focused: false })));
    assert!(matches!(convert_window_event(9, WinitWindowEvent::CloseRequested), Some(WindowEvent::CloseRequested { window: 9 })));
    assert!(matches!(convert_window_event(9, WinitWindowEvent::Moved(winit::dpi::PhysicalPosition::new(-2, 3))), Some(WindowEvent::Moved { window: 9, x: -2, y: 3 })));
    assert!(convert_window_event(9, WinitWindowEvent::RedrawRequested).is_none());
    let event_loop = EventLoop::<Request>::with_user_event().build().unwrap();
    let proxy = event_loop.create_proxy(); proxy.send_event(Request::Create).unwrap();
    let (done_tx, done_rx) = mpsc::channel(); let watchdog_proxy = proxy.clone();
    let watchdog = std::thread::spawn(move || {
        if done_rx.recv_timeout(std::time::Duration::from_secs(10)).is_err() { let _ = watchdog_proxy.send_event(Request::Deadline); }
    });
    let trace = Arc::new(Mutex::new(Vec::new())); let seen = trace.clone();
    let expired = Arc::new(Mutex::new(false)); let deadline = expired.clone();
    let weak_window = Arc::new(Mutex::new(None)); let stored_window = weak_window.clone();
    let (drop_tx, drop_rx) = mpsc::channel(); let drop_signal = DropSignal(drop_tx);
    let mut window: Option<Arc<Window>> = None; let mut stopping = false;
    event_loop.run_app(&mut WindowEventHandler(move |event: Event<Request>, target: &ActiveEventLoop| {
        let _keep_until_loop_return = &drop_signal;
        assert_eq!(target.control_flow(), ControlFlow::Wait);
        match event {
            Event::UserEvent(Request::Create) => {
                assert!(seen.lock().unwrap().is_empty(), "ignored lifecycle events reached callback");
                seen.lock().unwrap().push("create");
                let native = Arc::new(target.create_window(Window::default_attributes().with_visible(false).with_title("hidden winit owner regression")).unwrap());
                assert_eq!(native.is_visible(), Some(false));
                *stored_window.lock().unwrap() = Some(Arc::downgrade(&native));
                native.request_redraw(); window = Some(native);
            }
            Event::WindowEvent { window_id, event } => {
                assert_eq!(window.as_ref().unwrap().id(), window_id);
                assert_eq!(window.as_ref().unwrap().is_visible(), Some(false));
                seen.lock().unwrap().push("window");
                let _converted = convert_window_event(9, event);
                if !stopping { proxy.send_event(Request::Stop).unwrap(); stopping = true; }
            }
            Event::UserEvent(Request::Stop) => { seen.lock().unwrap().push("shutdown"); target.exit(); }
            Event::UserEvent(Request::Deadline) => { *deadline.lock().unwrap() = true; target.exit(); }
            _ => panic!("adapter forwarded a previously ignored event"),
        }
    })).unwrap();
    done_tx.send(()).unwrap(); watchdog.join().unwrap();
    assert!(!*expired.lock().unwrap(), "native hidden window dispatch timed out");
    assert_eq!(drop_rx.try_recv().unwrap(), "captures dropped");
    assert!(weak_window.lock().unwrap().as_ref().unwrap().upgrade().is_none(), "window capture outlived loop statement");
    let trace = trace.lock().unwrap();
    assert_eq!(trace.first(), Some(&"create")); assert!(trace.contains(&"window")); assert_eq!(trace.last(), Some(&"shutdown"));
    println!("PASS pinned winit hidden Windows loop: translation, ignored lifecycle, Wait, shutdown, capture/window drop; {trace:?}");
}
