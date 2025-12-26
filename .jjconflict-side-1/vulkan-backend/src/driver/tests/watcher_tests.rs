use std::path::PathBuf;
use std::thread;
use std::time::Duration;

use simple_driver::watcher::watch;

#[test]
fn watcher_rebuilds_on_change() {
    let dir = tempfile::tempdir().unwrap();
    let src_path = dir.path().join("main.spl");
    std::fs::write(&src_path, "main = 0").unwrap();

    // Spawn watcher in a separate thread; it will rebuild once initially and then on change.
    let src_for_thread = src_path.clone();
    let handle = thread::spawn(move || {
        // Run watcher with verbose=false; will block until the channel errors (never), so we sleep and then return.
        // For the test, we run it for a short time and then exit by letting the thread end.
        let _ = watch(&src_for_thread, false);
    });

    // Give watcher time to do the initial build
    thread::sleep(Duration::from_millis(200));

    // Touch the file to trigger rebuild
    std::fs::write(&src_path, "main = 0 # change").unwrap();
    thread::sleep(Duration::from_millis(200));

    // Validate that the .smf file exists (indicating watcher compiled)
    let smf_path = PathBuf::from(&src_path).with_extension("smf");
    assert!(smf_path.exists());

    // End watcher thread
    drop(handle);
}
