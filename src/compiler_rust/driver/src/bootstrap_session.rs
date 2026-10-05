//! Validate the existing bootstrap guard authority before relying on its monitor.
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::Read;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;
use sha2::{Digest, Sha256};

fn pinned_file(path: &Path) -> Option<File> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)
        .ok()?;
    let metadata = file.metadata().ok()?;
    (metadata.is_file() && metadata.uid() == unsafe { libc::geteuid() }).then_some(file)
}

fn digest(file: &mut File) -> Option<String> {
    let mut hash = Sha256::new();
    let mut bytes = [0; 8192];
    loop {
        let count = file.read(&mut bytes).ok()?;
        if count == 0 {
            break;
        }
        hash.update(&bytes[..count]);
    }
    Some(format!("{:x}", hash.finalize()))
}

fn positive_pid(text: &str) -> Option<libc::pid_t> {
    if text.is_empty() || !text.bytes().all(|c| c.is_ascii_digit()) {
        return None;
    }
    text.parse::<libc::pid_t>().ok().filter(|pid| *pid > 0)
}

fn validate(session: &str, helper: &str) -> Option<()> {
    let sid = positive_pid(session)?;
    if unsafe { libc::getsid(0) } != sid || !Path::new(helper).is_absolute() {
        return None;
    }
    let mut admission = pinned_file(Path::new(&format!("{helper}.admission.env")))?;
    if admission.metadata().ok()?.mode() & 0o777 != 0o400 {
        return None;
    }
    let mut text = String::new();
    (&mut admission).take(16385).read_to_string(&mut text).ok()?;
    if text.len() > 16384 || !text.ends_with('\n') {
        return None;
    }
    let mut fields = HashMap::new();
    for line in text.lines() {
        let (key, value) = line.split_once('=')?;
        if key.is_empty()
            || !key.bytes().all(|c| c.is_ascii_lowercase() || c == b'_')
            || fields.insert(key, value).is_some()
        {
            return None;
        }
    }
    if fields.get("schema") != Some(&"simple-bootstrap-session-v1")
        || fields.get("status") != Some(&"active")
        || fields.get("session_id") != Some(&session)
        || fields.get("session_helper") != Some(&helper)
    {
        return None;
    }
    let root = positive_pid(fields.get("root_pid")?)?;
    if unsafe { libc::getsid(root) } != sid {
        return None;
    }
    let mut executable = pinned_file(Path::new(helper))?;
    if executable.metadata().ok()?.mode() & 0o111 == 0 {
        return None;
    }
    if digest(&mut executable)?.as_str() != *fields.get("session_helper_sha")? {
        return None;
    }
    Some(())
}

pub(crate) fn managed_session_active() -> bool {
    let Ok(session) = std::env::var("SIMPLE_BOOTSTRAP_SESSION_ID") else {
        return false;
    };
    let Ok(helper) = std::env::var("SIMPLE_BOOTSTRAP_SESSION_EXEC") else {
        return false;
    };
    validate(&session, &helper).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::os::unix::fs::PermissionsExt;
    #[test]
    fn managed_monitor_requires_real_admission_and_helper() {
        let dir = tempfile::tempdir().unwrap();
        let helper = dir.path().join("helper");
        std::fs::write(&helper, "helper bytes").unwrap();
        std::fs::set_permissions(&helper, std::fs::Permissions::from_mode(0o500)).unwrap();
        let helper_text = helper.to_str().unwrap();
        let sid = unsafe { libc::getsid(0) }.to_string();
        assert!(validate(&sid, helper_text).is_none());
        assert!(validate("0", helper_text).is_none());
        assert!(validate("malformed", helper_text).is_none());
        assert!(validate(&sid, "relative").is_none());
        let receipt = dir.path().join("helper.admission.env");
        let hash = digest(&mut File::open(&helper).unwrap()).unwrap();
        let text = format!("schema=simple-bootstrap-session-v1\nstatus=active\nsession_id={sid}\nsession_helper={helper_text}\nroot_pid={}\nsession_helper_sha={hash}\n", std::process::id());
        File::create(&receipt).unwrap().write_all(text.as_bytes()).unwrap();
        std::fs::set_permissions(&receipt, std::fs::Permissions::from_mode(0o400)).unwrap();
        assert!(validate(&sid, helper_text).is_some());
        std::fs::set_permissions(&receipt, std::fs::Permissions::from_mode(0o600)).unwrap();
        assert!(validate(&sid, helper_text).is_none());
        std::fs::set_permissions(&receipt, std::fs::Permissions::from_mode(0o400)).unwrap();
        std::fs::set_permissions(&helper, std::fs::Permissions::from_mode(0o700)).unwrap();
        std::fs::write(&helper, "changed bytes").unwrap();
        assert!(validate(&sid, helper_text).is_none());
    }
}

#[cfg(test)]
mod contract_branches {
    use super::*;
    use std::os::unix::fs::{symlink, PermissionsExt};
    #[test]
    fn rejects_invalid_authority_fields_and_helper_files() {
        let dir = tempfile::tempdir().unwrap();
        assert!(pinned_file(dir.path()).is_none());
        let other_owner = dir.path().join("other-owner");
        if unsafe { libc::geteuid() } == 0 {
            std::fs::write(&other_owner, "private ownership fixture").unwrap();
            let path = std::ffi::CString::new(other_owner.as_os_str().as_encoded_bytes()).unwrap();
            assert_eq!(unsafe { libc::chown(path.as_ptr(), 1, 1) }, 0);
            assert!(pinned_file(&other_owner).is_none());
        } else {
            assert!(pinned_file(Path::new("/usr/bin/true")).is_none());
        }
        let helper = dir.path().join("helper");
        std::fs::write(&helper, "helper").unwrap();
        std::fs::set_permissions(&helper, std::fs::Permissions::from_mode(0o500)).unwrap();
        let receipt = dir.path().join("helper.admission.env");
        let h = helper.to_str().unwrap();
        let sid = unsafe { libc::getsid(0) }.to_string();
        let hash = digest(&mut File::open(&helper).unwrap()).unwrap();
        let valid = format!("schema=simple-bootstrap-session-v1\nstatus=active\nsession_id={sid}\nsession_helper={h}\nroot_pid={}\nsession_helper_sha={hash}\n", std::process::id());
        let write = |text: &str| {
            if receipt.exists() { std::fs::set_permissions(&receipt, std::fs::Permissions::from_mode(0o600)).unwrap(); }
            std::fs::write(&receipt,text).unwrap();
            std::fs::set_permissions(&receipt,std::fs::Permissions::from_mode(0o400)).unwrap();
        };
        for bad in [valid.replace("simple-bootstrap-session-v1","wrong"),valid.replace("status=active","status=complete"),valid.replace(&format!("session_id={sid}"), &format!("session_id={}", sid.parse::<i64>().unwrap() + 1)),valid.replace(&format!("session_helper={h}"),"session_helper=/wrong"),valid.replace(&format!("root_pid={}",std::process::id()),"root_pid=2147483647"),valid.replace(&format!("root_pid={}",std::process::id()),"root_pid=bad"),valid.replace(&format!("session_helper_sha={hash}\n"),""),valid.clone()+"status=active\n",valid.clone()+"malformed\n",valid.clone()+"BAD=value\n",valid.clone()+"=value\n",valid.clone()+&"x".repeat(16385),valid.trim_end().to_string()] {
            write(&bad); assert!(validate(&sid,h).is_none());
        }
        write(&valid); assert!(validate(&sid,h).is_some());
        std::fs::set_permissions(&helper,std::fs::Permissions::from_mode(0o400)).unwrap();
        assert!(validate(&sid,h).is_none());
        std::fs::set_permissions(&helper,std::fs::Permissions::from_mode(0o500)).unwrap();
        std::fs::remove_file(&helper).unwrap(); assert!(validate(&sid,h).is_none());
        symlink("/bin/sh",&helper).unwrap(); assert!(validate(&sid,h).is_none());
        std::fs::remove_file(&receipt).unwrap(); symlink("/etc/passwd",&receipt).unwrap(); assert!(validate(&sid,h).is_none());
        for bad in ["", "0", "-1", "2147483648", "1x"] { assert!(positive_pid(bad).is_none()); }
        assert!(validate(&(sid.parse::<i64>().unwrap() + 1).to_string(),h).is_none());
    }
}

#[cfg(test)]
mod environment_branches {
    use super::*;
    #[test]
    fn absent_partial_and_invalid_contract_keep_normal_monitor() {
        let id = std::env::var_os("SIMPLE_BOOTSTRAP_SESSION_ID");
        let helper = std::env::var_os("SIMPLE_BOOTSTRAP_SESSION_EXEC");
        std::env::remove_var("SIMPLE_BOOTSTRAP_SESSION_ID");
        std::env::remove_var("SIMPLE_BOOTSTRAP_SESSION_EXEC");
        assert!(!managed_session_active());
        std::env::set_var("SIMPLE_BOOTSTRAP_SESSION_ID", "123");
        assert!(!managed_session_active());
        std::env::set_var("SIMPLE_BOOTSTRAP_SESSION_EXEC", "/missing");
        assert!(!managed_session_active());
        std::env::remove_var("SIMPLE_BOOTSTRAP_SESSION_ID");
        assert!(!managed_session_active());
        if let Some(value) = id { std::env::set_var("SIMPLE_BOOTSTRAP_SESSION_ID", value); }
        if let Some(value) = helper { std::env::set_var("SIMPLE_BOOTSTRAP_SESSION_EXEC", value); }
        else { std::env::remove_var("SIMPLE_BOOTSTRAP_SESSION_EXEC"); }
    }
}
