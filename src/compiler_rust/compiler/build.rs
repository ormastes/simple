use std::env;
use std::path::Path;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let project_root = Path::new(&manifest_dir)
        .parent()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .unwrap();

    let platform_dir = project_root.join("src/runtime/platform");

    println!("cargo:rerun-if-changed={}", platform_dir.join("async_driver.c").display());
    println!("cargo:rerun-if-changed={}", platform_dir.join("async_driver.h").display());

    let mut build = cc::Build::new();
    build
        .include(&platform_dir)
        .warnings(false)
        .file(platform_dir.join("async_driver.c"));

    #[cfg(target_os = "linux")]
    {
        build.file(platform_dir.join("async_linux_epoll.c"));
        println!("cargo:rerun-if-changed={}", platform_dir.join("async_linux_epoll.c").display());
        println!("cargo:rustc-link-lib=pthread");
    }

    #[cfg(target_os = "macos")]
    {
        build.file(platform_dir.join("async_macos.c"));
        println!("cargo:rerun-if-changed={}", platform_dir.join("async_macos.c").display());
    }

    #[cfg(target_os = "freebsd")]
    {
        build.file(platform_dir.join("async_freebsd.c"));
        println!("cargo:rerun-if-changed={}", platform_dir.join("async_freebsd.c").display());
        println!("cargo:rustc-link-lib=pthread");
    }

    build.compile("spl_async_driver");
}
