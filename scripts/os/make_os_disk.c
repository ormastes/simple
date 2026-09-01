/*
 * Native SimpleOS FAT32 image builder.
 *
 * This keeps scripts/os/make_os_disk.shs independent of Python while
 * preserving the real FAT32 image and optional x86_64 ESP sidecar behavior.
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdbool.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#ifdef _WIN32
#include <direct.h>
#else
#include <fcntl.h>
#include <unistd.h>
#endif

enum {
    SECTOR_SIZE = 512,
    DEFAULT_TOTAL_SECTORS = 131072, /* 64 MiB */
    RESERVED_SECTORS = 32,
    FAT_COUNT = 1,
    ROOT_CLUSTER = 2,
    DIRECTORY_BYTES = 4096,
    DIRECTORY_ENTRY_CAPACITY = DIRECTORY_BYTES / 32,
    FAT32_MIN_DATA_CLUSTERS = 65525,
    SIMPLEOS_REPLACE_DESCRIPTOR_SECTOR = 2,
    SIMPLEOS_REPLACE_JOURNAL_START = 16,
    SIMPLEOS_REPLACE_JOURNAL_SECTORS = 16,
};

struct bytes {
    unsigned char *data;
    size_t len;
};

#include "make_os_disk_support.inc.c"
int main(int argc, char **argv)
{
    enum { FONT_ASSET_COUNT = 16 };
    static const char *font_env_names[FONT_ASSET_COUNT] = {
        "SIMPLEOS_FONT_ASSET_NSANSSC", "SIMPLEOS_FONT_ASSET_NSANSDEV",
        "SIMPLEOS_FONT_ASSET_NSANSARB", "SIMPLEOS_FONT_ASSET_NSANSBEN",
        "SIMPLEOS_FONT_ASSET_NSERIFSC", "SIMPLEOS_FONT_ASSET_NSERFDEV",
        "SIMPLEOS_FONT_ASSET_NNASKHAR", "SIMPLEOS_FONT_ASSET_NSERFBEN",
        "SIMPLEOS_FONT_ASSET_NOTOSANS", "SIMPLEOS_FONT_ASSET_BUNGEE",
        "SIMPLEOS_FONT_ASSET_NUNITO", "SIMPLEOS_FONT_ASSET_CAVEAT",
        "SIMPLEOS_FONT_ASSET_ROBOSLAB", "SIMPLEOS_FONT_ASSET_UNIFRAKT",
        "SIMPLEOS_FONT_ASSET_PIXELIFY", "SIMPLEOS_FONT_ASSET_NOTOEMOJ"
    };
    static const char *font_fat_names[FONT_ASSET_COUNT] = {
        "NSANSSC    ", "NSANSDEV   ", "NSANSARB   ", "NSANSBEN   ",
        "NSERIFSC   ", "NSERFDEV   ", "NNASKHAR   ", "NSERFBEN   ",
        "NOTOSANS   ", "BUNGEE     ", "NUNITO     ", "CAVEAT     ",
        "ROBOSLAB   ", "UNIFRAKT   ", "PIXELIFY   ", "NOTOEMOJ   "
    };
    static const char *font_long_names[FONT_ASSET_COUNT] = {
        "NotoSansSC[wght].ttf", "NotoSansDevanagari[wdth,wght].ttf",
        "NotoSansArabic[wdth,wght].ttf", "NotoSansBengali[wdth,wght].ttf",
        "NotoSerifSC[wght].ttf", "NotoSerifDevanagari[wdth,wght].ttf",
        "NotoNaskhArabic[wght].ttf", "NotoSerifBengali[wdth,wght].ttf",
        "NotoSansMono[wdth,wght].ttf", "Bungee-Regular.ttf",
        "Nunito[wght].ttf", "Caveat[wght].ttf",
        "RobotoSlab[wght].ttf", "UnifrakturCook-Bold.ttf",
        "PixelifySans[wght].ttf", "NotoEmoji[wght].ttf"
    };
    /* Compatibility overrides may relocate validated TTF bytes only. Keep
     * metadata/licenses anchored to the canonical pinned repository tree. */
    static const char *font_companion_anchor_paths[FONT_ASSET_COUNT] = {
        "assets/fonts/google-fonts/ofl/notosanssc/NotoSansSC[wght].ttf",
        "assets/fonts/google-fonts/ofl/notosansdevanagari/NotoSansDevanagari[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notosansarabic/NotoSansArabic[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notosansbengali/NotoSansBengali[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notoserifsc/NotoSerifSC[wght].ttf",
        "assets/fonts/google-fonts/ofl/notoserifdevanagari/NotoSerifDevanagari[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notonaskharabic/NotoNaskhArabic[wght].ttf",
        "assets/fonts/google-fonts/ofl/notoserifbengali/NotoSerifBengali[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf",
        "assets/fonts/google-fonts/ofl/nunito/Nunito[wght].ttf",
        "assets/fonts/google-fonts/ofl/caveat/Caveat[wght].ttf",
        "assets/fonts/google-fonts/apache/robotoslab/RobotoSlab[wght].ttf",
        "assets/fonts/google-fonts/ofl/unifrakturcook/UnifrakturCook-Bold.ttf",
        "assets/fonts/google-fonts/ofl/pixelifysans/PixelifySans[wght].ttf",
        "assets/fonts/google-fonts/ofl/notoemoji/NotoEmoji[wght].ttf"
    };
    if (argc != 5 && argc != 6)
        die("usage: make_os_disk IMAGE PLATFORM SIZE_BITS KERNEL [PROFILE]");
    const char *img_path = argv[1];
    const char *platform = argv[2];
    const char *kernel_path = argv[4];
    const char *profile = argc == 6 ? argv[5] : "fs-exec";
    bool desktop_fonts = strcmp(profile, "desktop-fonts") == 0;
    if (!desktop_fonts && strcmp(profile, "fs-exec") != 0)
        die("unsupported SimpleOS disk profile");
    const char *lane = lane_for_platform(platform);

    init_geometry(argv[3]);
    size_t image_size = (size_t)g_total_sectors * SECTOR_SIZE;
    g_image_size = image_size;
    g_image = (unsigned char *)xcalloc(image_size, 1);
    g_fat = (uint32_t *)xcalloc(g_fat_entry_count, sizeof(uint32_t));
    g_fat[0] = 0x0ffffff8U;
    g_fat[1] = 0x0fffffffU;
    g_fat[ROOT_CLUSTER] = 0x0fffffffU;
    reserve_root_directory();

    const char *hello_marker = strcmp(platform, "riscv64") == 0 ? "SIMPLEOS_RISCV64_HELLO_ELF" :
        strcmp(platform, "riscv32") == 0 ? "SIMPLEOS_RISCV32_HELLO_ELF" :
        strcmp(platform, "arm64") == 0 ? "SIMPLEOS_ARM64_HELLO_ELF" :
        strcmp(platform, "arm32") == 0 ? "SIMPLEOS_ARM32_HELLO_ELF" :
        strcmp(platform, "x86_32") == 0 ? "SIMPLEOS_X86_32_HELLO_ELF" : "SIMPLEOS_X86_64_HELLO_ELF";
    const char *gui_marker = strcmp(platform, "riscv64") == 0 ? "SIMPLEOS_RISCV64_GUI_ELF" :
        strcmp(platform, "riscv32") == 0 ? "SIMPLEOS_RISCV32_GUI_ELF" :
        strcmp(platform, "arm64") == 0 ? "SIMPLEOS_ARM64_GUI_ELF" :
        strcmp(platform, "arm32") == 0 ? "SIMPLEOS_ARM32_GUI_ELF" :
        strcmp(platform, "x86_32") == 0 ? "SIMPLEOS_X86_32_GUI_ELF" : "SIMPLEOS_X86_64_GUI_ELF";

    struct bytes kernel_file = read_file(kernel_path);
    struct bytes bootloader_file = read_file(getenv("SIMPLEOS_UEFI_BOOTLOADER"));
    struct bytes simple_payload = desktop_fonts ? (struct bytes){0} : read_simpleos_simple_payload();
    struct bytes clang_payload = read_file(getenv("SIMPLEOS_CLANG_BINARY"));
    struct bytes llc_payload = read_file(getenv("SIMPLEOS_LLC_BINARY"));
    struct bytes lld_payload = read_file(getenv("SIMPLEOS_LLD_BINARY"));
    struct bytes llvm_ar_payload = read_file(getenv("SIMPLEOS_LLVM_AR_BINARY"));
    struct bytes crt0_payload = read_file(getenv("SIMPLEOS_CRT0_OBJECT"));
    struct bytes runtime_payload = read_file(getenv("SIMPLEOS_RUNTIME_ARCHIVE"));
    struct bytes libc_payload = read_file(getenv("SIMPLEOS_LIBC_ARCHIVE"));
    struct bytes linker_script_payload = read_file(getenv("SIMPLEOS_LINKER_SCRIPT"));
    struct bytes simple_entry_payload = read_file(getenv("SIMPLEOS_SIMPLE_ENTRY_OBJECT"));
    struct bytes hello_object_payload = read_file(getenv("SIMPLEOS_HELLO_OBJECT"));
    struct bytes hello_ir_payload = read_file(getenv("SIMPLEOS_HELLO_IR"));
    struct bytes fsexec_payload = read_file(getenv("SIMPLEOS_FSEXEC_BINARY"));
    struct bytes authhello_payload = read_file(getenv("SIMPLEOS_AUTHHELLO_BINARY"));
    struct bytes authhello_manifest = read_file(getenv("SIMPLEOS_AUTHHELLO_MANIFEST"));
    struct bytes authhello_admission = read_file(getenv("SIMPLEOS_AUTHHELLO_ADMISSION"));
    struct bytes authhello_proof = read_file(getenv("SIMPLEOS_AUTHHELLO_PROOF"));
    struct bytes authhello_trust_root = read_file(getenv("SIMPLEOS_AUTHHELLO_TRUST_ROOT"));
    if ((authhello_payload.len || authhello_manifest.len || authhello_admission.len ||
         authhello_proof.len || authhello_trust_root.len) &&
        (!authhello_payload.len || !authhello_manifest.len || !authhello_admission.len ||
         !authhello_proof.len || !authhello_trust_root.len)) {
        fprintf(stderr, "AUTHHELLO.ELF requires manifest, admission, proof, and trust-root sidecars\n");
        return 1;
    }
    struct bytes servers_payload = read_file(getenv("SIMPLEOS_SERVERS_BINARY"));
    struct bytes servers_manifest = read_file(getenv("SIMPLEOS_SERVERS_MANIFEST"));
    struct bytes servers_admission = read_file(getenv("SIMPLEOS_SERVERS_ADMISSION"));
    struct bytes servers_proof = read_file(getenv("SIMPLEOS_SERVERS_PROOF"));
    struct bytes servers_trust_root = read_file(getenv("SIMPLEOS_SERVERS_TRUST_ROOT"));
    if ((servers_payload.len || servers_manifest.len || servers_admission.len || servers_proof.len || servers_trust_root.len) &&
        (!servers_payload.len || !servers_manifest.len || !servers_admission.len ||
         !servers_proof.len || !servers_trust_root.len)) {
        fprintf(stderr, "SERVERS.ELF requires manifest, admission, proof, and trust-root sidecars\n");
        return 1;
    }
    const char *server_credential_path = getenv("SIMPLEOS_SERVER_DB_CREDENTIAL_FILE");
    const char *server_certificate_path = getenv("SIMPLEOS_SERVER_DB_CERTIFICATE_FILE");
    const char *server_private_key_path = getenv("SIMPLEOS_SERVER_DB_PRIVATE_KEY_FILE");
    const char *server_credentials_manifest_path = getenv("SIMPLEOS_SERVER_DB_CREDENTIAL_MANIFEST_FILE");
    struct bytes server_credential = read_bounded_regular_file(server_credential_path, 128);
    struct bytes server_certificate = read_bounded_regular_file(server_certificate_path, 65536);
    struct bytes server_private_key = read_bounded_regular_file(server_private_key_path, 16384);
    struct bytes server_credentials_manifest = read_bounded_regular_file(server_credentials_manifest_path, 1024);
    if (servers_payload.len && (!server_credential.len || !server_certificate.len ||
                                !server_private_key.len || !server_credentials_manifest.len)) {
        wipe_bytes(server_credential);
        wipe_bytes(server_certificate);
        wipe_bytes(server_private_key);
        fprintf(stderr, "SERVERS.ELF requires bounded regular SRVDB.KEY, SRVDB.CRT, SRVDB.PK8, and credential-manifest inputs\n");
        return 1;
    }
    /* The fullscreen WM showcase stages a REAL freestanding browser client at
     * ::/SYS/APPS/BROWSMF.SMF. When SIMPLEOS_BROWSER_DEMO_BINARY is supplied it
     * is authoritative: an explicitly requested client must never be silently
     * replaced by the synthesized marker stub, so an unreadable/empty path is a
     * hard error rather than a fallback. The stub remains only for callers that
     * supply no binary at all (e.g. desktop-fonts profiles). */
    const char *browser_demo_path = getenv("SIMPLEOS_BROWSER_DEMO_BINARY");
    struct bytes browser_payload = read_file(getenv("SIMPLEOS_BROWSER_DEMO_BINARY"));
    if (browser_demo_path && browser_demo_path[0] != '\0' && !browser_payload.len) {
        fprintf(stderr, "SIMPLEOS_BROWSER_DEMO_BINARY could not be read: %s\n",
                browser_demo_path);
        return 1;
    }
    struct bytes font_payloads[FONT_ASSET_COUNT];
    struct bytes font_metadata_payloads[FONT_ASSET_COUNT];
    struct bytes font_license_payloads[FONT_ASSET_COUNT];
    for (int i = 0; i < FONT_ASSET_COUNT; ++i) {
        const char *font_asset_path = getenv(font_env_names[i]);
        if (!font_asset_path || font_asset_path[0] == '\0') {
            fprintf(stderr, "%s is required\n", font_env_names[i]);
            return 1;
        }
        font_payloads[i] = read_file(font_asset_path);
        if (!font_payloads[i].len) {
            fprintf(stderr, "%s could not be read\n", font_env_names[i]);
            return 1;
        }
        font_metadata_payloads[i] = read_sibling_file(font_companion_anchor_paths[i], "METADATA.pb");
        font_license_payloads[i] = read_sibling_file(
            font_companion_anchor_paths[i], i == 12 ? "LICENSE.txt" : "OFL.txt");
        if (!font_metadata_payloads[i].len || !font_license_payloads[i].len) {
            fprintf(stderr, "%s companion metadata/license could not be read\n", font_env_names[i]);
            return 1;
        }
    }
    struct bytes font_copyright_payload = read_sibling_file(font_companion_anchor_paths[12], "COPYRIGHT.txt");
    struct bytes font_corpus_payload = read_file("assets/fonts/google-fonts/CORPUS.sdn");
    struct bytes cldr_license_payload = read_file("assets/fonts/cldr/release-48-2/LICENSE");
    struct bytes simple_license_payload = read_file("LICENSE");
    struct bytes third_party_notices_payload = read_file("THIRD_PARTY_NOTICES.md");
    const char *theme_path = getenv("SIMPLEOS_WM_THEME_FILE");
    struct bytes theme_payload = read_file(theme_path);
    if (theme_path && theme_path[0] != '\0' && !theme_payload.len) {
        fprintf(stderr, "SIMPLEOS_WM_THEME_FILE could not be read: %s\n", theme_path);
        return 1;
    }
    if (!font_copyright_payload.len || !font_corpus_payload.len || !cldr_license_payload.len ||
        !simple_license_payload.len || !third_party_notices_payload.len)
        die("SimpleOS font bundle global notice could not be read");
    if (desktop_fonts) {
        write_desktop_font_image(
            img_path, font_fat_names, font_long_names, font_payloads,
            font_metadata_payloads, font_license_payloads, font_copyright_payload,
            font_corpus_payload, cldr_license_payload, simple_license_payload,
            third_party_notices_payload, theme_payload);
        return 0;
    }
    int efi_cluster = alloc_directory();
    int boot_cluster = alloc_directory();
    int sys_cluster = alloc_directory();
    int fonts_cluster = alloc_directory();
    int apps_cluster = alloc_directory();
    int perf_cluster = alloc_directory();
    int usr_cluster = alloc_directory();
    int usr_bin_cluster = alloc_directory();
    int usr_lib_cluster = alloc_directory();
    int bin_cluster = alloc_directory();
    int sysrt_cluster = alloc_directory();
    int tmp_cluster = alloc_directory();
    int work_cluster = alloc_directory();
    struct bytes cfat4k = read_cfat4k_baseline();
    struct bytes kernel = kernel_file.len ? kernel_file : text_bytes("SIMPLEOS_UEFI_KERNEL_MISSING\n");
    struct bytes bootloader = bootloader_file.len ? bootloader_file : text_bytes("SIMPLEOS_UEFI_BOOTLOADER_MISSING\n");
    struct bytes limine = text_bytes("timeout: 0\nserial: yes\n/ SimpleOS\nprotocol: multiboot1\npath: boot():/kernel.elf\ntextmode: no\nresolution: 1024x768x32\ncmdline: console=serial root=/dev/nvme0n1\n");
    struct bytes hello_txt = text_bytes("Hello from SimpleOS\n");
    struct bytes server_document = text_bytes("<html><body>SimpleOS filesystem server document</body></html>\n");
    static unsigned char qemu_nonce_slot_data[118];
    static const char qemu_nonce_placeholder[] =
        "SIMPLEOS_QEMU_NONCE=__SIMPLEOS_QEMU_NONCE_SLOT_V1__\n";
    memcpy(qemu_nonce_slot_data, qemu_nonce_placeholder,
           sizeof(qemu_nonce_placeholder) - 1U);
    struct bytes qemu_nonce_slot = {qemu_nonce_slot_data, sizeof(qemu_nonce_slot_data)};
    static unsigned char collector_nonce_slot_data[118];
    static const char collector_nonce_placeholder[] =
        "SOSIX_COLLECTOR_RUN_NONCE=__SOSIX_COLLECTOR_RUN_NONCE_SLOT_V1__\n";
    memcpy(collector_nonce_slot_data, collector_nonce_placeholder,
           sizeof(collector_nonce_placeholder) - 1U);
    struct bytes collector_nonce_slot = {
        collector_nonce_slot_data, sizeof(collector_nonce_slot_data)};
    struct bytes numbers_txt = text_bytes("5\n");
    struct bytes hello_spl = text_bytes("fn main() -> i64:\n    print \"Hello from SimpleOS\"\n    return 0\n");
    struct bytes nvfs = textf("nvfs-image-version=1\nplatform=%s\nlane=%s\n", platform, lane);
    struct bytes toolset = textf("lane = \"%s\"\nmode=native-filesystem-app\nstatus=standalone-required\n", lane);
    struct bytes simple_tool_manifest = textf(
        "[simple_toolchain]\nstatus = \"embedded\"\n"
        "host_payload = \"%s\"\nbuild_stamp = \"%s.build_stamp\"\n"
        "runtime_source = \"simpleos-filesystem\"\n"
        "role = \"/usr/bin/simple\"\nrole = \"/usr/bin/simple.smf\"\n"
        "role = \"/bin/simple\"\nrole = \"/bin/simple.smf\"\n"
        "role = \"/sys/apps/simple\"\nrole = \"/sys/apps/simple.smf\"\n"
        "role = \"/sys/apps/simple_compiler\"\nrole = \"/sys/apps/simple_compiler.smf\"\n"
        "role = \"/sys/apps/simple_interpreter\"\nrole = \"/sys/apps/simple_interpreter.smf\"\n"
        "role = \"/sys/apps/simple_loader\"\nrole = \"/sys/apps/simple_loader.smf\"\n",
        getenv("SIMPLEOS_SIMPLE_BINARY") ? getenv("SIMPLEOS_SIMPLE_BINARY") : "",
        getenv("SIMPLEOS_SIMPLE_BINARY") ? getenv("SIMPLEOS_SIMPLE_BINARY") : "");
    struct bytes markers = textf(
        "\nHELLOSMF\nBROWSMF\nSBROWSMF\nSMUXSMF\nSCOMPSMF\nSINTSMF\nSLOADSMF\nSIMPLSTC\nLLVMSMF\nCLANGSMF\nRUSTSMF\nSTEAM204SMF\n"
        "[steam-2048-demo] source=2048\n[game-port] profile=steamos-rebuild-v1 source=2048\nrebuild_target=simpleos-native\n"
        "steam_facade=simple-steam-sffi-v1\nport_required_capabilities=8\nruntime=SteamLinuxRuntime/soldier\nnetwork=true\nachievement=true\ndrm=true\n"
        "steam_backend_ready=false\nsteam_backend_blocker=missing_authenticated_steam_client\nsteam_backend_required_symbols=20\nsteam_backend_required_os_capabilities=11\n"
        "SMF\n/sys/apps/hello_world\n/sys/apps/simple_browser\n/sys/apps/smux\nSIMPLEOS_DISK_HELLO_ELF\nbrowser_demo_remote_main\nhello_world_remote_main\n"
        "file_manager_remote_main\nshell_remote_main\neditor_remote_main\nsmux_remote_main\ninfo|src/app/info/main.spl|smoke|staged\nlist|src/app/list/main.spl|smoke|staged\n"
        "stats|src/app/stats/main.spl|smoke|staged\nentry_app=/sys/apps/simple\nentry_app=/usr/bin/simple\nentry_app=/sys/apps/simple_compiler\nentry_app=/sys/apps/simple_interpreter\nentry_app=/sys/apps/simple_loader\nentry_app=/sys/apps/llvm\nentry_app=/sys/apps/clang\nentry_app=/sys/apps/rust\n"
        "lane=%s\nlane = \"%s\"\nelf-machine=%s\nmode=native-filesystem-app\nstatus=standalone-required\npipeline=compile-pipeline-step\npipeline=build-pipeline-step\n"
        "proof_pipeline=/usr/share/simpleos/toolchain/llvm/pipeline.step\nproof_pipeline=/usr/share/simpleos/toolchain/clang/pipeline.step\nproof_pipeline=/usr/share/simpleos/toolchain/rust/pipeline.step\n"
        "/usr/share/simpleos/toolchain/llvm/hello.ll\n/usr/bin/simple status=standalone-required\n/sys/apps/simple status=standalone-required\n/sys/apps/simple_compiler status=standalone-required\n/sys/apps/simple_interpreter status=standalone-required\n/sys/apps/simple_loader status=standalone-required\n/sys/apps/llvm status=standalone-required\n"
        "/sys/apps/clang status=standalone-required\n/sys/apps/rust status=standalone-required\nSimpleOS LLVM standalone app v1\nclang version 20.0.0\nSimpleOS Rust standalone app v1\n"
        "/usr/share/simpleos/toolchain/llvm/pipeline.step\n/usr/share/simpleos/toolchain/clang/pipeline.step\n/usr/share/simpleos/toolchain/rust/pipeline.step\n"
        "SIMPLEOS_FONT_ASSET_COUNT=16\nSIMPLEOS_FONT_BUNDLE_COUNT=53\nSIMPLEOS_FONT_ASSET_PATH=/SYS/FONTS/NOTOSANS\nSIMPLEOS_FONT_NOTICES_PATH=/SYS/FONTS/NOTICES.MD\n",
        lane, lane, platform);

    struct bytes llvm_manifest = textf("[toolchain]\napp=llvm\ntitle=LLVM\ntool=/sys/apps/llvm\nlane=%s\nmode=native-filesystem-app\nstatus=standalone-required\ncapability_primary=local-ir-inspection\nproof_primary=/usr/share/simpleos/toolchain/llvm/hello.ll\ncapability_secondary=object-assembly-inspection\nproof_secondary=/usr/share/simpleos/toolchain/llvm/hello.s\npipeline=compile-pipeline-step\nproof_pipeline=/usr/share/simpleos/toolchain/llvm/pipeline.step\n", lane);
    struct bytes clang_manifest = textf("[toolchain]\napp=clang\ntitle=Clang\ntool=/sys/apps/clang\nlane=%s\nmode=native-filesystem-app\nstatus=standalone-required\ncapability_primary=local-c-source-inspection\nproof_primary=/usr/share/simpleos/toolchain/clang/hello.c\ncapability_secondary=driver-flag-inspection\nproof_secondary=/usr/share/simpleos/toolchain/clang/flags.rsp\npipeline=compile-pipeline-step\nproof_pipeline=/usr/share/simpleos/toolchain/clang/pipeline.step\n", lane);
    struct bytes rust_manifest = textf("[toolchain]\napp=rust\ntitle=Rust\ntool=/sys/apps/rust\nlane=%s\nmode=native-filesystem-app\nstatus=standalone-required\ncapability_primary=local-source-inspection\nproof_primary=/usr/share/simpleos/toolchain/rust/hello.rs\ncapability_secondary=package-layout-inspection\nproof_secondary=/usr/share/simpleos/toolchain/rust/Cargo.toml\npipeline=build-pipeline-step\nproof_pipeline=/usr/share/simpleos/toolchain/rust/pipeline.step\n", lane);
    struct bytes steam_port = text_bytes("port_profile=steamos-rebuild-v1\napp_id=2048\napp_name=SimpleOS Steam 2048 Smoke\nsource=2048\nupstream=https://github.com/gabrielecirulli/2048\nlicense=MIT\nrebuild_target=simpleos-native\nruntime_profile=SteamLinuxRuntime/soldier-source-rebuild\npackage_path=/sys/apps/steam_2048\ngraphics_api=sdl2_subset\ninput_api=simple_input_events\naudio_api=simple_audio_optional\nnetwork_api=simple_bsd_sockets_optional\nstorage_api=simple_posix_save_data\nsteam_facade=simple-steam-sffi-v1\n");
    struct bytes llvm_ll = text_bytes("source_filename = \"hello.simple\"\ndefine i32 @main() { ret i32 0 }\n");
    struct bytes llvm_s = text_bytes(".globl _start\n_start:\n  ret\n");
    struct bytes llvm_pipe = text_bytes("pipeline=compile-pipeline-step\ninput=/work/hello.simple\noutput=/work/hello.ll\nnext=/sys/apps/simple_loader\n");
    struct bytes clang_c = text_bytes("extern int puts(const char *);\nint main(void) { puts(\"Hello World\"); return 0; }\n");
    struct bytes clang_flags = text_bytes("-target x86_64-unknown-simpleos\n-ffreestanding\n-nostdlib\n");
    struct bytes clang_pipe = text_bytes("pipeline=compile-pipeline-step\ninput=/work/hello.c\noutput=/work/hello.o\nnext=/sys/apps/simple_loader\n");
    struct bytes rust_rs = text_bytes("#![no_std]\n#![no_main]\nfn main() {}\n");
    struct bytes rust_cargo = text_bytes("[package]\nname = \"simpleos-hello\"\nversion = \"0.1.0\"\nedition = \"2021\"\n");
    struct bytes rust_pipe = text_bytes("pipeline=build-pipeline-step\ninput=/work/Cargo.toml\noutput=/work/target/hello\nnext=/sys/apps/simple_loader\n");
    struct bytes fat4k = text_bytes("SIMPLEOS_FAT32_DIRECT_IO_4K_FIXTURE\n");

    struct bytes hello = smf(platform_elf(platform, hello_marker));
    struct bytes browser = smf(browser_payload.len ? browser_payload : platform_elf(platform, gui_marker));
    struct bytes simple_cli = simple_role_payload(platform, "SIMPLE", simple_payload);
    struct bytes simple_compiler = simple_role_payload(platform, "SIMPLE_COMPILER", simple_payload);
    struct bytes simple_interpreter = simple_role_payload(platform, "SIMPLE_INTERPRETER", simple_payload);
    struct bytes simple_loader = simple_role_payload(platform, "SIMPLE_LOADER", simple_payload);
    struct bytes llvm_app = app_elf(platform, "LLVM");
    struct bytes clang_app = app_elf(platform, "CLANG");
    struct bytes rust_app = app_elf(platform, "RUST");
    struct bytes steam_app = smf(platform_elf(platform, "[steam-2048-demo] source=2048 runtime=SteamLinuxRuntime/soldier network=true achievement=true drm=true"));

    int kernel_cluster = alloc_clusters(kernel.data, kernel.len);
    int bootloader_cluster = alloc_clusters(bootloader.data, bootloader.len);
    int limine_cluster = alloc_clusters(limine.data, limine.len);
    int hello_txt_cluster = alloc_clusters(hello_txt.data, hello_txt.len);
    int server_document_cluster = servers_payload.len ? alloc_clusters(server_document.data, server_document.len) : 0;
    int server_credential_cluster = servers_payload.len ? alloc_clusters(server_credential.data, server_credential.len) : 0;
    int server_certificate_cluster = servers_payload.len ? alloc_clusters(server_certificate.data, server_certificate.len) : 0;
    int server_private_key_cluster = servers_payload.len ? alloc_clusters(server_private_key.data, server_private_key.len) : 0;
    int server_credentials_manifest_cluster = servers_payload.len ? alloc_clusters(server_credentials_manifest.data, server_credentials_manifest.len) : 0;
    if (servers_payload.len) {
        require_cluster_bytes(server_credential_cluster, server_credential,
                              "SRVDB.KEY staging verification failed");
        require_cluster_bytes(server_certificate_cluster, server_certificate,
                              "SRVDB.CRT staging verification failed");
        require_cluster_bytes(server_private_key_cluster, server_private_key,
                              "SRVDB.PK8 staging verification failed");
        require_cluster_bytes(server_credentials_manifest_cluster, server_credentials_manifest,
                              "SRVDB.MAN staging verification failed");
    }
    /* alloc_clusters copied the secret into the credential-bearing image.
     * Remove the transient host-side read buffer immediately; the resulting
     * image remains sensitive and is governed by the acceptance-image policy. */
    wipe_bytes(server_credential);
    wipe_bytes(server_certificate);
    wipe_bytes(server_private_key);
    int qemu_nonce_cluster = alloc_clusters(qemu_nonce_slot.data, qemu_nonce_slot.len);
    int collector_nonce_cluster = alloc_clusters(
        collector_nonce_slot.data, collector_nonce_slot.len);
    int numbers_cluster = alloc_clusters(numbers_txt.data, numbers_txt.len);
    int hello_spl_cluster = alloc_clusters(hello_spl.data, hello_spl.len);
    int nvfs_cluster = alloc_clusters(nvfs.data, nvfs.len);
    int toolset_cluster = alloc_clusters(toolset.data, toolset.len);
    int simple_tool_manifest_cluster = simple_payload.len ? alloc_clusters(simple_tool_manifest.data, simple_tool_manifest.len) : 0;
    int markers_cluster = alloc_clusters(markers.data, markers.len);
    int llvm_manifest_cluster = alloc_clusters(llvm_manifest.data, llvm_manifest.len);
    int clang_manifest_cluster = alloc_clusters(clang_manifest.data, clang_manifest.len);
    int rust_manifest_cluster = alloc_clusters(rust_manifest.data, rust_manifest.len);
    /* Steam manifest/proof bytes are intentionally not allocated by this disk
     * profile. Earlier code allocated them without publishing directory entries,
     * creating orphan FAT clusters that fsck reclaimed. A future profile that
     * owns Steam proof staging must allocate and publish both artifacts in the
     * same change; this generic filesystem profile keeps the FAT closed now. */
    int steam_port_cluster = alloc_clusters(steam_port.data, steam_port.len);
    int llvm_ll_cluster = alloc_clusters(llvm_ll.data, llvm_ll.len);
    int llvm_s_cluster = alloc_clusters(llvm_s.data, llvm_s.len);
    int llvm_pipe_cluster = alloc_clusters(llvm_pipe.data, llvm_pipe.len);
    /* FAT32 has NO hard links: two directory entries must not share one cluster
     * chain. This payload is deliberately published at two paths (/SYS/CLANGHEL.C
     * via clang_c_cluster and /HELLO.C via hello_c_cluster), and sharing made
     * fsck report "/HELLO.C and /SYS/CLANGHEL.C share clusters. Truncating second
     * to 0 bytes" — one of the two paths then read as empty. Each path gets its
     * own independent copy. */
    int clang_c_cluster = alloc_clusters(clang_c.data, clang_c.len);
    int hello_c_cluster = alloc_clusters(clang_c.data, clang_c.len);
    int work_hello_c_cluster = alloc_clusters(clang_c.data, clang_c.len);
    int clang_flags_cluster = alloc_clusters(clang_flags.data, clang_flags.len);
    int clang_pipe_cluster = alloc_clusters(clang_pipe.data, clang_pipe.len);
    int rust_rs_cluster = alloc_clusters(rust_rs.data, rust_rs.len);
    int rust_cargo_cluster = alloc_clusters(rust_cargo.data, rust_cargo.len);
    int rust_pipe_cluster = alloc_clusters(rust_pipe.data, rust_pipe.len);
    int hello_cluster = alloc_clusters(hello.data, hello.len);
    int browser_cluster = alloc_clusters(browser.data, browser.len);
    int compiler_cluster = alloc_clusters(simple_compiler.data, simple_compiler.len);
    int interpreter_cluster = alloc_clusters(simple_interpreter.data, simple_interpreter.len);
    int loader_cluster = alloc_clusters(simple_loader.data, simple_loader.len);
    int simple_cluster = alloc_clusters(simple_cli.data, simple_cli.len);
    int simple_usr_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    /* Same no-hard-links rule as clang_c_cluster/hello_c_cluster above: this
     * payload is published at /USR/BIN/SIMPLE, /BIN/SIMPLE and /SIMPLE.ELF, so
     * each entry needs its own chain. Every allocation guard here must match the
     * guard on the CONSUMING put_dir_entry, or the chain is allocated in the FAT
     * and never referenced ("Reclaimed N unused clusters"). simple_usr_cluster is
     * non-zero exactly when simple_payload.len is non-zero (cluster numbers start
     * at 2), so the `if (simple_usr_cluster)` consumers below are covered by the
     * `simple_payload.len` guard used here; simple_root_cluster is consumed under
     * its own `if (simple_root_cluster)`. */
    int simple_bin_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_root_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_apps_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_usr_smf_cluster = simple_payload.len ? alloc_clusters(simple_cli.data, simple_cli.len) : 0;
    int simple_bin_smf_cluster = simple_payload.len ? alloc_clusters(simple_cli.data, simple_cli.len) : 0;
    int simple_compiler_raw_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_interpreter_raw_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_loader_raw_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int clang_bin_cluster = clang_payload.len ? alloc_clusters(clang_payload.data, clang_payload.len) : 0;
    int clangxx_bin_cluster = clang_payload.len ? alloc_clusters(clang_payload.data, clang_payload.len) : 0;
    int llc_bin_cluster = llc_payload.len ? alloc_clusters(llc_payload.data, llc_payload.len) : 0;
    int lld_bin_cluster = lld_payload.len ? alloc_clusters(lld_payload.data, lld_payload.len) : 0;
    int llvm_ar_bin_cluster = llvm_ar_payload.len ? alloc_clusters(llvm_ar_payload.data, llvm_ar_payload.len) : 0;
    int crt0_cluster = crt0_payload.len ? alloc_clusters(crt0_payload.data, crt0_payload.len) : 0;
    int runtime_cluster = runtime_payload.len ? alloc_clusters(runtime_payload.data, runtime_payload.len) : 0;
    int libc_cluster = libc_payload.len ? alloc_clusters(libc_payload.data, libc_payload.len) : 0;
    int linker_script_cluster = linker_script_payload.len ? alloc_clusters(linker_script_payload.data, linker_script_payload.len) : 0;
    int simple_entry_cluster = simple_entry_payload.len ? alloc_clusters(simple_entry_payload.data, simple_entry_payload.len) : 0;
    int hello_object_cluster = hello_object_payload.len ? alloc_clusters(hello_object_payload.data, hello_object_payload.len) : 0;
    int hello_ir_cluster = hello_ir_payload.len ? alloc_clusters(hello_ir_payload.data, hello_ir_payload.len) : 0;
    int fsexec_cluster = fsexec_payload.len ? alloc_clusters(fsexec_payload.data, fsexec_payload.len) : 0;
    int authhello_cluster = authhello_payload.len ? alloc_clusters(authhello_payload.data, authhello_payload.len) : 0;
    int authhello_manifest_cluster = authhello_manifest.len ? alloc_clusters(authhello_manifest.data, authhello_manifest.len) : 0;
    int authhello_admission_cluster = authhello_admission.len ? alloc_clusters(authhello_admission.data, authhello_admission.len) : 0;
    int authhello_proof_cluster = authhello_proof.len ? alloc_clusters(authhello_proof.data, authhello_proof.len) : 0;
    int authhello_trust_root_cluster = authhello_trust_root.len ? alloc_clusters(authhello_trust_root.data, authhello_trust_root.len) : 0;
    int servers_cluster = servers_payload.len ? alloc_clusters(servers_payload.data, servers_payload.len) : 0;
    int servers_manifest_cluster = servers_manifest.len ? alloc_clusters(servers_manifest.data, servers_manifest.len) : 0;
    int servers_admission_cluster = servers_admission.len ? alloc_clusters(servers_admission.data, servers_admission.len) : 0;
    int servers_proof_cluster = servers_proof.len ? alloc_clusters(servers_proof.data, servers_proof.len) : 0;
    int servers_trust_root_cluster = servers_trust_root.len ? alloc_clusters(servers_trust_root.data, servers_trust_root.len) : 0;
    int font_clusters[FONT_ASSET_COUNT];
    int font_metadata_clusters[FONT_ASSET_COUNT];
    int font_license_clusters[FONT_ASSET_COUNT];
    for (int i = 0; i < FONT_ASSET_COUNT; ++i) {
        font_clusters[i] = alloc_clusters(font_payloads[i].data, font_payloads[i].len);
        font_metadata_clusters[i] = alloc_clusters(font_metadata_payloads[i].data, font_metadata_payloads[i].len);
        font_license_clusters[i] = alloc_clusters(font_license_payloads[i].data, font_license_payloads[i].len);
    }
    int font_copyright_cluster = alloc_clusters(font_copyright_payload.data, font_copyright_payload.len);
    int font_corpus_cluster = alloc_clusters(font_corpus_payload.data, font_corpus_payload.len);
    int cldr_license_cluster = alloc_clusters(cldr_license_payload.data, cldr_license_payload.len);
    int simple_license_cluster = alloc_clusters(simple_license_payload.data, simple_license_payload.len);
    int third_party_notices_cluster = alloc_clusters(third_party_notices_payload.data, third_party_notices_payload.len);
    int llvm_cluster = alloc_clusters(llvm_app.data, llvm_app.len);
    int clang_cluster = alloc_clusters(clang_app.data, clang_app.len);
    int rust_cluster = alloc_clusters(rust_app.data, rust_app.len);
    int steam_cluster = alloc_clusters(steam_app.data, steam_app.len);
    int cfat4k_cluster = cfat4k.len ? alloc_clusters(cfat4k.data, cfat4k.len) : 0;
    int fat4k_cluster = alloc_clusters(fat4k.data, fat4k.len);
    int theme_cluster = theme_payload.len ? alloc_clusters(theme_payload.data, theme_payload.len) : 0;

    /* `tmp` was once the one directory given a cluster and a root entry but NO
     * content buffer, so its cluster was never written and fsck reported
     * "/TMP Expected a valid '.' entry in the first slot, found free entry".
     * Every directory declared here must also get dot entries below AND a
     * write_directory() call at the end — TMP was the sole gap. */
    unsigned char root[DIRECTORY_BYTES] = {0}, efi[DIRECTORY_BYTES] = {0};
    unsigned char boot[DIRECTORY_BYTES] = {0}, sys[DIRECTORY_BYTES] = {0};
    unsigned char fonts[DIRECTORY_BYTES] = {0}, apps[DIRECTORY_BYTES] = {0};
    unsigned char perf[DIRECTORY_BYTES] = {0}, usr[DIRECTORY_BYTES] = {0};
    unsigned char usr_bin[DIRECTORY_BYTES] = {0}, usr_lib[DIRECTORY_BYTES] = {0};
    unsigned char bin[DIRECTORY_BYTES] = {0}, sysrt[DIRECTORY_BYTES] = {0};
    unsigned char tmp[DIRECTORY_BYTES] = {0};
    unsigned char work[DIRECTORY_BYTES] = {0};
    int root_n = 0, efi_n = 0, boot_n = 0, sys_n = 0, fonts_n = 0;
    int apps_n = 0, perf_n = 0, usr_n = 0, usr_bin_n = 0, usr_lib_n = 0;
    int bin_n = 0, sysrt_n = 0, tmp_n = 0;
    int work_n = 0;
    put_dir_entry(root, &root_n, "SIMPLEOS   ", 0, 0, 0x08);
    put_dir_entry(root, &root_n, "EFI        ", efi_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "SYS        ", sys_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "USR        ", usr_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "BIN        ", bin_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "SYSRT      ", sysrt_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "TMP        ", tmp_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "WORK       ", work_cluster, 0, 0x10);
    if (theme_cluster)
        put_dir_entry(root, &root_n, "THEME   CSS", theme_cluster, theme_payload.len, 0x20);
    /* Lane BA: root-level staging of the cross-built interpreter so the arm64
     * board gate reads it via the proven root directory-scan path (avoids the
     * /SYS/APPS subdirectory descent). Placed early so the dirent stays within
     * the first 512-byte directory sector. */
    if (simple_root_cluster)
        put_dir_entry(root, &root_n, "SIMPLE  ELF", simple_root_cluster, simple_payload.len, 0x20);
    put_dir_entry(root, &root_n, "KERNEL  ELF", kernel_cluster, kernel.len, 0x20);
    put_dir_entry(root, &root_n, "LIMINE  CNF", limine_cluster, limine.len, 0x20);
    put_dir_entry(root, &root_n, "HELLO   TXT", hello_txt_cluster, hello_txt.len, 0x20);
    put_dir_entry(root, &root_n, "QEMUNONCTXT", qemu_nonce_cluster, qemu_nonce_slot.len, 0x20);
    put_dir_entry(root, &root_n, "SOSIXNONTXT", collector_nonce_cluster,
                  collector_nonce_slot.len, 0x20);
    put_dir_entry(root, &root_n, "NUMBERS TXT", numbers_cluster, numbers_txt.len, 0x20);
    put_dir_entry(root, &root_n, "HELLO   SPL", hello_spl_cluster, hello_spl.len, 0x20);
    put_dir_entry(root, &root_n, "HELLO   C  ", hello_c_cluster, clang_c.len, 0x20);
    if (hello_object_cluster)
        put_dir_entry(root, &root_n, "HELLO   O  ", hello_object_cluster, hello_object_payload.len, 0x20);
    if (hello_ir_cluster)
        put_dir_entry(root, &root_n, "HELLO   LL ", hello_ir_cluster, hello_ir_payload.len, 0x20);
    if (fsexec_cluster)
        put_dir_entry(root, &root_n, "FSEXEC  ELF", fsexec_cluster, fsexec_payload.len, 0x20);
    if (authhello_cluster) {
        put_named_dir_entry(apps, &apps_n, "AUTHHELELF ", "AUTHHELLO.ELF",
                            authhello_cluster, authhello_payload.len, 0x20);
        put_dir_entry(root, &root_n, "AUTHHEL MAN", authhello_manifest_cluster, authhello_manifest.len, 0x20);
        put_dir_entry(root, &root_n, "AUTHHEL ADM", authhello_admission_cluster, authhello_admission.len, 0x20);
        put_dir_entry(root, &root_n, "AUTHHEL SIG", authhello_proof_cluster, authhello_proof.len, 0x20);
        put_dir_entry(root, &root_n, "AUTHHEL PUB", authhello_trust_root_cluster, authhello_trust_root.len, 0x20);
    }
    if (servers_cluster) {
        put_dir_entry(root, &root_n, "SERVERS ELF", servers_cluster, servers_payload.len, 0x20);
        if (servers_manifest_cluster) {
            put_dir_entry(root, &root_n, "SERVER  MAN", servers_manifest_cluster, servers_manifest.len, 0x20);
            put_dir_entry(root, &root_n, "SERVER  ADM", servers_admission_cluster, servers_admission.len, 0x20);
            put_dir_entry(root, &root_n, "SERVER  SIG", servers_proof_cluster, servers_proof.len, 0x20);
            put_dir_entry(root, &root_n, "SERVER  PUB", servers_trust_root_cluster, servers_trust_root.len, 0x20);
        }
    }
    put_dot_entries(efi, &efi_n, efi_cluster, 0);
    put_dot_entries(boot, &boot_n, boot_cluster, efi_cluster);
    put_dot_entries(sys, &sys_n, sys_cluster, 0);
    put_dot_entries(fonts, &fonts_n, fonts_cluster, sys_cluster);
    put_dot_entries(apps, &apps_n, apps_cluster, sys_cluster);
    put_dot_entries(work, &work_n, work_cluster, 0);
    put_dir_entry(work, &work_n, "HELLO   C  ", work_hello_c_cluster, clang_c.len, 0x20);
    put_dot_entries(perf, &perf_n, perf_cluster, sys_cluster);
    put_dot_entries(usr, &usr_n, usr_cluster, 0);
    put_dot_entries(usr_bin, &usr_bin_n, usr_bin_cluster, usr_cluster);
    put_dot_entries(usr_lib, &usr_lib_n, usr_lib_cluster, usr_cluster);
    put_dot_entries(bin, &bin_n, bin_cluster, 0);
    put_dot_entries(sysrt, &sysrt_n, sysrt_cluster, 0);
    put_dot_entries(tmp, &tmp_n, tmp_cluster, 0);
    put_dir_entry(efi, &efi_n, "BOOT       ", boot_cluster, 0, 0x10);
    put_dir_entry(boot, &boot_n, "BOOTX64 EFI", bootloader_cluster, bootloader.len, 0x20);
    put_dir_entry(sys, &sys_n, "APPS       ", apps_cluster, 0, 0x10);
    put_dir_entry(sys, &sys_n, "PERF       ", perf_cluster, 0, 0x10);
    put_dir_entry(sys, &sys_n, "FONTS      ", fonts_cluster, 0, 0x10);
    if (servers_payload.len) {
        put_dir_entry(sys, &sys_n, "SERVER  HTM", server_document_cluster, server_document.len, 0x20);
        put_dir_entry(sys, &sys_n, "SRVDB   KEY", server_credential_cluster, server_credential.len, 0x20);
        put_dir_entry(sys, &sys_n, "SRVDB   CRT", server_certificate_cluster, server_certificate.len, 0x20);
        put_dir_entry(sys, &sys_n, "SRVDB   PK8", server_private_key_cluster, server_private_key.len, 0x20);
        put_dir_entry(sys, &sys_n, "SRVDB   MAN", server_credentials_manifest_cluster, server_credentials_manifest.len, 0x20);
    }
    for (int i = 0; i < FONT_ASSET_COUNT; ++i) {
        put_named_dir_entry(fonts, &fonts_n, font_fat_names[i], font_long_names[i],
                            font_clusters[i], font_payloads[i].len, 0x20);
        char metadata_name[12], license_name[12];
        font_companion_fat_name(metadata_name, font_fat_names[i], "PB");
        font_companion_fat_name(license_name, font_fat_names[i], i == 12 ? "LIC" : "OFL");
        put_dir_entry(fonts, &fonts_n, metadata_name,
                      font_metadata_clusters[i], font_metadata_payloads[i].len, 0x20);
        put_dir_entry(fonts, &fonts_n, license_name,
                      font_license_clusters[i], font_license_payloads[i].len, 0x20);
    }
    char copyright_name[12];
    font_companion_fat_name(copyright_name, font_fat_names[12], "CPY");
    put_dir_entry(fonts, &fonts_n, copyright_name,
                  font_copyright_cluster, font_copyright_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "CORPUS  SDN",
                  font_corpus_cluster, font_corpus_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "CLDR    LIC",
                  cldr_license_cluster, cldr_license_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "SIMPLE  LIC",
                  simple_license_cluster, simple_license_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "NOTICES MD ",
                  third_party_notices_cluster, third_party_notices_payload.len, 0x20);
    /* 93 = 91 font-bundle entries + the 2 mandatory FAT32 dot entries. Guard
     * kept; only the expected total moved, by exactly 2. */
    if (fonts_n != 93)
        die("SimpleOS font bundle directory manifest mismatch");
    put_dir_entry(sys, &sys_n, "NVFSVER TXT", nvfs_cluster, nvfs.len, 0x20);
    put_dir_entry(sys, &sys_n, "TOOLSET SDN", toolset_cluster, toolset.len, 0x20);
    if (simple_tool_manifest_cluster)
        put_named_dir_entry(sys, &sys_n, "SIMPLETOSDN", "SIMPLETOOL.SDN",
                            simple_tool_manifest_cluster, simple_tool_manifest.len, 0x20);
    put_dir_entry(sys, &sys_n, "MARKERS TXT", markers_cluster, markers.len, 0x20);
    put_dir_entry(sys, &sys_n, "LLVMMAN TXT", llvm_manifest_cluster, llvm_manifest.len, 0x20);
    put_dir_entry(sys, &sys_n, "CLANGMANTXT", clang_manifest_cluster, clang_manifest.len, 0x20);
    put_dir_entry(sys, &sys_n, "RUSTMAN TXT", rust_manifest_cluster, rust_manifest.len, 0x20);
    put_dir_entry(sys, &sys_n, "ST204PRTTXT", steam_port_cluster, steam_port.len, 0x20);
    put_dir_entry(sys, &sys_n, "LLVHELLOLL ", llvm_ll_cluster, llvm_ll.len, 0x20);
    put_dir_entry(sys, &sys_n, "LLVMPIPESTP", llvm_pipe_cluster, llvm_pipe.len, 0x20);
    put_dir_entry(sys, &sys_n, "LLVMHELLS  ", llvm_s_cluster, llvm_s.len, 0x20);
    put_dir_entry(sys, &sys_n, "CLANGHELC  ", clang_c_cluster, clang_c.len, 0x20);
    put_dir_entry(sys, &sys_n, "CLANGFLGRSP", clang_flags_cluster, clang_flags.len, 0x20);
    put_dir_entry(sys, &sys_n, "CLANGPLNSTP", clang_pipe_cluster, clang_pipe.len, 0x20);
    put_dir_entry(sys, &sys_n, "RUSTHELORS ", rust_rs_cluster, rust_rs.len, 0x20);
    put_dir_entry(sys, &sys_n, "RUSTCARGTOM", rust_cargo_cluster, rust_cargo.len, 0x20);
    put_dir_entry(sys, &sys_n, "RUSTPIPESTP", rust_pipe_cluster, rust_pipe.len, 0x20);
    put_dir_entry(apps, &apps_n, "HELLOSMFSMF", hello_cluster, hello.len, 0x20);
    put_dir_entry(apps, &apps_n, "BROWSMF SMF", browser_cluster, browser.len, 0x20);
    put_named_dir_entry(apps, &apps_n, "SCOMPSMFSMF", "simple_compiler.smf", compiler_cluster, simple_compiler.len, 0x20);
    put_named_dir_entry(apps, &apps_n, "SINTSMF SMF", "simple_interpreter.smf", interpreter_cluster, simple_interpreter.len, 0x20);
    put_named_dir_entry(apps, &apps_n, "SLOADSMFSMF", "simple_loader.smf", loader_cluster, simple_loader.len, 0x20);
    put_named_dir_entry(apps, &apps_n, "SIMPLSTCSMF", "simple.smf", simple_cluster, simple_cli.len, 0x20);
    put_dir_entry(usr, &usr_n, "BIN        ", usr_bin_cluster, 0, 0x10);
    put_dir_entry(usr, &usr_n, "LIB        ", usr_lib_cluster, 0, 0x10);
    if (simple_usr_cluster) {
        put_dir_entry(usr_bin, &usr_bin_n, "SIMPLE     ", simple_usr_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(usr_bin, &usr_bin_n, "SIMPLE  SMF", "simple.smf", simple_usr_smf_cluster, simple_cli.len, 0x20);
        put_dir_entry(bin, &bin_n, "SIMPLE     ", simple_bin_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(bin, &bin_n, "SIMPLE  SMF", "simple.smf", simple_bin_smf_cluster, simple_cli.len, 0x20);
        put_dir_entry(apps, &apps_n, "SIMPLE     ", simple_apps_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(apps, &apps_n, "SCOMPILER  ", "simple_compiler", simple_compiler_raw_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(apps, &apps_n, "SINTERP    ", "simple_interpreter", simple_interpreter_raw_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(apps, &apps_n, "SLOADER    ", "simple_loader", simple_loader_raw_cluster, simple_payload.len, 0x20);
    }
    if (clang_bin_cluster)
        put_dir_entry(usr_bin, &usr_bin_n, "CLANG      ", clang_bin_cluster, clang_payload.len, 0x20);
    if (clangxx_bin_cluster)
        put_named_dir_entry(usr_bin, &usr_bin_n, "CLANGXX    ", "clang++", clangxx_bin_cluster, clang_payload.len, 0x20);
    if (llc_bin_cluster)
        put_dir_entry(usr_bin, &usr_bin_n, "LLC        ", llc_bin_cluster, llc_payload.len, 0x20);
    if (lld_bin_cluster)
        put_dir_entry(usr_bin, &usr_bin_n, "LD      LLD", lld_bin_cluster, lld_payload.len, 0x20);
    if (llvm_ar_bin_cluster)
        put_named_dir_entry(usr_bin, &usr_bin_n, "LLVMAR     ", "llvm-ar", llvm_ar_bin_cluster, llvm_ar_payload.len, 0x20);
    if (crt0_cluster)
        put_named_dir_entry(usr_lib, &usr_lib_n, "CRT0    O  ", "crt0.o", crt0_cluster, crt0_payload.len, 0x20);
    if (runtime_cluster)
        put_named_dir_entry(usr_lib, &usr_lib_n, "SIMPRT  A  ", "libsimpleos_runtime.a", runtime_cluster, runtime_payload.len, 0x20);
    if (libc_cluster)
        put_named_dir_entry(usr_lib, &usr_lib_n, "SOSLIB  A  ", "libsimpleos_c.a", libc_cluster, libc_payload.len, 0x20);
    if (simple_entry_cluster)
        put_dir_entry(usr_lib, &usr_lib_n, "SIMAIN  O  ", simple_entry_cluster, simple_entry_payload.len, 0x20);
    if (linker_script_cluster)
        put_named_dir_entry(sysrt, &sysrt_n, "SIMPLEOSLD ", "simpleos.ld", linker_script_cluster, linker_script_payload.len, 0x20);
    put_dir_entry(apps, &apps_n, "LLVMSMF SMF", llvm_cluster, llvm_app.len, 0x20);
    put_dir_entry(apps, &apps_n, "CLANGSMFSMF", clang_cluster, clang_app.len, 0x20);
    put_dir_entry(apps, &apps_n, "RUSTSMF SMF", rust_cluster, rust_app.len, 0x20);
    put_dir_entry(apps, &apps_n, "STEAM204SMF", steam_cluster, steam_app.len, 0x20);
    if (cfat4k.len)
        put_dir_entry(perf, &perf_n, "CFAT4K  TXT", cfat4k_cluster, cfat4k.len, 0x20);
    put_dir_entry(perf, &perf_n, "FAT4K   BIN", fat4k_cluster, fat4k.len, 0x20);

    write_directory(ROOT_CLUSTER, root, root_n);
    write_directory(efi_cluster, efi, efi_n);
    write_directory(boot_cluster, boot, boot_n);
    write_directory(sys_cluster, sys, sys_n);
    write_directory(fonts_cluster, fonts, fonts_n);
    write_directory(apps_cluster, apps, apps_n);
    write_directory(perf_cluster, perf, perf_n);
    write_directory(usr_cluster, usr, usr_n);
    write_directory(usr_bin_cluster, usr_bin, usr_bin_n);
    write_directory(usr_lib_cluster, usr_lib, usr_lib_n);
    write_directory(bin_cluster, bin, bin_n);
    write_directory(sysrt_cluster, sysrt, sysrt_n);
    write_directory(tmp_cluster, tmp, tmp_n);
    write_directory(work_cluster, work, work_n);

    finish_fat32_image(img_path);
    if (servers_payload.len) {
#ifdef _WIN32
        die("server credential staging requires a no-reparse Windows descriptor owner");
#else
        const char *receipt_path = getenv("SIMPLEOS_SERVER_CREDENTIAL_STAGING_RECEIPT");
        if (!receipt_path || receipt_path[0] == '\0')
            die("server credential staging receipt path is required");
        int receipt_fd = open(receipt_path,
                              O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW,
                              S_IRUSR | S_IWUSR);
        if (receipt_fd < 0)
            die("server credential staging receipt creation failed");
        FILE *receipt = fdopen(receipt_fd, "w");
        if (!receipt)
            die("server credential staging receipt stream failed");
        fprintf(receipt, "schema=simpleos-server-credential-staging-v1\n");
        fprintf(receipt, "credential_offset=%zu\ncredential_length=%zu\n",
                cluster_offset(server_credential_cluster), server_credential.len);
        fprintf(receipt, "certificate_offset=%zu\ncertificate_length=%zu\n",
                cluster_offset(server_certificate_cluster), server_certificate.len);
        fprintf(receipt, "private_key_offset=%zu\nprivate_key_length=%zu\n",
                cluster_offset(server_private_key_cluster), server_private_key.len);
        fprintf(receipt, "manifest_offset=%zu\nmanifest_length=%zu\n",
                cluster_offset(server_credentials_manifest_cluster), server_credentials_manifest.len);
        if (fclose(receipt) != 0)
            die("server credential staging receipt write failed");
#endif
    }
    if (strcmp(platform, "x86_64") == 0 && bootloader_file.len)
        maybe_write_esp(img_path, &bootloader, &kernel, &limine);
    return 0;
}
