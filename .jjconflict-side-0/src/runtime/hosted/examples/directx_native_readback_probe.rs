fn checksum(pixels: &[u32]) -> i64 {
    let mut sum: i64 = 0;
    for (i, pixel) in pixels.iter().enumerate() {
        sum = (sum + (*pixel as i64) * ((i as i64) + 1)) % 2_147_483_647;
    }
    sum
}

fn emit(status: &str, reason: &str, source: &str, handle: i64, expected: i64, actual: i64) {
    println!("directx_native_readback_status={status}");
    println!("directx_native_readback_reason={reason}");
    println!("directx_native_readback_source={source}");
    println!("directx_native_readback_backend_handle={handle}");
    println!("directx_native_readback_expected_checksum={expected}");
    println!("directx_native_readback_actual_checksum={actual}");
}

#[cfg(not(all(target_os = "windows", feature = "win32-real")))]
fn main() {
    let pixels: [u32; 4] = [0xff112233, 0xff445566, 0xff778899, 0xffaabbcc];
    let expected = checksum(&pixels);
    emit(
        "unavailable",
        "directx-native-readback-requires-windows-win32-real",
        "not_device_readback",
        0,
        expected,
        -1,
    );
}

#[cfg(all(target_os = "windows", feature = "win32-real"))]
mod d3d11_probe {
    use super::checksum;
    use std::ffi::c_void;
    use std::ptr::copy_nonoverlapping;
    use windows::core::Interface;
    use windows::Win32::Foundation::HMODULE;
    use windows::Win32::Graphics::Direct3D::{
        D3D_DRIVER_TYPE_HARDWARE, D3D_FEATURE_LEVEL, D3D_FEATURE_LEVEL_11_0,
    };
    use windows::Win32::Graphics::Direct3D11::{
        D3D11CreateDevice, ID3D11Device, ID3D11DeviceContext, ID3D11Resource, ID3D11Texture2D,
        D3D11_BIND_RENDER_TARGET, D3D11_CPU_ACCESS_READ, D3D11_CREATE_DEVICE_BGRA_SUPPORT,
        D3D11_MAPPED_SUBRESOURCE, D3D11_MAP_READ, D3D11_SDK_VERSION, D3D11_SUBRESOURCE_DATA,
        D3D11_TEXTURE2D_DESC, D3D11_USAGE_DEFAULT, D3D11_USAGE_STAGING,
    };
    use windows::Win32::Graphics::Dxgi::Common::{DXGI_FORMAT_R8G8B8A8_UNORM, DXGI_SAMPLE_DESC};

    pub fn run_readback(pixels: &[u32], width: u32, height: u32) -> Result<(i64, i64), String> {
        if pixels.len() != (width as usize) * (height as usize) {
            return Err("pixel-count-mismatch".to_string());
        }

        unsafe {
            let levels = [D3D_FEATURE_LEVEL_11_0];
            let mut device: Option<ID3D11Device> = None;
            let mut context: Option<ID3D11DeviceContext> = None;
            let mut selected_level = D3D_FEATURE_LEVEL(0);

            D3D11CreateDevice(
                None,
                D3D_DRIVER_TYPE_HARDWARE,
                HMODULE(std::ptr::null_mut()),
                D3D11_CREATE_DEVICE_BGRA_SUPPORT,
                Some(&levels),
                D3D11_SDK_VERSION,
                Some(&mut device),
                Some(&mut selected_level),
                Some(&mut context),
            )
            .map_err(|err| format!("d3d11-create-device:{err:?}"))?;

            let device = device.ok_or_else(|| "d3d11-device-missing".to_string())?;
            let context = context.ok_or_else(|| "d3d11-context-missing".to_string())?;
            let row_pitch = width * 4;
            let slice_pitch = row_pitch * height;
            let desc = D3D11_TEXTURE2D_DESC {
                Width: width,
                Height: height,
                MipLevels: 1,
                ArraySize: 1,
                Format: DXGI_FORMAT_R8G8B8A8_UNORM,
                SampleDesc: DXGI_SAMPLE_DESC {
                    Count: 1,
                    Quality: 0,
                },
                Usage: D3D11_USAGE_DEFAULT,
                BindFlags: D3D11_BIND_RENDER_TARGET.0 as u32,
                CPUAccessFlags: 0,
                MiscFlags: 0,
            };
            let init = D3D11_SUBRESOURCE_DATA {
                pSysMem: pixels.as_ptr() as *const c_void,
                SysMemPitch: row_pitch,
                SysMemSlicePitch: slice_pitch,
            };
            let mut texture: Option<ID3D11Texture2D> = None;
            device
                .CreateTexture2D(&desc, Some(&init), Some(&mut texture))
                .map_err(|err| format!("d3d11-create-render-target:{err:?}"))?;

            let staging_desc = D3D11_TEXTURE2D_DESC {
                Usage: D3D11_USAGE_STAGING,
                BindFlags: 0,
                CPUAccessFlags: D3D11_CPU_ACCESS_READ.0 as u32,
                ..desc
            };
            let mut staging: Option<ID3D11Texture2D> = None;
            device
                .CreateTexture2D(&staging_desc, None, Some(&mut staging))
                .map_err(|err| format!("d3d11-create-staging:{err:?}"))?;

            let texture_resource: ID3D11Resource = texture
                .ok_or_else(|| "d3d11-render-target-missing".to_string())?
                .cast()
                .map_err(|err| format!("d3d11-render-target-cast:{err:?}"))?;
            let staging_resource: ID3D11Resource = staging
                .ok_or_else(|| "d3d11-staging-missing".to_string())?
                .cast()
                .map_err(|err| format!("d3d11-staging-cast:{err:?}"))?;

            context.CopyResource(&staging_resource, &texture_resource);

            let mut mapped = D3D11_MAPPED_SUBRESOURCE::default();
            context
                .Map(&staging_resource, 0, D3D11_MAP_READ, 0, Some(&mut mapped))
                .map_err(|err| format!("d3d11-map-staging:{err:?}"))?;

            let mut readback = vec![0_u32; pixels.len()];
            for row in 0..height as usize {
                let src = (mapped.pData as *const u8).add(row * mapped.RowPitch as usize);
                let dst = readback.as_mut_ptr().add(row * width as usize) as *mut u8;
                copy_nonoverlapping(src, dst, row_pitch as usize);
            }
            context.Unmap(&staging_resource, 0);

            Ok((1, checksum(&readback)))
        }
    }
}

#[cfg(all(target_os = "windows", feature = "win32-real"))]
fn main() {
    let pixels: [u32; 16] = [
        0xff101010, 0xff202020, 0xff303030, 0xff404040, 0xff506070, 0xff607080, 0xff708090,
        0xff8090a0, 0xff90a0b0, 0xffa0b0c0, 0xffb0c0d0, 0xffc0d0e0, 0xffd0e0f0, 0xffe0f0ff,
        0xff112233, 0xff445566,
    ];
    let expected = checksum(&pixels);

    match d3d11_probe::run_readback(&pixels, 4, 4) {
        Ok((handle, actual)) if handle > 0 && actual == expected => emit(
            "pass",
            "directx-native-d3d11-staging-readback-matched",
            "device_readback",
            handle,
            expected,
            actual,
        ),
        Ok((handle, actual)) => emit(
            "fail",
            "directx-native-d3d11-staging-checksum-mismatch",
            "not_device_readback",
            handle,
            expected,
            actual,
        ),
        Err(reason) => emit(
            "unavailable",
            &reason,
            "not_device_readback",
            0,
            expected,
            -1,
        ),
    }
}
