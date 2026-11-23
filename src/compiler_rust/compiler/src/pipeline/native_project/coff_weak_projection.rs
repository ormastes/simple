//! PE/COFF weak definitions need an undefined alias with a fallback auxiliary
//! record. GNU objcopy's section-defined WEAK_EXTERNAL without aux is not that
//! representation (and is rejected by PE LLD).
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

fn u16_at(b: &[u8], p: usize) -> Result<u16, String> {
    Ok(u16::from_le_bytes(b.get(p..p + 2).ok_or("truncated COFF u16")?.try_into().unwrap()))
}
fn u32_at(b: &[u8], p: usize) -> Result<u32, String> {
    Ok(u32::from_le_bytes(b.get(p..p + 4).ok_or("truncated COFF u32")?.try_into().unwrap()))
}

pub(crate) fn project(path: &Path, requested: &BTreeSet<String>) -> Result<(), String> {
    if requested.is_empty() { return Ok(()); }
    let input = std::fs::read(path).map_err(|e| e.to_string())?;
    let output = project_bytes(&input, requested)?;
    std::fs::write(path, output).map_err(|e| e.to_string())
}

/// GNU objcopy leaves defined weak aliases global even when asked to localize
/// them. Bind those private aliases directly to their existing fallback body.
pub(crate) fn localize_weak(path: &Path, requested: &BTreeSet<String>) -> Result<(), String> {
    if requested.is_empty() { return Ok(()); }
    let input = std::fs::read(path).map_err(|e| e.to_string())?;
    if !matches!(u16_at(&input, 0)?, 0x8664 | 0x14c) || u16_at(&input, 16)? != 0 {
        return Err("weak localization requires ordinary x86/x64 COFF".into());
    }
    let sections = u16_at(&input, 2)? as usize;
    let table = u32_at(&input, 8)? as usize;
    let count = u32_at(&input, 12)? as usize;
    let end = table.checked_add(count.checked_mul(18).ok_or("COFF symbol overflow")?).ok_or("COFF table overflow")?;
    let string_size = u32_at(&input, end)? as usize;
    if string_size < 4 || end.checked_add(string_size) != Some(input.len()) || table < 20 + sections * 40 {
        return Err("unsupported COFF localization table bounds".into());
    }
    let strings = &input[end..];
    let mut primary = BTreeSet::new();
    let mut index = 0;
    while index < count {
        primary.insert(index);
        index += 1 + input[table + index * 18 + 17] as usize;
        if index > count { return Err("truncated COFF auxiliary records".into()); }
    }
    let mut output = input.clone();
    let mut vacated = BTreeSet::new();
    for index in &primary {
        let pos = table + index * 18;
        let record = &input[pos..pos + 18];
        if record[16] != 105 { continue; }
        let name_bytes = if u32_at(record, 0)? == 0 {
            let offset = u32_at(record, 4)? as usize;
            if offset < 4 { return Err("invalid COFF name offset".into()); }
            strings.get(offset..).ok_or("invalid COFF name offset")?
        } else { &record[..8] };
        let length = name_bytes.iter().position(|b| *b == 0).unwrap_or(name_bytes.len());
        let name = std::str::from_utf8(&name_bytes[..length]).map_err(|_| "non-UTF8 COFF symbol")?;
        if !requested.contains(name) { continue; }
        if u16_at(record, 12)? != 0 || record[17] != 1 {
            return Err(format!("invalid private COFF weak alias {name}"));
        }
        let fallback_index = u32_at(&input, pos + 18)? as usize;
        if !primary.contains(&fallback_index) { return Err("COFF private fallback is not a primary symbol".into()); }
        let fallback = &input[table + fallback_index * 18..table + (fallback_index + 1) * 18];
        let section = u16_at(fallback, 12)? as i16;
        if section <= 0 || section as usize > sections || !matches!(fallback[16], 2 | 3) {
            return Err(format!("private COFF weak alias {name} has no defined fallback"));
        }
        output[pos + 8..pos + 16].copy_from_slice(&fallback[8..16]);
        output[pos + 16] = 3; // STATIC at the existing body's address
        output[pos + 17] = 0;
        output[pos + 18..pos + 36].fill(0);
        // A private absolute-zero symbol is a valid inert record (the same
        // shape as Clang's @feat.00). NULL/UNDEFINED is rejected by PE LLD.
        output[pos + 18..pos + 22].copy_from_slice(b".pad");
        output[pos + 30..pos + 32].copy_from_slice(&(-1i16).to_le_bytes());
        output[pos + 34] = 3; // STATIC, ABSOLUTE, no auxiliary records
        vacated.insert(index + 1);
    }
    for index in &primary {
        let pos = table + index * 18;
        if input[pos + 16] == 105 && input[pos + 17] > 0
            && vacated.contains(&(u32_at(&input, pos + 18)? as usize)) {
            return Err("COFF weak alias references a vacated auxiliary index".into());
        }
    }
    for section in 0..sections {
        let header = 20 + section * 40;
        let offset = u32_at(&input, header + 24)? as usize;
        let mut relocations = u16_at(&input, header + 32)? as usize;
        let first = if u32_at(&input, header + 36)? & 0x01000000 != 0 {
            if relocations != 0xffff { return Err("invalid COFF relocation overflow".into()); }
            relocations = u32_at(&input, offset)? as usize;
            1
        } else { 0 };
        if relocations > 0 && (offset < 20 + sections * 40 || offset.checked_add(relocations.checked_mul(10).ok_or("COFF relocation overflow")?).is_none_or(|end| end > table)) {
            return Err("unsupported COFF relocation bounds".into());
        }
        for relocation in first..relocations {
            if vacated.contains(&(u32_at(&input, offset + relocation * 10 + 4)? as usize)) {
                return Err("COFF relocation references a vacated auxiliary index".into());
            }
        }
    }
    std::fs::write(path, output).map_err(|e| e.to_string())
}

fn project_bytes(input: &[u8], requested: &BTreeSet<String>) -> Result<Vec<u8>, String> {
    if !matches!(u16_at(input, 0)?, 0x8664 | 0x14c) || u16_at(input, 16)? != 0 {
        return Err("weak projection requires ordinary x86/x64 COFF object".into());
    }
    let sections = u16_at(input, 2)? as usize;
    let table = u32_at(input, 8)? as usize;
    let count = u32_at(input, 12)? as usize;
    let end = table.checked_add(count.checked_mul(18).ok_or("COFF symbol overflow")?).ok_or("COFF table overflow")?;
    let string_size = u32_at(input, end)? as usize;
    if string_size < 4 || end.checked_add(string_size) != Some(input.len()) || table < 20 + sections * 40 {
        return Err("unsupported COFF symbol/string table bounds".into());
    }
    let mut body = input[..end].to_vec();
    let mut strings = input[end..].to_vec();
    let mut appended = Vec::new();
    let mut redirects = BTreeMap::new();
    let mut found = BTreeSet::new();
    let mut index = 0;
    while index < count {
        let pos = table + index * 18;
        let record = &input[pos..pos + 18];
        let aux = record[17] as usize;
        if index + 1 + aux > count { return Err("truncated COFF auxiliary records".into()); }
        let name_bytes = if u32_at(record, 0)? == 0 {
            let offset = u32_at(record, 4)? as usize;
            if offset < 4 { return Err("invalid COFF string offset".into()); }
            strings.get(offset..).ok_or("invalid COFF string offset")?
        } else { &record[..8] };
        let length = name_bytes.iter().position(|b| *b == 0).unwrap_or(name_bytes.len());
        let name = std::str::from_utf8(&name_bytes[..length]).map_err(|_| "non-UTF8 COFF symbol")?;
        if requested.contains(name) {
            if !found.insert(name.to_string()) { return Err(format!("duplicate COFF weak provider {name}")); }
            let section = u16_at(record, 12)? as i16;
            if record[16] == 105 {
                if section != 0 || aux != 1 { return Err(format!("invalid existing COFF weak alias {name}")); }
            } else {
                if record[16] != 2 || section <= 0 || section as usize > sections {
                    return Err(format!("COFF weak provider is not a strong definition: {name}"));
                }
                let new_index = count + appended.len() / 18;
                let fallback_name = format!(".weak.{name}.default.simple_projection_{index}");
                let string_offset = u32::try_from(strings.len()).map_err(|_| "COFF string overflow")?;
                strings.extend_from_slice(fallback_name.as_bytes());
                strings.push(0);
                // Preserve the body and every original symbol index. Only the
                // old definition becomes private; public references use alias.
                body[pos..pos + 4].fill(0);
                body[pos + 4..pos + 8].copy_from_slice(&string_offset.to_le_bytes());
                body[pos + 16] = 3; // STATIC
                let mut alias = [0u8; 18];
                alias[..8].copy_from_slice(&record[..8]);
                alias[16] = 105; // WEAK_EXTERNAL, UNDEFINED, value zero
                alias[17] = 1;
                appended.extend_from_slice(&alias);
                let mut fallback = [0u8; 18];
                fallback[..4].copy_from_slice(&(index as u32).to_le_bytes());
                fallback[4..8].copy_from_slice(&3u32.to_le_bytes()); // SEARCH_ALIAS
                appended.extend_from_slice(&fallback);
                redirects.insert(index as u32, new_index as u32);
            }
        }
        index += 1 + aux;
    }
    if &found != requested { return Err("missing requested COFF weak providers".into()); }
    for section in 0..sections {
        let header = 20 + section * 40;
        let offset = u32_at(input, header + 24)? as usize;
        let mut relocations = u16_at(input, header + 32)? as usize;
        let overflow = u32_at(input, header + 36)? & 0x01000000 != 0;
        let first = if overflow {
            if relocations != 0xffff { return Err("invalid COFF relocation overflow".into()); }
            relocations = u32_at(input, offset)? as usize;
            1
        } else { 0 };
        if relocations > 0 && (offset < 20 + sections * 40 || offset.checked_add(relocations.checked_mul(10).ok_or("COFF relocation overflow")?).is_none_or(|end| end > table)) {
            return Err("unsupported COFF relocation bounds".into());
        }
        for relocation in first..relocations {
            let pos = offset + relocation * 10 + 4;
            if let Some(replacement) = redirects.get(&u32_at(input, pos)?) {
                body[pos..pos + 4].copy_from_slice(&replacement.to_le_bytes());
            }
        }
    }
    let new_count = u32::try_from(count + appended.len() / 18).map_err(|_| "COFF symbol overflow")?;
    body[12..16].copy_from_slice(&new_count.to_le_bytes());
    let length = u32::try_from(strings.len()).map_err(|_| "COFF string overflow")?;
    strings[..4].copy_from_slice(&length.to_le_bytes());
    body.extend_from_slice(&appended);
    body.extend_from_slice(&strings);
    Ok(body)
}
