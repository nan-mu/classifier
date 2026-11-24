use std::io::{self, Read};

use serde_json::{json, Value};
use xpost_elf::{
    build_container_with_limit, scan_at, ImageMetadataV0, MapDescriptorV0, ScanOutcome,
};

// The libbpf-mcu v0.1.0 host profile permits 8 KiB files.
const RELEASE_LIMIT: usize = 8192;

fn inspect(bytes: &[u8]) -> Result<Value, &'static str> {
    if bytes.len() > RELEASE_LIMIT {
        return Err("Compact ELF exceeds the size limit");
    }
    let ScanOutcome::Ok(container) = scan_at(&mut &bytes[..], 0) else {
        return Err("invalid Compact ELF format or image digest");
    };
    if container.file_len != bytes.len() {
        return Err("trailing bytes after Compact ELF");
    }

    let image = &bytes[container.image_offset..container.image_offset + container.image_size];
    let metadata = ImageMetadataV0 {
        slot_address: container.slot_address as u32,
        helper_address: container.helper_address as u32,
        machine: 1,
        name: container.name.clone(),
        maps: container
            .maps
            .iter()
            .map(|map| MapDescriptorV0 {
                name: map.name.clone(),
                map_type: map.map_type,
                len: map.len,
                map_vma: map.vma,
                key_layout: map.key.clone(),
                value_layout: map.value.clone(),
            })
            .collect(),
    };
    // The cold scanner verifies the image digest and the metadata it consumes.
    // The release format additionally requires canonical ELF headers and padding.
    let canonical = build_container_with_limit::<RELEASE_LIMIT>(image, &metadata, None)
        .map_err(|_| "invalid Compact ELF metadata")?;
    if canonical.as_slice() != bytes {
        return Err("noncanonical Compact ELF headers, sections or padding");
    }

    let maps: Vec<_> = container
        .maps
        .iter()
        .map(|map| {
            json!({
                "name": map.name.as_str(),
                "type": map.map_type,
                "capacity": map.len,
                "vma": map.vma,
                "key_bytes": map.key.as_ref().map_or(4, |layout| layout_bytes(layout)),
                "value_bytes": map.value.as_ref().map_or(0, |layout| layout_bytes(layout)),
            })
        })
        .collect();

    Ok(json!({
        "inspector_version": env!("CARGO_PKG_VERSION"),
        "name": container.name.as_str(),
        "slot_address": container.slot_address,
        "helper_address": container.helper_address,
        "image": image,
        "maps": maps,
    }))
}

fn layout_bytes(layout: &[u8]) -> usize {
    layout.iter().map(|&bits| usize::from(bits)).sum::<usize>() / 8
}

fn main() -> Result<(), String> {
    let mut bytes = Vec::new();
    io::stdin()
        .take(RELEASE_LIMIT as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|err| err.to_string())?;
    println!("{}", inspect(&bytes)?);
    Ok(())
}
