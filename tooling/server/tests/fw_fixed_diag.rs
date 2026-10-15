//! Fixed-ihl firewall: packet-keyed map lookup/write completes on both arches.
use lean_binding::ebpf;
use server::bpf_image;
use server::expand::{Arch, Session};
use server::rv32_image;

const ELF: &[u8] = include_bytes!("../../test/xdp/firewall/firewall.elf");
const BPF: &[u8] = include_bytes!("../../test/xdp/firewall/firewall.bpf.o");

#[test]
fn dump_fixed_firewall() {
    let elf = rv32_image::parse_xdp_elf(ELF).unwrap();
    let mut rv = Session::new("rv", 512, Arch::Rv32imc, "firewall.elf".into(), elf.clone());
    rv.run_all();
    let snap = rv.snapshot();
    assert_eq!(snap.status, "complete", "RV failed={:?} reason={:?}", snap.failed, snap.reason);

    let slots = bpf_image::map_lddw_slots(BPF).unwrap();
    let map = elf.maps.first().expect("map");
    let meta = ebpf::Meta {
        entry: ebpf::Entry::just_tx(),
        resource_locations: slots
            .iter()
            .map(|slot| ebpf::ResourceLocation {
                slot: *slot,
                term: Some(map.map_id.to_string()),
            })
            .collect(),
        maps: elf.maps.clone(),
    };
    let bpf = bpf_image::extract_insn_words(BPF).unwrap();
    let mut eb = Session::new_ebpf("eb", 512, "firewall.bpf.o".into(), bpf, meta);
    eb.run_all();
    let snap = eb.snapshot();
    assert_eq!(
        snap.status, "complete",
        "BPF failed={:?} reason={:?}",
        snap.failed, snap.reason
    );
}
