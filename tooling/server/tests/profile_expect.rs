//! Every `[[program]]` in `profile.toml`: both artifacts exist, and the
//! dual-arch outcome matches that program's `expect`.

use std::collections::BTreeSet;

use server::harness::run_profile;
use server::profile;

#[test]
fn profile_programs_match_expect() {
    let profile = profile::load().expect("profile.toml");
    let mut names = BTreeSet::new();
    for program in &profile.programs {
        assert!(
            names.insert(program.name.clone()),
            "duplicate program {}",
            program.name
        );
        assert!(
            program.elf.is_file(),
            "missing elf for {}: {}",
            program.name,
            program.elf.display()
        );
        assert!(
            program.bpf.is_file(),
            "missing bpf for {}: {}",
            program.name,
            program.bpf.display()
        );
    }
    let report = run_profile(&profile.programs);
    assert!(report.all_ok(), "{}", report.to_json());
}
