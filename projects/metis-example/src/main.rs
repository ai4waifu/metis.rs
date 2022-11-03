//! Smoke: parse Living-grammar `.metis` fixtures.

use metis::{VERSION, parse_source};

fn main() {
    println!("metis {VERSION}");
    let group = include_str!("../../metis-compile/fixtures/group_theory_min.metis");
    let m = parse_source(group).expect("group_theory_min.metis");
    println!("parsed island {} items={}", m.islands[0].name, m.islands[0].items.len());
    let iff = include_str!("../../metis-compile/fixtures/iff_samples.metis");
    let m2 = parse_source(iff).expect("iff_samples.metis");
    println!("parsed iff module islands={}", m2.islands.len());
}
