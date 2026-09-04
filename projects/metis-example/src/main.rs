//! Smoke: run ZFC finite-fragment theorems from island language source.

use metis::{run_source, VERSION};

fn main() {
    println!("metis {VERSION}");
    let src = include_str!("../../metis-compile/fixtures/zfc_basic.metis");
    let reports = run_source(src).expect("zfc_basic.metis");
    for r in &reports {
        println!(
            "proved {}::{} checks={}",
            r.island,
            r.theorem,
            r.proofs.len()
        );
    }
}
