//! Smoke: hash-cons, reachability, staging discard.

use metis::{parse_stub, EdgeKind, Graph, IslandStore, SourceFile, VERSION};

fn main() {
    println!("metis {VERSION}");

    let mut g = Graph::new();
    let leaf = g.intern_empty().expect("empty");
    let a = g.intern(&[(EdgeKind::In, leaf)]).expect("a");
    let b = g.intern(&[(EdgeKind::In, leaf)]).expect("b");
    assert_eq!(a, b);
    assert!(g.reaches(a, leaf).expect("reach"));

    let mut store = IslandStore::new();
    let _zfc = store.register_accepted("ZFC").expect("zfc");
    let _sid = store.open_staging("scratch").expect("staging");
    {
        let st = store.staging_mut().expect("staging mut");
        let x = st.graph.intern_empty().expect("x");
        let _ = st.graph.intern(&[(EdgeKind::Equal, x)]).expect("eq");
    }
    store.discard_staging();

    let src = SourceFile {
        path: "smoke.island".into(),
        text: "island Smoke {}".into(),
    };
    let stub = parse_stub(&src).expect("parse stub");
    println!(
        "nodes={} edges={} parse_bytes={}",
        g.node_count(),
        g.edge_count(),
        stub.byte_len
    );
}
