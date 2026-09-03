//! Smoke: hash-cons, athena-gc, staging, oak-metis lex, JIT stub.

use metis::{
    compile_reach, lex_stub, EdgeKind, GcHeap, Graph, HeapBudget, IslandStore, VERSION,
};

fn main() {
    println!("metis {VERSION}");

    let heap = GcHeap::new(HeapBudget::default());
    let _ = heap.borrow().id();

    let mut g = Graph::new();
    let leaf = g.intern_empty().expect("empty");
    let a = g.intern(&[(EdgeKind::In, leaf)]).expect("a");
    let b = g.intern(&[(EdgeKind::In, leaf)]).expect("b");
    assert_eq!(a, b);
    assert!(g.reaches(a, leaf).expect("reach"));

    let art = compile_reach(a, leaf).expect("jit");
    assert_eq!(art.kind, metis::ArtifactKind::Eager);

    let mut store = IslandStore::new();
    let _zfc = store.register_accepted("ZFC").expect("zfc");
    let _sid = store.open_staging("scratch").expect("staging");
    {
        let st = store.staging_mut().expect("staging mut");
        let x = st.graph.intern_empty().expect("x");
        let _ = st.graph.intern(&[(EdgeKind::Equal, x)]).expect("eq");
    }
    store.discard_staging();

    let tokens = lex_stub("island Smoke {}").expect("lex");
    println!(
        "nodes={} edges={} tokens={} jit_unit={}",
        g.node_count(),
        g.edge_count(),
        tokens.len(),
        art.unit.get()
    );
}
