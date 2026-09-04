//! Smoke: parse / lower Living-grammar fixtures and exercise Core admission basics.

use metis::{
    EdgeKind, QueryStatus, VERSION, compile_declarations, form_relation, parse_source,
};

fn main() {
    println!("metis {VERSION}");

    let group = include_str!("../../metis-compile/fixtures/group_theory_min.metis");
    let m = parse_source(group).expect("group_theory_min.metis");
    println!(
        "parsed island {} items={}",
        m.islands[0].name,
        m.islands[0].items.len()
    );

    let low = compile_declarations(group).expect("lower group");
    let gid = low.store.lookup("GroupTheory").expect("GroupTheory");
    println!(
        "lowered GroupTheory nodes={} relations={} axioms={} actions={} rewrites={}",
        low.nodes.iter().filter(|((id, _), _)| *id == gid).count(),
        low.relations.iter().filter(|((id, _), _)| *id == gid).count(),
        low.axioms.iter().filter(|(id, _)| *id == gid).count(),
        low.actions.len(),
        low.rewrites.iter().filter(|(id, _)| *id == gid).count()
    );

    // Core EQ smoke on a fresh accepted world (not from FOL axioms — declarations only).
    let mut store = metis::IslandStore::new();
    store.open_world("eq").unwrap();
    store.declare_generating_kind(EdgeKind::Equal).unwrap();
    let (a, b) = {
        let st = store.staging_mut().unwrap();
        let a = st.graph.intern_label(b"a").unwrap();
        let b = st.graph.intern_label(b"b").unwrap();
        st.graph.assert(a, EdgeKind::Equal, b).unwrap();
        (a, b)
    };
    let id = store.accept_staging("EQ").unwrap();
    let world = store.get(id).unwrap().world_id(id);
    let adm = store
        .admit_equal_candidate(id, form_relation(world, (a, b), None))
        .expect("admit EQ");
    let (st, _) = store.search_admit_equal(id, a, b).unwrap();
    assert_eq!(st, QueryStatus::Proven);
    let _ = store.admit_identity(id).expect("identity");
    println!(
        "core smoke: Equal proven tag={} identity_connections={}",
        adm.evidence_tag(),
        store.admitted_connections().len()
    );

    let iff = include_str!("../../metis-compile/fixtures/iff_samples.metis");
    let m2 = parse_source(iff).expect("iff_samples.metis");
    println!("parsed iff module islands={}", m2.islands.len());
}
