# Metis.rs

Metis is a relation-first math engine: a directed **graph** of nodes and morphisms, **islands** as knowledge domains, and an independent **island language** as the source of truth.

This repository is the Rust implementation workspace. Design lives outside the tree; this README is only an install and entry guide.

## Crates

```text
athena-types → athena-gc
                  ↓
metis-types → metis-graph → metis-island → metis-verify → metis-compile → metis-jit → metis
                                                ↑
                                         oak-metis (AST)
```

| Crate | Role |
|-------|------|
| `athena-gc` | Shared runtime GC heap |
| `metis-types` | Handles and diagnostics |
| `metis-graph` | Relation graph, labels, judgment edges |
| `metis-island` | Island registry and staging |
| `metis-verify` | EQ + ZFC-lite prove/verify |
| `metis-compile` | Run theorem scripts from island source |
| `metis-jit` | Path/query compile units |
| `oak-metis` | Island language parse (oaks) |
| `metis` | Stable facade |
| `metis-example` | Smoke binary |

Theorems and proofs are authored in `.metis` files (see `projects/metis-compile/fixtures/`).

## Develop

External crates come from git (`athena.rs` / `oaks` on `dev`). Optional local overrides:

```toml
[patch."https://github.com/ai4waifu/athena.rs.git"]
athena-types = { path = "../athena.rs/projects/athena-types" }
athena-gc = { path = "../athena.rs/projects/athena-gc" }

[patch."https://github.com/ygg-lang/oaks.git"]
oak-metis = { path = "../oaks/examples/oak-metis", default-features = false }
```

```shell
cargo check --workspace
cargo test --workspace
cargo run -p metis-example
```

Requires the workspace Rust toolchain (see `rust-toolchain.toml`).

## Boundaries

- Graph is the only kernel representation. Expression trees are views at most.
- Structural outs hash-cons; judgment edges assert facts without rewriting identity.
- Trusted boundary is Metis Core (world / admission / connection). Island verifiers do not define Core.
- Object heap protocol is `athena-gc`. Do not add `metis-gc` / `metis-arena`.
- Ordinary discrete adjacency is `athena-graph` (not CAS M-Graph). `metis-graph` only adds Metis semantics.
- Islands are local relation worlds under Core. ZFC is one island, not the foundation of every other island.
- Connection is a world morphism first; Galois needs extra proof.
- Query results are at least Proven / Refuted / Unknown / Inconsistent. Missing a path is not negation by default.
- Keywords declare. Actions are static `Module::fn` paths.
- Parsing is `oak-metis` only. Do not revive `metis-lang`.
- Frontends are skins. They must not bypass the graph kernel.
- Metis does not replace Athena and is not a Titan / SXO / Apollo rename.
- Metis and Athena M-Graph share philosophy only, not object models or admission contracts.
