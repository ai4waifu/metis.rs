# Metis.rs

Metis is a relation-first math engine: a directed **graph** of nodes and morphisms, **islands** as self-contained knowledge domains, and an independent **island language** as the source of truth.

This repository is the Rust implementation workspace. Design lives outside the tree; this README is only an install and entry guide.

## Crates

```text
metis-types → metis-graph → metis-island → metis-lang → metis → metis-example
```

| Crate | Role |
|-------|------|
| `metis-types` | Handles and diagnostics |
| `metis-graph` | Arena graph, hash-cons, reachability |
| `metis-island` | Island registry and staging |
| `metis-lang` | Island language skeleton (stub) |
| `metis` | Stable facade |
| `metis-example` | Smoke binary |

## Develop

```shell
cargo check --workspace
cargo test --workspace
cargo run -p metis-example
```

Requires the workspace Rust toolchain (see `rust-toolchain.toml`).

## Boundaries

- Graph is the only kernel representation. Expression trees are views at most.
- Islands are first-class. ZFC is one island, not the foundation of every other island.
- Keywords declare. Actions are static `Module::fn` paths.
- Frontends are skins. They must not bypass the graph kernel.
- Metis does not replace Athena and is not a Titan / SXO / Apollo rename.
