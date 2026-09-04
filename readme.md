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

Local path deps expect sibling checkouts:

```text
../athena.rs
../oaks
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
- Object heap protocol is `athena-gc`. Do not add `metis-gc` / `metis-arena`.
- Islands are first-class. ZFC is one island, not the foundation of every other island.
- Keywords declare. Actions are static `Module::fn` paths.
- Parsing is `oak-metis` only. Do not revive `metis-lang`.
- Frontends are skins. They must not bypass the graph kernel.
- Metis does not replace Athena and is not a Titan / SXO / Apollo rename.
