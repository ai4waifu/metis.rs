//! Path and query JIT stubs for Metis.
//!
//! This is not `athena-jit` (KernelIR). It compiles Metis path/query routines.

use metis_types::{MetisError, NodeId};

/// Opaque compile-unit identity for a path/query plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompileUnitId(u64);

impl CompileUnitId {
    pub const fn get(self) -> u64 {
        self.0
    }
}

/// Eager-or-native artifact handle (foundation: eager only).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Artifact {
    pub unit: CompileUnitId,
    pub kind: ArtifactKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArtifactKind {
    /// Interpreter / BFS fallback.
    Eager,
    /// Reserved for native code objects.
    Native,
}

/// Compile a reachability query between two node handles into a unit.
pub fn compile_reach(from: NodeId, to: NodeId) -> Result<Artifact, MetisError> {
    let mut h: u64 = 0xcbf29ce484222325;
    for x in [from.get() as u64, to.get() as u64] {
        h ^= x;
        h = h.wrapping_mul(0x100000001b3);
    }
    Ok(Artifact {
        unit: CompileUnitId(h),
        kind: ArtifactKind::Eager,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;

    #[test]
    fn reach_unit_is_deterministic() {
        let a = NodeId::from_raw(NonZeroU32::new(1).unwrap());
        let b = NodeId::from_raw(NonZeroU32::new(2).unwrap());
        let x = compile_reach(a, b).unwrap();
        let y = compile_reach(a, b).unwrap();
        assert_eq!(x, y);
        assert_eq!(x.kind, ArtifactKind::Eager);
    }
}
