#[cfg(feature = "mem_dbg")]
use mem_dbg::{MemDbg, MemSize};

use crate::error::Either;
use crate::{Error, Result};
use std::fmt;
use std::ops::Index;

use super::{ENodeIdx, EqTransIdx, MatchIdx, QuantIdx, TermId, TermIdx};

/// A Z3 instantiation.
#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct Instantiation {
    pub match_: MatchIdx,
    pub fingerprint: Fingerprint,
    pub proof_id: Option<Either<TermIdx, TermId>>,
    pub z3_generation: Option<u32>,
    pub yields_terms: Box<[ENodeIdx]>,
}

impl Instantiation {
    pub fn get_resulting_term(&self) -> Option<TermIdx> {
        self.proof_id.as_ref()?.as_result().ok().copied()
    }
}

#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct Match {
    pub kind: MatchKind,
    pub blamed: Box<[BlameKind]>,
}

impl Match {
    /// A quantifier may have multiple possible triggers where each
    /// instantiation will be due to matching exactly one. Each of these
    /// triggers has a sequence of arbitrarily many terms which must all be
    /// matched. This returns a sequence of `Blame` where each explains how the
    /// corresponding term in the trigger was matched.
    pub fn trigger_matches(&self) -> impl Iterator<Item = Blame> {
        let mut last = 0;
        let terms = self
            .blamed
            .iter()
            .enumerate()
            .flat_map(|(idx, blame)| matches!(blame, BlameKind::Term { .. }).then(|| idx))
            .chain([self.blamed.len()]);
        terms.skip(1).map(move |idx| {
            let slice = &self.blamed[last..idx];
            last = idx;
            Blame { slice }
        })
    }
}

#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum MatchKind {
    MBQI {
        quant: QuantIdx,
        bound_terms: Box<[ENodeIdx]>,
    },
    TheorySolving {
        axiom_id: TermId,
        bound_terms: Box<[TermIdx]>,
        rewrite_of: Option<TermIdx>,
    },
    Axiom {
        axiom: QuantIdx,
        pattern: TermIdx,
        bound_terms: Box<[TermIdx]>,
    },
    Quantifier {
        quant: QuantIdx,
        pattern: TermIdx,
        bound_terms: Box<[ENodeIdx]>,
    },
}
impl MatchKind {
    pub fn quant_idx(&self) -> Option<QuantIdx> {
        match self {
            Self::MBQI { quant, .. }
            | Self::Axiom { axiom: quant, .. }
            | Self::Quantifier { quant, .. } => Some(*quant),
            _ => None,
        }
    }
    pub fn pattern(&self) -> Option<TermIdx> {
        match self {
            Self::MBQI { .. } | Self::TheorySolving { .. } => None,
            Self::Axiom { pattern, .. } | Self::Quantifier { pattern, .. } => Some(*pattern),
        }
    }
    pub fn bound_terms<T>(
        &self,
        enode: impl Fn(ENodeIdx) -> T,
        term: impl Fn(TermIdx) -> T,
    ) -> Vec<T> {
        match self {
            Self::MBQI { bound_terms, .. } | Self::Quantifier { bound_terms, .. } => {
                bound_terms.iter().map(|&x| enode(x)).collect()
            }
            Self::TheorySolving { bound_terms, .. } | Self::Axiom { bound_terms, .. } => {
                bound_terms.iter().map(|&x| term(x)).collect()
            }
        }
    }
    pub fn is_discovered(&self) -> bool {
        self.quant_idx().is_none()
    }
    pub fn is_mbqi(&self) -> bool {
        matches!(self, Self::MBQI { .. })
    }
    // TODO: this is currently unused
    pub fn rewrite_of(&self) -> Option<TermIdx> {
        match self {
            Self::TheorySolving { rewrite_of, .. } => *rewrite_of,
            _ => None,
        }
    }
}

/// The kind of dependency between two quantifier instantiations.
/// - Term: one instantiation produced a term that the other triggered on
/// - Equality: dependency based on an equality.
#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub enum BlameKind {
    Term { term: ENodeIdx },
    Equality { eq: EqTransIdx },
}
impl BlameKind {
    fn unwrap_enode(&self) -> &ENodeIdx {
        match self {
            Self::Term { term } => term,
            _ => panic!("expected term"),
        }
    }
    fn unwrap_eq(&self) -> &EqTransIdx {
        match self {
            Self::Equality { eq } => eq,
            _ => panic!("expected equality"),
        }
    }
}

/// Explains how a term in a trigger was matched. It will always start with an
/// enode and then have some sequence of equalities used to rewrite distinct
/// subexpressions of the enode.
#[derive(Debug, Clone, Copy)]
pub struct Blame<'a> {
    slice: &'a [BlameKind],
}
impl<'a> Blame<'a> {
    pub fn enode(self) -> ENodeIdx {
        *self.slice[0].unwrap_enode()
    }

    pub fn equalities_len(self) -> usize {
        self.slice.len() - 1
    }
    pub fn equalities(self) -> impl Iterator<Item = EqTransIdx> + 'a {
        self.slice.iter().skip(1).map(|x| *x.unwrap_eq())
    }
}
impl Index<usize> for Blame<'_> {
    type Output = EqTransIdx;
    fn index(&self, idx: usize) -> &Self::Output {
        self.slice[idx + 1].unwrap_eq()
    }
}

/// An identifier for a Z3 quantifier instantiation (called "fingerprint" in the original Axiom Profiler).
/// Represented as a 16-digit hexadecimal number in log files.
#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Fingerprint(pub u64);
impl Fingerprint {
    pub fn parse(value: &str) -> Result<Self> {
        u64::from_str_radix(value.strip_prefix("0x").unwrap_or(value), 16)
            .map(Self)
            .map_err(Error::InvalidFingerprint)
    }
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }
}
impl std::ops::Deref for Fingerprint {
    type Target = u64;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl fmt::Display for Fingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:x}", self.0)
    }
}