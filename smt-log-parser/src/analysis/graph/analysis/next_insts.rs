use petgraph::Direction;

use crate::{
    analysis::{
        raw::{NextInsts, Node, NodeKind},
        RawNodeIndex,
    },
    Z3Parser,
};

use super::{Initialiser, TransferInitialiser};

pub trait NextInstsInitialiser<const FORWARD: bool> {
    /// The starting value for a node.
    fn base(&mut self, node: &Node, parser: &Z3Parser) -> NextInsts;
    /// Called between initialisations of different subgraphs.
    fn reset(&mut self) {}
    type Observed;
    fn observe(&mut self, node: &Node, parser: &Z3Parser) -> Self::Observed;
    fn transfer(
        &mut self,
        from: &Node,
        from_idx: RawNodeIndex,
        to_idx: usize,
        to_all: &[Self::Observed],
    ) -> NextInsts;
}
impl<C: NextInstsInitialiser<FORWARD>, const FORWARD: bool> Initialiser<FORWARD, 2> for C {
    type Value = NextInsts;
    fn direction() -> Direction {
        if FORWARD {
            Direction::Outgoing
        } else {
            Direction::Incoming
        }
    }
    fn base(&mut self, _node: &Node, _parser: &Z3Parser) -> Self::Value {
        NextInsts::default()
    }
    fn assign(&mut self, node: &mut Node, value: Self::Value) {
        if FORWARD {
            node.inst_parents = value;
        } else {
            node.inst_children = value;
        }
    }
    fn reset(&mut self) {
        NextInstsInitialiser::reset(self)
    }
}
impl<C: NextInstsInitialiser<FORWARD>, const FORWARD: bool> TransferInitialiser<FORWARD, 2> for C {
    type Observed = C::Observed;
    fn observe(&mut self, node: &Node, parser: &Z3Parser) -> Self::Observed {
        NextInstsInitialiser::observe(self, node, parser)
    }
    fn transfer(
        &mut self,
        from: &Node,
        from_idx: RawNodeIndex,
        to_idx: usize,
        to_all: &[Self::Observed],
    ) -> Self::Value {
        NextInstsInitialiser::transfer(self, from, from_idx, to_idx, to_all)
    }
    fn add(&mut self, node: &mut Node, value: Self::Value) {
        if FORWARD {
            node.inst_parents.nodes.extend(value.nodes);
        } else {
            node.inst_children.nodes.extend(value.nodes);
        }
    }
}

pub struct DefaultNextInsts<const FORWARD: bool>;
impl<const FORWARD: bool> NextInstsInitialiser<FORWARD> for DefaultNextInsts<FORWARD> {
    fn base(&mut self, _node: &Node, _parser: &Z3Parser) -> NextInsts {
        NextInsts::default()
    }
    type Observed = ();
    fn observe(&mut self, _node: &Node, _parser: &Z3Parser) -> Self::Observed {}
    fn transfer(
        &mut self,
        node: &Node,
        _from_idx: RawNodeIndex,
        _idx: usize,
        _incoming: &[Self::Observed],
    ) -> NextInsts {
        match *node.kind() {
            NodeKind::Instantiation(iidx) => NextInsts {
                nodes: std::iter::once(iidx).collect(),
            },
            _ => {
                if FORWARD {
                    node.inst_parents.clone()
                } else {
                    node.inst_children.clone()
                }
            }
        }
    }
}
