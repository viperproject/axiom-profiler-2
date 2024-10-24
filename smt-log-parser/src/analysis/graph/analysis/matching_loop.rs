use std::{
    collections::{HashMap, HashSet},
    ops::Deref,
};

use fxhash::{FxHashMap, FxHashSet};
use petgraph::{graph::NodeIndex, visit::Dfs, Direction::Outgoing};

use super::RawNodeIndex;
use crate::{
    analysis::{
        raw::{Node, NodeKind, RawIx},
        visible::VisibleEdge,
        InstGraph,
    },
    display_with::{DisplayCtxt, DisplayWithCtxt},
    items::{ENodeIdx, EqTransIdx, InstIdx, MatchKind, QuantIdx, TermIdx},
    Graph, Z3Parser,
};
// use matching_loop_graph::*;

pub const MIN_MATCHING_LOOP_LENGTH: usize = 3;

struct MlEquality {
    from: TermIdx,
    to: TermIdx,
    creators: FxHashSet<(QuantIdx, TermIdx)>,
}

impl MlEquality {
    pub fn merge_with(
        &mut self,
        from: TermIdx,
        to: TermIdx,
        creators: Vec<(QuantIdx, TermIdx)>,
        parser: &mut Z3Parser,
    ) {
        if let Some(term) = parser
            .terms
            .generalise(&mut parser.strings, vec![self.from, from])
        {
            self.from = term;
        }
        if let Some(term) = parser
            .terms
            .generalise(&mut parser.strings, vec![self.to, to])
        {
            self.to = term;
        }
        self.creators.extend(creators);
    }
    pub fn from(from: TermIdx, to: TermIdx, creators: Vec<(QuantIdx, TermIdx)>) -> Self {
        MlEquality {
            from,
            to,
            creators: creators.iter().cloned().collect(),
        }
    }
}

impl Default for MlEquality {
    fn default() -> Self {
        Self {
            from: TermIdx::from(0),
            to: TermIdx::from(0),
            creators: HashSet::default(),
        }
    }
}

struct MlMatchedTerm {
    matched: TermIdx,
    creator: (QuantIdx, TermIdx),
}

impl MlMatchedTerm {
    // TODO: maybe only generalise the terms in the very end? Otherwise we are creating lots of unnecessary generalised
    // terms that we won't even make use of
    pub fn merge_with(
        &mut self,
        matched: TermIdx,
        quant: QuantIdx,
        pattern: TermIdx,
        parser: &mut Z3Parser,
    ) {
        if let Some(term) = parser
            .terms
            .generalise(&mut parser.strings, vec![self.matched, matched])
        {
            self.matched = term;
        }
        self.creator = (quant, pattern)
    }
    pub fn from(matched: TermIdx, quant: QuantIdx, pattern: TermIdx) -> Self {
        MlMatchedTerm {
            matched,
            creator: (quant, pattern),
        }
    }
}

struct AbstractInst {
    // abstract instantiation defined by quantifier and trigger
    id: (QuantIdx, TermIdx),
    // stores the generalised blame terms and which (generalised) instantiation created it (indirectly)
    // the first element in each tuple is a vector that will be mapped to a generalised term
    matched_terms: FxHashMap<usize, MlMatchedTerm>,
    // stores the generalised equalities and which (generalised) instantiation created it (indirectly)
    // the first element in each tuple is a vector that will be mapped to a generalised term
    equalities: FxHashMap<usize, MlEquality>,
}

impl AbstractInst {
    pub fn from(id: (QuantIdx, TermIdx)) -> Self {
        Self {
            id,
            matched_terms: HashMap::default(),
            equalities: HashMap::default(),
        }
    }
    pub fn merge_nth_blame_term(
        &mut self,
        n: usize,
        blame_term: TermIdx,
        creator_quant: QuantIdx,
        creator_pattern: TermIdx,
        parser: &mut Z3Parser,
    ) {
        if let Some(matched_term) = self.matched_terms.get_mut(&n) {
            matched_term.merge_with(blame_term, creator_quant, creator_pattern, parser);
        } else {
            self.matched_terms.insert(
                n,
                MlMatchedTerm::from(blame_term, creator_quant, creator_pattern),
            );
        }
    }

    pub fn merge_nth_equalities(
        &mut self,
        n: usize,
        from: TermIdx,
        to: TermIdx,
        creators: Vec<(QuantIdx, TermIdx)>,
        parser: &mut Z3Parser,
    ) {
        if let Some(equalities) = self.equalities.get_mut(&n) {
            equalities.merge_with(from, to, creators, parser);
        } else {
            self.equalities
                .insert(n, MlEquality::from(from, to, creators));
        }
    }
    pub fn _to_string(&self, compact: bool, parser: &mut Z3Parser, ctxt: DisplayCtxt) -> String {
        let generalised_pattern = parser
            .terms
            .generalise_pattern(&mut parser.strings, self.id.1);
        let matched_terms = self
            .matched_terms
            .values()
            .map(|mterm| {
                format!(
                    "{} created by {}",
                    mterm.matched.with(&ctxt),
                    parser[mterm.creator.0].kind.with(&ctxt)
                )
            })
            .collect::<Vec<String>>()
            .join(", ");
        let equalities = self
            .equalities
            .values()
            .map(|meq| {
                format!(
                    "{} = {} created by {}",
                    meq.from.with(&ctxt),
                    meq.to.with(&ctxt),
                    meq.creators
                        .iter()
                        .map(|cr| format!("{}", parser[cr.0].kind.with(&ctxt)))
                        .collect::<Vec<String>>()
                        .join(", ")
                )
            })
            .collect::<Vec<String>>()
            .join(", ");
        if compact {
            format!(
                "{}: {}",
                parser[self.id.0].kind.with(&ctxt),
                generalised_pattern.with(&ctxt)
            )
        } else {
            format!("Abstract Instantiation ({}, {}) \n has matched terms \n {} \n and \n equalities {}", parser[self.id.0].kind.with(&ctxt), generalised_pattern.with(&ctxt), matched_terms, equalities)
        }
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum MLGraphNode {
    QI(QuantIdx, TermIdx),
    ENode(TermIdx),
    Equality(TermIdx, TermIdx),
}

impl InstGraph {
    pub fn search_matching_loops(&mut self, parser: &mut Z3Parser) -> usize {
        let currently_disabled_nodes = self.disabled_nodes();
        self.initialise_inst_succs_and_preds(parser);
        // disable all nodes that do not correspond to QIs
        self.reset_disabled_to(parser, |nx, g| {
            !matches!(g[nx].kind(), NodeKind::Instantiation(_))
        });
        let quants: FxHashSet<_> = self
            .raw
            .graph
            .node_weights()
            .filter_map(|node| {
                if let NodeKind::Instantiation(inst) = node.kind() {
                    Some(inst)
                } else {
                    None
                }
            })
            .flat_map(|inst| parser[parser[*inst].match_].kind.quant_idx())
            .collect();
        let mut matching_loop_nodes_per_quant: Vec<FxHashSet<RawNodeIndex>> = Vec::new();
        for quant in quants {
            self.raw.reset_visibility_to(true);
            self.raw
                .set_visibility_when(false, |_: RawNodeIndex, node: &Node| {
                    node.kind()
                        .inst()
                        .is_some_and(|i| parser[parser[i].match_].kind.quant_idx() == Some(quant))
                });
            let mut visible_graph = self.to_visible_simplified();
            let matching_loops = visible_graph.find_end_nodes_of_longest_paths();
            matching_loop_nodes_per_quant.push(matching_loops);
        }
        self.raw.reset_visibility_to(true);
        let ml_nodes = matching_loop_nodes_per_quant
            .iter()
            .flat_map(|ml| ml.iter().cloned());
        self.raw.set_visibility_many(false, ml_nodes);
        let mut matching_loop_subgraph = self.to_visible_simplified();
        // for displaying the nth longest matching loop later on, we want to compute the end nodes of all the matching loops
        // and sort them by max-depth in descending order
        matching_loop_subgraph.compute_longest_distances_from_roots();
        // compute end-nodes of matching loops
        let mut matching_loop_end_nodes: Vec<_> = matching_loop_subgraph
            .graph
            .node_indices()
            // only keep end-points of matching loops, i.e., nodes without any children in the matching loop subgraph
            .filter(|nx| {
                matching_loop_subgraph
                    .graph
                    .neighbors_directed(*nx, Outgoing)
                    .count()
                    == 0
            })
            .collect();
        // sort the matching loop end-nodes by the max-depth
        matching_loop_end_nodes.sort_unstable_by(|node_a, node_b| {
            let max_depth_node_a = matching_loop_subgraph
                .graph
                .node_weight(*node_a)
                .unwrap()
                .max_depth;
            let max_depth_node_b = matching_loop_subgraph
                .graph
                .node_weight(*node_b)
                .unwrap()
                .max_depth;
            if max_depth_node_a < max_depth_node_b {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Less
            }
        });
        // assign to each node in a matching loop which matching loops it belongs to, i.e., if a node is part of the
        // i-th longest matching loop, it stores the index i-1. Do this, by doing a reverse-DFS from all ML end nodes
        for (i, end_node) in matching_loop_end_nodes.iter().enumerate() {
            let mut dfs = Dfs::new(
                petgraph::visit::Reversed(&matching_loop_subgraph.graph),
                *end_node,
            );
            while let Some(nx) = dfs.next(petgraph::visit::Reversed(&matching_loop_subgraph.graph))
            {
                let orig_nx = matching_loop_subgraph.graph[nx].idx.0;
                self.raw.graph[orig_nx].part_of_ml.insert(i);
            }
        }
        // collect all matching loop end nodes
        let matching_loop_end_nodes_raw_indices: Vec<RawNodeIndex> = matching_loop_end_nodes
            .iter()
            .map(|nidx| matching_loop_subgraph.graph[*nidx].idx)
            .collect();
        // return the total number of potential matching loops
        let nr_matching_loop_end_nodes = matching_loop_end_nodes_raw_indices.len();
        self.analysis.matching_loop_end_nodes = Some(matching_loop_end_nodes_raw_indices);

        // compute the ML graphs for all the potential matching loops
        // first enable all of them
        self.reset_disabled_to(parser, |_, _| false);
        self.analysis.matching_loop_graphs = (0..nr_matching_loop_end_nodes)
            .map(|n| self.compute_nth_matching_loop_graph(n, parser))
            .collect();

        // make sure the enabled and disabled nodes stay the same as before calling the ML search
        self.reset_disabled_to(parser, |nx, _| currently_disabled_nodes.contains(&nx));
        nr_matching_loop_end_nodes
    }

    pub fn found_matching_loops(&self) -> Option<usize> {
        self.analysis
            .matching_loop_end_nodes
            .as_ref()
            .map(|mlen| mlen.len())
    }

    pub fn nth_matching_loop_graph(&mut self, n: usize) -> petgraph::Graph<MLGraphNode, ()> {
        if let Some(ml_graph) = self.analysis.matching_loop_graphs.get(n) {
            ml_graph.deref().clone()
        } else {
            petgraph::Graph::default().clone()
        }
    }

    fn _get_blame_term(&self, edge: &VisibleEdge, parser: &Z3Parser) -> Option<TermIdx> {
        let kind = edge.kind(self);
        let node = &self.raw[self.raw.index(kind.blame(self))];
        match node.kind() {
            NodeKind::ENode(enode) => Some(parser[*enode].owner),
            NodeKind::GivenEquality(eq, _) => match parser[*eq] {
                crate::items::EqualityExpl::Literal { eq, .. } => Some(parser[eq].owner),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn compute_nth_matching_loop_graph(
        &self,
        n: usize,
        parser: &mut Z3Parser,
    ) -> Graph<MLGraphNode, ()> {
        let nodes_of_nth_matching_loop = self
            .raw
            .graph
            .node_indices()
            .filter(|nx| self.raw.graph[*nx].part_of_ml.contains(&n))
            .collect::<FxHashSet<NodeIndex<RawIx>>>();
        // here we "fold" a potential matching loop into an abstract instantiation graph that represents the repeating pattern of the potential matching loop
        // an abstract instantiation is defined by the quantifier and the pattern used for the pattern match
        let mut abstract_insts: FxHashMap<(QuantIdx, TermIdx), AbstractInst> = HashMap::default();
        // for each abstract instantiation, we identify the matched terms and the blamed equalities
        for nx in nodes_of_nth_matching_loop {
            let node_kind = self.raw.graph[nx].kind();
            if let NodeKind::Instantiation(inst) = node_kind {
                let match_ = &parser[parser[*inst].match_];
                let pattern = match_.kind.pattern().unwrap();
                // here we have pairs (trigger, matched) where
                // matched.enode(): ENodeIdx is the matched term
                // matched.equalities(): Iterator<EqTransIdx> iterates over all equalities used to rewrite the matched term
                let trigger_matches = parser[pattern]
                    .child_ids
                    .iter()
                    .zip(match_.trigger_matches());
                let (matched_terms, equalities): (Vec<ENodeIdx>, Vec<Vec<EqTransIdx>>) =
                    trigger_matches
                        .map(|(_, matched)| (matched.enode(), matched.equalities().collect()))
                        .unzip();
                let quant = match_.kind.quant_idx().unwrap();
                for (n, matched_term) in matched_terms.iter().enumerate() {
                    let creator = parser[*matched_term].created_by;
                    if let Some(inst) = creator {
                        let match_ = &parser[parser[inst].match_];
                        let creator_pattern = match_.kind.pattern().unwrap();
                        let creator_quant = match_.kind.quant_idx().unwrap();
                        let blame_term = parser[*matched_term].owner;
                        if let Some(abstract_inst) = abstract_insts.get_mut(&(quant, pattern)) {
                            abstract_inst.merge_nth_blame_term(
                                n,
                                blame_term,
                                creator_quant,
                                creator_pattern,
                                parser,
                            )
                        } else {
                            abstract_insts
                                .insert((quant, pattern), AbstractInst::from((quant, pattern)));
                            abstract_insts
                                .get_mut(&(quant, pattern))
                                .unwrap()
                                .merge_nth_blame_term(
                                    n,
                                    blame_term,
                                    creator_quant,
                                    creator_pattern,
                                    parser,
                                )
                        }
                    }
                }
                for (n, equality) in equalities.iter().enumerate() {
                    for (i, eq) in equality.iter().enumerate() {
                        let creator_insts: Vec<(QuantIdx, TermIdx)> = parser[*eq]
                            .get_creator_insts(parser)
                            .iter()
                            .filter_map(|iidx| {
                                if let Some(inst) = iidx {
                                    let match_ = &parser[parser[*inst].match_];
                                    let creator_pattern = match_.kind.pattern().unwrap();
                                    let creator_quant = match_.kind.quant_idx().unwrap();
                                    Some((creator_quant, creator_pattern))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        if !creator_insts.is_empty() {
                            let from = parser.egraph.equalities.from(*eq);
                            let from_term = parser[from].owner;
                            let to = parser[*eq].to;
                            let to_term = parser[to].owner;
                            if let Some(abstract_inst) = abstract_insts.get_mut(&(quant, pattern)) {
                                abstract_inst.merge_nth_equalities(
                                    n + i,
                                    from_term,
                                    to_term,
                                    creator_insts,
                                    parser,
                                )
                            } else {
                                abstract_insts
                                    .insert((quant, pattern), AbstractInst::from((quant, pattern)));
                                abstract_insts
                                    .get_mut(&(quant, pattern))
                                    .unwrap()
                                    .merge_nth_equalities(
                                        n + i,
                                        from_term,
                                        to_term,
                                        creator_insts,
                                        parser,
                                    )
                            }
                        }
                    }
                }
            }
        }
        let mut ml_graph: Graph<MLGraphNode, ()> = Graph::with_capacity(0, 0);
        let mut nx_of_gen_term: FxHashMap<MLGraphNode, NodeIndex> = HashMap::default();
        let mut nx_of_abstract_inst: FxHashMap<(QuantIdx, TermIdx), NodeIndex> = HashMap::default();

        for ((quant, pattern), abstract_inst) in &abstract_insts {
            let abstract_inst_nx = if let Some(nx) = nx_of_abstract_inst.get(&(*quant, *pattern)) {
                *nx
            } else {
                let generalised_pattern = parser
                    .terms
                    .generalise_pattern(&mut parser.strings, *pattern);
                let nx = ml_graph.add_node(MLGraphNode::QI(*quant, generalised_pattern));
                nx_of_abstract_inst.insert((*quant, *pattern), nx);
                nx
            };
            for matched_term in abstract_inst.matched_terms.values() {
                let enode = MLGraphNode::ENode(matched_term.matched);
                let matched_term_nx = if let Some(nx) = nx_of_gen_term.get(&enode) {
                    *nx
                } else {
                    let nx = ml_graph.add_node(enode.clone());
                    nx_of_gen_term.insert(enode, nx);
                    nx
                };
                ml_graph.update_edge(matched_term_nx, abstract_inst_nx, ());
                let matched_term_creator_nx =
                    if let Some(nx) = nx_of_abstract_inst.get(&matched_term.creator) {
                        *nx
                    } else if let Some(creator_abstract_inst) =
                        abstract_insts.get(&matched_term.creator)
                    {
                        let generalised_pattern = parser
                            .terms
                            .generalise_pattern(&mut parser.strings, creator_abstract_inst.id.1);
                        let nx = ml_graph.add_node(MLGraphNode::QI(
                            creator_abstract_inst.id.0,
                            generalised_pattern,
                        ));
                        nx_of_abstract_inst
                            .insert((creator_abstract_inst.id.0, creator_abstract_inst.id.1), nx);
                        nx
                    } else {
                        let creator_abstract_inst = AbstractInst::from(matched_term.creator);
                        let generalised_pattern = parser
                            .terms
                            .generalise_pattern(&mut parser.strings, creator_abstract_inst.id.1);
                        let nx = ml_graph.add_node(MLGraphNode::QI(
                            creator_abstract_inst.id.0,
                            generalised_pattern,
                        ));
                        nx_of_abstract_inst
                            .insert((creator_abstract_inst.id.0, creator_abstract_inst.id.1), nx);
                        nx
                    };
                ml_graph.update_edge(matched_term_creator_nx, matched_term_nx, ());
            }
            for eq in abstract_inst.equalities.values() {
                if eq.from != eq.to {
                    let eq_node = MLGraphNode::Equality(eq.from, eq.to);
                    let eq_nx = if let Some(nx) = nx_of_gen_term.get(&eq_node) {
                        *nx
                    } else {
                        let nx = ml_graph.add_node(eq_node.clone());
                        nx_of_gen_term.insert(eq_node, nx);
                        nx
                    };
                    ml_graph.update_edge(eq_nx, abstract_inst_nx, ());
                    for eq_creator in &eq.creators {
                        let eq_creator_nx = if let Some(nx) = nx_of_abstract_inst.get(eq_creator) {
                            *nx
                        } else if let Some(creator_abstract_inst) = abstract_insts.get(eq_creator) {
                            let generalised_pattern = parser.terms.generalise_pattern(
                                &mut parser.strings,
                                creator_abstract_inst.id.1,
                            );
                            let nx = ml_graph.add_node(MLGraphNode::QI(
                                creator_abstract_inst.id.0,
                                generalised_pattern,
                            ));
                            nx_of_abstract_inst.insert(
                                (creator_abstract_inst.id.0, creator_abstract_inst.id.1),
                                nx,
                            );
                            nx
                        } else {
                            let creator_abstract_inst = AbstractInst::from(*eq_creator);
                            let generalised_pattern = parser.terms.generalise_pattern(
                                &mut parser.strings,
                                creator_abstract_inst.id.1,
                            );
                            let nx = ml_graph.add_node(MLGraphNode::QI(
                                creator_abstract_inst.id.0,
                                generalised_pattern,
                            ));
                            nx_of_abstract_inst.insert(
                                (creator_abstract_inst.id.0, creator_abstract_inst.id.1),
                                nx,
                            );
                            nx
                        };
                        ml_graph.update_edge(eq_creator_nx, eq_nx, ());
                    }
                }
            }
        }
        ml_graph
    }

    fn _get_pattern(&self, iidx: InstIdx, parser: &Z3Parser) -> Option<TermIdx> {
        if let Some(_quant) = parser[parser[iidx].match_].kind.quant_idx() {
            let inst = &parser[iidx];
            let match_ = &parser[inst.match_];
            match_.kind.pattern()
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub enum InstOrEquality {
    Inst(String, MatchKind),
    Equality,
}

impl std::fmt::Display for InstOrEquality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstOrEquality::Inst(quant, _) => write!(f, "{}", quant),
            InstOrEquality::Equality => write!(f, ""),
        }
    }
}
