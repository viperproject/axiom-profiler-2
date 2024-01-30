use petgraph::Direction::{Incoming, Outgoing};
use smt_log_parser::parsers::z3::inst_graph::NodeInfo;
use yew::prelude::*;

use super::graph_filters::Filter;

#[derive(Properties, PartialEq)]
pub struct NodeActionsProps {
    pub selected_nodes: Vec<NodeInfo>,
    pub action: Callback<Vec<Filter>>,
}

#[function_component(NodeActions)]
pub fn node_actions(props: &NodeActionsProps) -> Html {
    let callback_from = |filter_for_inst: Box<dyn Fn(&NodeInfo) -> Filter>| {
        let callback = props.action.clone();
        let selected_insts = props.selected_nodes.clone();
        Callback::from(move |_| {
            let filters: Vec<Filter> = selected_insts.iter().map(&filter_for_inst).collect();
            callback.emit(filters);
        })
    };
    let show_subtree = callback_from(Box::new(|inst: &NodeInfo| {
        Filter::VisitSubTreeWithRoot(inst.node_index(), true)
    }));
    let hide_subtree = callback_from(Box::new(|inst: &NodeInfo| {
        Filter::VisitSubTreeWithRoot(inst.node_index(), false)
    }));
    let show_children = callback_from(Box::new(|inst: &NodeInfo| {
        Filter::ShowNeighbours(inst.node_index(), Outgoing)
    }));
    let show_parents = callback_from(Box::new(|inst: &NodeInfo| {
        Filter::ShowNeighbours(inst.node_index(), Incoming)
    }));
    let show_source_tree = callback_from(Box::new(|inst: &NodeInfo| {
        Filter::VisitSourceTree(inst.node_index(), true)
    }));
    let hide_source_tree = callback_from(Box::new(|inst: &NodeInfo| {
        Filter::VisitSourceTree(inst.node_index(), false)
    }));
    let ignore_quantifier = callback_from(Box::new(|inst: &NodeInfo| {
            match inst.mkind() {
                Some(mkind) => Filter::IgnoreQuantifier(mkind.quant_idx()),
                None => Filter::IgnoreQuantifier(None),
            }
        }
    ));
    let ignore_all_but_quantifier = callback_from(Box::new(|inst: &NodeInfo| {
        // Filter::IgnoreAllButQuantifier(inst.mkind.quant_idx())
            match inst.mkind() {
                Some(mkind) => Filter::IgnoreAllButQuantifier(mkind.quant_idx()),
                None => Filter::IgnoreAllButQuantifier(None),
            }
    }));
    let show_longest_path = callback_from(Box::new(|inst: &NodeInfo| {
        Filter::ShowLongestPath(inst.node_index())
    }));
    html! {
    <>
        <h4>{"You have selected some nodes. Here are possible actions (applied to all selected nodes):"}</h4>
        <div>
            <button onclick={show_subtree}>{"Show subtree with this root"}</button>
            <button onclick={hide_subtree}>{"Hide subtree with this root"}</button>
        </div>
        <div>
            <button onclick={show_children}>{"Show children"}</button>
            <button onclick={show_parents}>{"Show parents"}</button>
        </div>
        <div>
            <button onclick={show_source_tree}>{"Show ancestors"}</button>
            <button onclick={hide_source_tree}>{"Hide ancestors"}</button>
        </div>
        <div>
            <button onclick={ignore_quantifier}>{"Ignore all nodes of this quantifier"}</button>
        </div>
        <div>
            <button onclick={ignore_all_but_quantifier}>{"Only show this quantifier"}</button>
        </div>
        <div>
            <button onclick={show_longest_path}>{"Show longest path through last selected node"}</button>
        </div>
    </>
    }
}
