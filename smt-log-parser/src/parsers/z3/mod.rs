use std::fmt::Debug;

use super::LogParser;

pub mod inst_graph;
/// Original Z3 log parser. Works with Z3 v.4.12.1, should work with other versions
/// as long as the log format is the same for the important line cases.
/// Compare with the log files in the `logs/` folder to see if this is the case.
pub mod z3parser;
// pub mod dump;

impl<T: Z3LogParser + Default> LogParser for T {
    fn process_line(&mut self, line: &str, line_no: usize) -> bool {
        // Much faster than `split_whitespace` or `split(' ')` since it works on
        // [u8] instead of [char] and so doesn't need to convert to UTF-8.
        let mut split = line.split_ascii_whitespace();
        // println!("Processing {line:?} ({line_no})");
        let parse = match split.next().unwrap() {
            // match the line case
            "[tool-version]" => self.version_info(split),
            "[mk-quant]" | "[mk-lambda]" => self.mk_quant(split),
            "[mk-var]" => self.mk_var(split),
            "[mk-proof]" => self.mk_proof_app(split, true),
            "[mk-app]" => self.mk_proof_app(split, false),
            "[attach-meaning]" => self.attach_meaning(split),
            "[attach-var-names]" => self.attach_var_names(split),
            "[attach-enode]" => self.attach_enode(split),
            "[eq-expl]" => self.eq_expl(split),
            "[new-match]" => self.new_match(split, line_no),
            "[inst-discovered]" => self.inst_discovered(split, line_no),
            "[instance]" => self.instance(split, line_no),
            "[end-of-instance]" => self.end_of_instance(split),
            "[decide-and-or]" => self.decide_and_or(split),
            "[decide]" => self.decide(split),
            "[assign]" => self.assign(split),
            "[push]" => self.push(split),
            "[pop]" => self.pop(split),
            "[begin-check]" => self.begin_check(split),
            "[query-done]" => self.query_done(split),
            "[eof]" => return false,
            "[resolve-process]" => self.resolve_process(split),
            "[resolve-lit]" => self.resolve_lit(split),
            "[conflict]" => self.conflict(split),
            _ => None,
        };
        parse.unwrap_or_else(|| eprintln!("Error parsing line: {line:?}"));
        true
    }

    fn end_of_file(&mut self) {
        self.eof();
    }
}

const DEFAULT: Option<()> = Some(());
pub trait Z3LogParser: Debug {
    /* Methods to handle each line case of Z3 logs.
     `l` is a line split with spaces as delimiters,
     and `l0` is the raw line (used only when )
    */
    fn version_info<'a>(&mut self, l: impl Iterator<Item = &'a str>) -> Option<()>;
    fn mk_quant<'a>(&mut self, l: impl Iterator<Item = &'a str>) -> Option<()>;
    fn mk_var<'a>(&mut self, l: impl Iterator<Item = &'a str>) -> Option<()>;
    fn mk_proof_app<'a>(&mut self, l: impl Iterator<Item = &'a str>, is_proof: bool) -> Option<()>;
    fn attach_meaning<'a>(&mut self, l: impl Iterator<Item = &'a str>) -> Option<()>;
    fn attach_var_names<'a>(&mut self, l: impl Iterator<Item = &'a str>) -> Option<()>;
    fn attach_enode<'a>(&mut self, l: impl Iterator<Item = &'a str>) -> Option<()>;
    fn eq_expl<'a>(&mut self, l: impl Iterator<Item = &'a str>) -> Option<()>;
    fn new_match<'a>(&mut self, l: impl Iterator<Item = &'a str>, line_no: usize) -> Option<()>;
    fn inst_discovered<'a>(
        &mut self,
        l: impl Iterator<Item = &'a str>,
        line_no: usize,
    ) -> Option<()>;
    fn instance<'a>(&mut self, l: impl Iterator<Item = &'a str>, line_no: usize) -> Option<()>;
    fn end_of_instance<'a>(&mut self, l: impl Iterator<Item = &'a str>) -> Option<()>;
    fn eof(&mut self);

    // unused in original parser
    fn decide_and_or<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn decide<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn assign<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn push<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn pop<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn begin_check<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn query_done<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn resolve_process<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn resolve_lit<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
    fn conflict<'a>(&mut self, _l: impl Iterator<Item = &'a str>) -> Option<()> {
        DEFAULT
    }
}

/// Type of solver and version number
#[derive(Debug)]
pub struct VersionInfo {
    solver: String,
    version: semver::Version,
}
impl VersionInfo {
    pub fn solver(&self) -> &str {
        &self.solver
    }
    pub fn version(&self) -> &semver::Version {
        &self.version
    }
}