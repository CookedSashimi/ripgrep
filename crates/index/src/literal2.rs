// BREADCRUMBS: Move this file aside and just work on porting the ngram
// extractor. The code below should be polished and moved into regex-syntax
// however.

use std::cmp;
use std::mem;

use bstr::{BString, ByteVec};
use regex_syntax::hir::{self, Hir, HirKind};

#[derive(Clone, Debug)]
pub enum Literals {
    Exact(LiteralSet),
    Inexact(Inexact),
}

#[derive(Clone, Debug)]
struct Inexact {
    tree: BoolTree,
    prefix: LiteralSet,
    inner: LiteralSet,
    suffix: LiteralSet,
}

impl Literals {
    fn exact(set: LiteralSet) -> Literals {
        Literals::Exact(set)
    }

    fn exact_one(string: BString) -> Literals {
        Literals::Exact(LiteralSet::single(string))
    }

    fn anything() -> Literals {
        Literals::Inexact(Inexact {
            tree: BoolTree::everything(),
            prefix: LiteralSet::new(),
            inner: LiteralSet::new(),
            suffix: LiteralSet::new(),
        })
    }

    fn empty_string() -> Literals {
        Literals::exact(LiteralSet::single(BString::from("")))
    }

    fn max_len(&self) -> usize {
        match *self {
            Literals::Exact(ref set) => set.len(),
            Literals::Inexact(ref inex) => cmp::max(
                inex.prefix.len(),
                cmp::max(inex.inner.len(), inex.suffix.len()),
            ),
        }
    }

    fn is_exact(&self) -> bool {
        match *self {
            Literals::Exact(..) => true,
            _ => false,
        }
    }

    fn make_inexact(&mut self) -> &mut Inexact {
        let exact = match *self {
            Literals::Inexact(ref mut inex) => return inex,
            Literals::Exact(ref mut exact) => {
                mem::replace(exact, LiteralSet::new())
            }
        };
        *self = Literals::Inexact(Inexact {
            tree: BoolTree::from_set(exact.clone()),
            prefix: exact.clone(),
            inner: exact.clone(),
            suffix: exact,
        });
        match *self {
            Literals::Inexact(ref mut inex) => inex,
            _ => unreachable!(),
        }
    }

    fn union(&mut self, o: Literals) {
        match o {
            Literals::Exact(set2) => match *self {
                Literals::Exact(ref mut set1) => {
                    set1.union(set2);
                }
                Literals::Inexact(ref mut inex1) => {
                    inex1.tree.union(BoolTree::from_set(set2.clone()));
                    inex1.prefix.union(set2.clone());
                    inex1.inner.union(set2.clone());
                    inex1.suffix.union(set2);
                }
            },
            Literals::Inexact(inex2) => {
                let inex1 = self.make_inexact();
                inex1.tree.union(inex2.tree);
                inex1.prefix.union(inex2.prefix);
                inex1.inner.union(inex2.inner);
                inex1.suffix.union(inex2.suffix);
            }
        }
    }

    fn concat(&mut self, o: Literals) {
        match o {
            Literals::Exact(set2) => match *self {
                Literals::Exact(ref mut set1) => {
                    set1.cross(set2);
                }
                Literals::Inexact(ref mut inex1) => {
                    inex1.tree.concat(BoolTree::from_set(set2.clone()));
                    if inex1.prefix.has_empty() {
                        inex1.prefix.union(set2.clone());
                    }
                    inex1.inner.union(set2.clone());
                    inex1.suffix.cross(set2);
                }
            },
            Literals::Inexact(inex2) => {
                let was_exact = self.is_exact();
                let inex1 = self.make_inexact();

                inex1.tree.concat(inex2.tree);

                if was_exact {
                    inex1.prefix.cross(inex2.prefix);
                } else if inex1.prefix.has_empty() {
                    inex1.prefix.union(inex2.prefix);
                }

                inex1.inner.union(inex2.inner);

                let old_suffix = mem::replace(&mut inex1.suffix, inex2.suffix);
                if inex1.suffix.has_empty() {
                    inex1.suffix.union(old_suffix);
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
struct LiteralSet {
    lits: Vec<BString>,
}

impl LiteralSet {
    fn new() -> LiteralSet {
        LiteralSet { lits: vec![] }
    }

    fn single(lit: BString) -> LiteralSet {
        LiteralSet { lits: vec![lit] }
    }

    fn clear(&mut self) {
        self.lits.clear();
    }

    fn canonicalize(&mut self) {
        self.lits.sort();
        self.lits.dedup();
    }

    fn union(&mut self, o: LiteralSet) {
        self.lits.extend(o.lits);
        self.canonicalize();
    }

    fn cross(&mut self, o: LiteralSet) {
        if o.is_empty() || o.has_only_empty() {
            return;
        }
        if self.is_empty() || self.has_only_empty() {
            *self = o;
            return;
        }

        let orig = mem::replace(&mut self.lits, vec![]);
        for selflit in &orig {
            for olit in &o.lits {
                let mut newlit = selflit.clone();
                newlit.push_str(olit);
                self.lits.push(newlit);
            }
        }
    }

    fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    fn len(&self) -> usize {
        self.lits.len()
    }

    fn min_len(&self) -> usize {
        self.lits.iter().map(|x| x.len()).min().unwrap_or(0)
    }

    fn has_empty(&self) -> bool {
        self.lits.get(0).map_or(false, |x| x.is_empty())
    }

    fn has_only_empty(&self) -> bool {
        self.len() == 1 && self.has_empty()
    }
}

#[derive(Clone, Debug)]
enum BoolTree {
    Literal(BString),
    And(Vec<BoolTree>),
    Or(Vec<BoolTree>),
}

impl BoolTree {
    fn empty() -> BoolTree {
        BoolTree::Or(vec![])
    }

    fn everything() -> BoolTree {
        BoolTree::And(vec![])
    }

    fn from_set(set: LiteralSet) -> BoolTree {
        let lits: Vec<_> =
            set.lits.into_iter().map(BoolTree::Literal).collect();
        if lits.is_empty() {
            return BoolTree::and(vec![]);
        }
        BoolTree::or(lits)
    }

    fn or(mut trees: Vec<BoolTree>) -> BoolTree {
        if trees.is_empty() || trees.len() > 1 {
            return BoolTree::Or(trees);
        }
        trees.pop().unwrap()
    }

    fn and(mut trees: Vec<BoolTree>) -> BoolTree {
        if trees.is_empty() || trees.len() > 1 {
            return BoolTree::And(trees);
        }
        trees.pop().unwrap()
    }

    fn union(&mut self, tree2: BoolTree) {
        use self::BoolTree::*;

        let mut tree1 = mem::replace(self, BoolTree::empty());
        match (tree1, tree2) {
            (Literal(lit1), Literal(lit2)) => {
                *self = Or(vec![Literal(lit1), Literal(lit2)]);
            }
            (Literal(lit1), And(trees2)) => {
                *self = Or(vec![Literal(lit1), And(trees2)]);
            }
            (Literal(lit1), Or(mut trees2)) => {
                trees2.push(Literal(lit1));
                *self = Or(trees2);
            }
            (And(trees1), tree2) => {
                *self = Or(vec![And(trees1), tree2]);
            }
            (Or(mut trees1), tree2) => {
                trees1.push(tree2);
                *self = Or(trees1);
            }
        }
    }

    fn concat(&mut self, tree2: BoolTree) {
        use self::BoolTree::*;

        let mut tree1 = mem::replace(self, BoolTree::empty());
        match (tree1, tree2) {
            (Literal(lit1), Literal(lit2)) => {
                *self = And(vec![Literal(lit1), Literal(lit2)]);
            }
            (Literal(lit1), And(mut trees2)) => {
                trees2.push(Literal(lit1));
                *self = And(trees2);
            }
            (Literal(lit1), Or(trees2)) => {
                *self = And(vec![Literal(lit1), And(trees2)]);
            }
            (And(mut trees1), tree2) => {
                trees1.push(tree2);
                *self = And(trees1);
            }
            (Or(trees1), tree2) => {
                *self = And(vec![Or(trees1), tree2]);
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct LiteralsBuilder {
    limit_len: usize,
    limit_class: usize,
}

impl LiteralsBuilder {
    pub fn new() -> LiteralsBuilder {
        LiteralsBuilder { limit_len: 250, limit_class: 10 }
    }

    pub fn limit_len(&mut self, len: usize) -> &mut LiteralsBuilder {
        self.limit_len = len;
        self
    }

    pub fn limit_class(&mut self, len: usize) -> &mut LiteralsBuilder {
        self.limit_class = len;
        self
    }

    pub fn build(&self, exp: &Hir) -> Literals {
        match *exp.kind() {
            HirKind::Empty | HirKind::Anchor(_) | HirKind::WordBoundary(_) => {
                Literals::empty_string()
            }
            HirKind::Literal(hir::Literal::Unicode(ch)) => {
                let mut lit = BString::from(vec![]);
                lit.push_char(ch);
                Literals::Exact(LiteralSet::single(lit))
            }
            HirKind::Literal(hir::Literal::Byte(b)) => {
                let mut lit = BString::from(vec![]);
                lit.push_byte(b);
                Literals::Exact(LiteralSet::single(lit))
            }
            HirKind::Class(hir::Class::Unicode(ref cls)) => {
                if class_over_limit_unicode(cls, self.limit_class) {
                    return Literals::anything();
                }

                let mut set = LiteralSet::new();
                for r in cls.iter() {
                    for cp in (r.start() as u32)..=(r.end() as u32) {
                        let ch = match std::char::from_u32(cp) {
                            None => continue,
                            Some(ch) => ch,
                        };
                        set.lits.push(BString::from(ch.to_string()));
                    }
                }
                set.canonicalize();
                Literals::exact(set)
            }
            HirKind::Class(hir::Class::Bytes(ref cls)) => {
                if class_over_limit_bytes(cls, self.limit_class) {
                    return Literals::anything();
                }

                let mut set = LiteralSet::new();
                for r in cls.iter() {
                    for b in r.start()..=r.end() {
                        set.lits.push(BString::from(vec![b]));
                    }
                }
                set.canonicalize();
                Literals::exact(set)
            }
            HirKind::Group(ref group) => self.build(&group.hir),
            HirKind::Repetition(ref rep) => {
                if rep.is_match_empty() {
                    Literals::anything()
                } else {
                    let mut lits = self.build(&rep.hir);
                    lits.make_inexact();
                    lits
                }
            }
            HirKind::Alternation(ref exps) => {
                let mut set = self.build(&exps[0]);
                for e in exps.iter().skip(1) {
                    set.union(self.build(e));
                }
                set
            }
            HirKind::Concat(ref exps) => {
                let mut exps = combine_literals(exps);
                let mut set = Literals::Exact(LiteralSet::new());
                for e in exps {
                    let next = self.build_literal_or_hir(e);
                    if set.max_len() + next.max_len() > self.limit_len {
                        set.concat(Literals::anything());
                    } else {
                        set.concat(next);
                    }
                }
                set

                // let mut set = self.build(&exps[0]);
                // for e in exps.iter().skip(1) {
                // let next = self.build(e);
                // if set.max_len() + next.max_len() > self.limit_len {
                // set.concat(Literals::anything());
                // } else {
                // set.concat(next);
                // }
                // }
                // set
            }
        }
    }

    fn build_literal_or_hir(&self, or: LiteralOrHir) -> Literals {
        match or {
            LiteralOrHir::Literal(string) => Literals::exact_one(string),
            LiteralOrHir::Other(exp) => self.build(exp),
        }
    }
}

impl Default for LiteralsBuilder {
    fn default() -> LiteralsBuilder {
        LiteralsBuilder::new()
    }
}

fn class_over_limit_unicode(cls: &hir::ClassUnicode, limit: usize) -> bool {
    let mut count = 0;
    for r in cls.iter() {
        if count > limit {
            return true;
        }
        count += (r.end() as u32 - r.start() as u32) as usize;
    }
    count > limit
}

fn class_over_limit_bytes(cls: &hir::ClassBytes, limit: usize) -> bool {
    let mut count = 0;
    for r in cls.iter() {
        if count > limit {
            return true;
        }
        count += (r.end() - r.start()) as usize;
    }
    count > limit
}

#[derive(Debug)]
enum LiteralOrHir<'a> {
    Literal(BString),
    // Guaranteed to never contain a HirKind::Literal.
    Other(&'a Hir),
}

fn combine_literals(concat: &[Hir]) -> Vec<LiteralOrHir> {
    let mut combined = vec![];
    let mut lit = BString::from(vec![]);
    for exp in concat {
        match *exp.kind() {
            HirKind::Literal(hir::Literal::Unicode(ch)) => {
                lit.push_char(ch);
            }
            HirKind::Literal(hir::Literal::Byte(b)) => {
                lit.push_byte(b);
            }
            _ => {
                if !lit.is_empty() {
                    combined.push(LiteralOrHir::Literal(lit));
                    lit = BString::from(vec![]);
                }
                combined.push(LiteralOrHir::Other(exp));
            }
        }
    }
    if !lit.is_empty() {
        combined.push(LiteralOrHir::Literal(lit));
    }
    combined
}

#[cfg(test)]
mod tests {
    use super::*;
    use regex_syntax::ParserBuilder;

    fn parse(pattern: &str) -> Hir {
        ParserBuilder::new()
            .allow_invalid_utf8(true)
            .build()
            .parse(pattern)
            .unwrap()
    }

    fn literals(pattern: &str) -> Literals {
        let re = parse(pattern);
        let mut b = LiteralsBuilder::new();
        // b.limit_len(3);
        b.build(&re)
    }

    #[test]
    fn scratch() {
        // dbg!(literals(r"a|b|c"));
        // dbg!(literals(r"[2-6]"));
        // dbg!(literals(r"abcQ+def(QQ)+xyz"));
        // dbg!(literals(r".abc(XYZ)+"));
        dbg!(literals(r".(a)(yz)"));
        // dbg!(literals(r"abc.def.ghi"));
        // dbg!(literals(r"ZZZ+(foo|bar|baz)(a|b)"));
        // dbg!(literals(r"aND|caN|Ha[DS]|WaS"));
        // dbg!(literals(r"\|[^|][^|]*\|"));
        // dbg!(literals(r"a[act]ggtaaa|tttacc[agt]t"));
        // dbg!(literals(r">[^\n]*\n|\n"));
    }
}
