use std::fmt;

use crate::text::{
    color::Rainbow,
    style::{Highlighter, Paint},
    symbol::Symbol,
};

use super::ast::{self, Ast, Expr, Infix, Pat, VisitMut};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[default_variant::default(Left)]
pub enum Assoc {
    Left,
    Right,
    Neither,
}

impl Assoc {
    pub const fn is_left(&self) -> bool {
        matches!(self, Self::Left)
    }

    pub const fn is_right(&self) -> bool {
        matches!(self, Self::Right)
    }

    pub const fn is_neither(&self) -> bool {
        !self.is_left() && !self.is_right()
    }

    pub const fn adjective(&self) -> &'static str {
        match self {
            Assoc::Left => "left-associative",
            Assoc::Right => "right-associative",
            Assoc::Neither => "non-associative",
        }
    }

    pub const fn keyword(&self) -> &'static str {
        match self {
            Assoc::Left => "infixl",
            Assoc::Right => "infixr",
            Assoc::Neither => "infix",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Prec(pub u8);

impl Prec {
    pub const MAX_VAL: u8 = 9;
    pub const MIN_VAL: u8 = 0;
    pub const MAX: Self = Self(Self::MAX_VAL);
    pub const MIN: Self = Self(Self::MIN_VAL);
    pub const THEN: Self = Self(1);
    pub const OR: Self = Self(2);
    pub const AND: Self = Self(3);
}

#[cfg(not(feature = "precs"))]
impl Prec {
    pub const CMP: Self = Self(4);
    pub const ADD: Self = Self(6);
    pub const MUL: Self = Self(7);
    pub const POW: Self = Self(8);
    pub const OF: Self = Self(9);
}

impl Default for Prec {
    fn default() -> Self {
        Self::MAX
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Fixity {
    pub prec: Prec,
    pub assoc: Assoc,
}

impl Default for Fixity {
    fn default() -> Self {
        Self::DEFAULT
    }
}

impl Fixity {
    pub const DEFAULT: Self = Self {
        prec: Prec::MAX,
        assoc: Assoc::Left,
    };

    pub const CONS: Self = Self {
        prec: Prec(5),
        assoc: Assoc::Right,
    };

    pub const PLUS_MINUS: Self = Self {
        prec: Prec(6),
        assoc: Assoc::Left,
    };

    pub const MULT_DIV_REM: Self = Self {
        prec: Prec(7),
        assoc: Assoc::Left,
    };

    pub const POW: Self = Self {
        prec: Prec::POW,
        assoc: Assoc::Right,
    };

    pub const COMPOSE: Self = Self {
        prec: Prec::MAX,
        assoc: Assoc::Right,
    };

    pub fn write_alignable(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.assoc.keyword().set_fg_red())?;
        if self.assoc.is_neither() {
            write!(f, " ",)?;
        }
        write!(f, " {}", &self.prec.0.set_fg_purple())
    }
}

impl fmt::Display for Fixity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.assoc.keyword(), self.prec.0)
    }
}

#[derive(PartialEq, Eq)]
enum Rule {
    Shift,
    Reduce,
    Ambiguous(Prec, Assoc, Assoc),
}

impl Rule {
    fn from_fixities(prev_fixity: Fixity, curr_fixity: Fixity) -> Rule {
        let Fixity {
            prec: prev_prec,
            assoc: prev_assoc,
        } = prev_fixity;
        let Fixity {
            prec: curr_prec,
            assoc: curr_assoc,
        } = curr_fixity;
        if curr_prec > prev_prec {
            Rule::Shift
        } else if curr_prec == prev_prec {
            match (curr_assoc, prev_assoc) {
                (Assoc::Left, Assoc::Left) => Rule::Reduce,
                (Assoc::Right, Assoc::Right) => Rule::Shift,
                _ => Rule::Ambiguous(curr_prec, prev_assoc, curr_assoc),
            }
        } else {
            Rule::Reduce
        }
    }

    fn reduce(operands: &mut Vec<Box<Expr>>, infixes: &mut Vec<Infix>) {
        assert!(operands.len() >= 2);
        let infix = infixes.pop().unwrap();
        let right = operands.pop().unwrap();
        let left = operands.pop().unwrap();
        operands.push(Box::new(Expr::Bin(left, infix, right)));
    }

    fn shift(infixes: &mut Vec<Infix>, infix: Infix) {
        infixes.push(infix);
    }

    fn error(_prec: Prec, prev: Operator, curr: Operator) -> AssocError {
        match (prev, curr) {
            ((_, Assoc::Neither), _) | (_, (_, Assoc::Neither)) => {
                AssocError::Nonfix { prev, curr }
            }
            _ => AssocError::Mixfix { prev, curr },
        }
    }
}

type Operator = (Infix, Assoc);

#[derive(Clone, Debug, PartialEq)]
pub enum AssocError {
    /// Non-associative infix within an associative context
    Nonfix { prev: Operator, curr: Operator },
    /// Mismatching associativities within the same precedence level
    Mixfix { prev: Operator, curr: Operator },
}

impl AssocError {
    fn parts(&self) -> (&'static str, &Operator, &Operator) {
        match self {
            AssocError::Nonfix { prev, curr } => ("Non-associative operator", prev, curr),
            AssocError::Mixfix { prev, curr } => ("Associativity mismatch", prev, curr),
        }
    }
}

impl std::fmt::Display for AssocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (_label, (prev_op, prev_assoc), (curr_op, curr_assoc)) = self.parts();
        write!(
            f,
            "found {} operator `{}` followed by infix \
            expression using the {} operator `{}`",
            prev_assoc.adjective(),
            prev_op,
            curr_assoc.adjective(),
            curr_op
        )
    }
}

type FnvIndexMap<K, V> = indexmap::IndexMap<K, V, fnv::FnvBuildHasher>;
type FixityMap = FnvIndexMap<Infix, Fixity>;

#[derive(Clone, Debug)]
pub struct Fixities {
    data: FixityMap,
}

impl Default for Fixities {
    fn default() -> Self {
        Self {
            data: Default::default(),
        }
    }
}

impl Fixities {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn empty() -> Self {
        Self {
            data: Default::default(),
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn iter(&self) -> indexmap::map::Iter<'_, Infix, Fixity> {
        self.data.iter()
    }

    pub fn has(&self, op: &Infix) -> bool {
        self.data.contains_key(op)
    }

    pub fn get_defined(&self, op: &Infix) -> Option<Fixity> {
        self.data.get(op).copied()
    }

    pub fn get(&self, op: &Infix) -> Fixity {
        self.get_defined(op).unwrap_or_default()
    }

    pub fn insert(&mut self, op: Infix, fixity: Fixity) -> Option<Fixity> {
        self.data.insert(op, fixity)
    }

    pub fn remove(&mut self, op: &Infix) -> Option<Fixity> {
        self.data.shift_remove(op)
    }

    pub fn remove_last(&mut self, count: usize) -> impl Iterator<Item = (Infix, Fixity)> + '_ {
        (0..count).flat_map(|_| self.data.pop()).rev()
    }

    pub fn insert_many_with_fixity(
        &mut self,
        fixity: Fixity,
        infixes: impl IntoIterator<Item = Infix>,
    ) {
        infixes.into_iter().for_each(|infix| {
            self.insert(infix, fixity);
        });
    }

    pub fn rewrite(&mut self, mut expr: Expr) -> Result<Expr, AssocError> {
        let mut operands = vec![];
        let mut infixes = Vec::new();
        loop {
            match expr {
                Expr::Bin(left, infix, right) => {
                    operands.push(left);
                    expr = *right;
                    loop {
                        match infixes.last().copied() {
                            Some(prev_op) => {
                                match Rule::from_fixities(self.get(&prev_op), self.get(&infix)) {
                                    Rule::Shift => {
                                        Rule::shift(&mut infixes, infix);
                                        break;
                                    }
                                    Rule::Reduce => Rule::reduce(&mut operands, &mut infixes),
                                    Rule::Ambiguous(prec, a0, a1) => {
                                        return Err(Rule::error(prec, (prev_op, a0), (infix, a1)))
                                    }
                                };
                            }
                            None => {
                                infixes.push(infix);
                                break;
                            }
                        }
                    }
                }
                mut right => {
                    while !infixes.is_empty() {
                        assert!(operands.len() >= 1);
                        let left = operands.pop().unwrap();
                        let infix = infixes.pop().unwrap();
                        right = Expr::Bin(left, infix, Box::new(right))
                    }
                    return Ok(right);
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Resolver {
    fixities: Fixities,
    errors: Vec<AssocError>,
}

impl Default for Resolver {
    fn default() -> Self {
        Self {
            fixities: Default::default(),
            errors: Default::default(),
        }
    }
}

impl Resolver {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn clear(&mut self) -> usize {
        let k = self.fixities.len();
        self.fixities = Fixities::default();
        k
    }

    pub fn fixities(&self) -> &Fixities {
        &self.fixities
    }

    pub fn entries_for<'a, I>(
        &'a self,
        ops: I,
    ) -> FixityEntries<impl Iterator<Item = FixityEntry<'a>>>
    where
        I: Iterator<Item = Infix>,
    {
        FixityEntries(ops.filter_map(|op| self.fixities.data.get_key_value(&op)))
    }

    pub fn fixity_entries<'a>(&'a self) -> FixityEntries<indexmap::map::Iter<'_, Infix, Fixity>> {
        FixityEntries(self.fixities.iter())
    }

    pub fn resolved(ast: &mut Ast) -> Result<(), Vec<AssocError>> {
        Self::new().load_fixities(ast).resolve_ast(ast)
    }

    fn store_error(&mut self, error: AssocError) {
        if !self.errors.contains(&error) {
            self.errors.push(error);
        }
    }

    pub fn take_errors(&mut self) -> Vec<AssocError> {
        std::mem::take(&mut self.errors)
    }

    pub fn add_fixity(&mut self, infix: Infix, fixity: Fixity) -> Option<(Infix, Fixity)> {
        self.fixities
            .insert(infix, fixity)
            .map(|old_fixity| (infix, old_fixity))
    }

    pub fn load_fixities(&mut self, ast: &mut Ast) -> &mut Self {
        ast.infxs.iter().for_each(|decl| {
            self.fixities
                .insert_many_with_fixity(decl.fixity, decl.infixes.iter().copied())
        });
        self
    }

    pub fn resolve_ast(&mut self, ast: &mut Ast) -> Result<(), Vec<AssocError>> {
        self.visit_ast_mut(ast);
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.take_errors())
        }
    }

    pub fn resolve_expr(&mut self, expr: Expr) -> Result<Expr, AssocError> {
        self.fixities.rewrite(expr)
    }

    pub fn printer(&self) -> Printer<'_> {
        Printer::new(&self.fixities)
    }

    pub fn print_expr(&self, expr: &Expr) {
        self.printer().print_expr(expr)
    }

    pub fn load_hs_prelude(&mut self) -> usize {
        // let start = self.fixities.data.len();
        self.fixities.insert(
            Infix::Standard(Symbol::CASH),
            Fixity {
                prec: Prec::MIN,
                assoc: Assoc::Right,
            },
        );
        self.fixities.insert_many_with_fixity(
            Fixity {
                prec: Prec(1),
                assoc: Assoc::Left,
            },
            [
                Infix::Standard(Symbol::intern(">>=")),
                Infix::Standard(Symbol::intern(">>")),
            ],
        );
        self.fixities.insert(
            Infix::Standard(Symbol::intern("=<<")),
            Fixity {
                prec: Prec(1),
                assoc: Assoc::Right,
            },
        );

        self.fixities.insert(
            Infix::Standard(Symbol::PIPE2),
            Fixity {
                prec: Prec::OR,
                assoc: Assoc::Right,
            },
        );
        self.fixities.insert(
            Infix::Standard(Symbol::AMPERSAND2),
            Fixity {
                prec: Prec::AND,
                assoc: Assoc::Right,
            },
        );
        self.fixities.insert_many_with_fixity(
            Fixity {
                prec: Prec(4),
                assoc: Assoc::Neither,
            },
            [
                Symbol::intern("=="),
                Symbol::intern("/="),
                Symbol::intern("<"),
                Symbol::intern("<="),
                Symbol::intern(">"),
                Symbol::intern(">="),
            ]
            .into_iter()
            .map(Infix::Standard)
            .chain(std::iter::once(Infix::Promoted(Symbol::intern("elem")))),
        );
        self.fixities.insert_many_with_fixity(
            Fixity::CONS,
            [Symbol::COLON, Symbol::intern("++")]
                .into_iter()
                .map(Infix::Standard),
        );
        self.fixities.insert(
            Infix::Standard(Symbol::intern("<>")),
            Fixity {
                prec: Prec(6),
                assoc: Assoc::Right,
            },
        );
        self.fixities.insert_many_with_fixity(
            Fixity::PLUS_MINUS,
            [Symbol::PLUS, Symbol::DASH]
                .into_iter()
                .map(Infix::Standard),
        );
        self.fixities.insert_many_with_fixity(
            Fixity::MULT_DIV_REM,
            [
                Symbol::intern("*"),
                Symbol::intern("/"),
                Symbol::intern("%"),
            ]
            .into_iter()
            .map(Infix::Standard),
        );

        self.fixities.insert_many_with_fixity(
            Fixity::POW,
            [
                Symbol::intern("^"),
                Symbol::intern("^^"),
                Symbol::intern("**"),
            ]
            .into_iter()
            .map(Infix::Standard),
        );

        // self.fixities.data.len() - start
        23
    }

    pub fn load_arithmetic(&mut self) -> usize {
        [
            (Fixity::PLUS_MINUS, vec![Symbol::PLUS, Symbol::DASH]),
            (
                Fixity::PLUS_MINUS,
                vec![Symbol::STAR, Symbol::FSLASH, Symbol::PERCENT],
            ),
            (
                Fixity::POW,
                vec![Symbol::CARET, Symbol::CARET2, Symbol::STAR2],
            ),
        ]
        .into_iter()
        .for_each(|(fixity, infixes)| {
            self.fixities
                .insert_many_with_fixity(fixity, infixes.into_iter().map(Infix::Standard));
        });
        8
    }
}

impl VisitMut for Resolver {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // ast::walk_expr_mut(self, expr);
        match expr {
            Expr::Bin(..) => match self.fixities.rewrite(expr.clone()) {
                Ok(e) => {
                    *expr = e;
                    ast::walk_expr_mut(self, expr);
                }
                Err(err) => self.store_error(err),
            },
            Expr::Let(decl, body) => {
                // add local fixities, then after rewriting the body,
                // restore pre-existing fixities and remove all the
                // rest
                //
                // note that since hash_map APIs return `None` if an
                // entry didn't exist, this vector will never have a
                // length greater than the number of fixities
                // originally defined
                let old_fixities = decl
                    .infixes
                    .clone()
                    .into_iter()
                    .flat_map(|infix| {
                        self.fixities
                            .insert(infix, decl.fixity)
                            .map(|fx| (infix, fx))
                    })
                    .collect::<Vec<_>>();
                self.visit_expr_mut(body);
                // optimization: instead of manually removing fixities
                // that didnt exist prior to this expression, remove
                // `new_len - old_len` of the last fixities, then
                // re-insert the fixities that used to exist
                self.fixities
                    .remove_last(old_fixities.len())
                    .for_each(|_| ());
                old_fixities.into_iter().for_each(|(infix, fixity)| {
                    self.fixities.insert(infix, fixity);
                });
            }
            _ => ast::walk_expr_mut(self, expr),
        };
    }

    fn visit_ast_mut(&mut self, ast: &mut Ast) {
        ast.infxs.iter().for_each(|decl| {
            self.fixities
                .insert_many_with_fixity(decl.fixity, decl.infixes.iter().copied());
        });
        ast::walk_ast_mut(self, ast);
    }
}

pub struct Printer<'a> {
    fixities: &'a Fixities,
    stack: Vec<Fixity>,
}

impl<'a> Printer<'a> {
    pub fn new(fixities: &'a Fixities) -> Self {
        Self {
            fixities,
            stack: vec![],
        }
    }

    pub fn curr_fixity(&self) -> Fixity {
        self.stack.last().copied().unwrap_or_else(|| Fixity {
            prec: self.curr_prec(),
            assoc: self.curr_assoc(),
        })
    }

    pub fn curr_prec(&self) -> Prec {
        self.stack
            .last()
            .map(|fixity| fixity.prec)
            .unwrap_or_else(|| Prec(0))
    }

    pub fn curr_assoc(&self) -> Assoc {
        self.stack
            .last()
            .map(|fixity| fixity.assoc)
            .unwrap_or_else(|| Assoc::Neither)
    }

    pub fn print_expr(&'a mut self, expr: &'a Expr) {
        use std::cell::RefCell;
        struct Show<'a>(RefCell<&'a mut Printer<'a>>, &'a Expr);
        impl fmt::Display for Show<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.borrow_mut().write_expr(self.1, f)
            }
        }
        println!("  {}", Show(RefCell::new(self), expr))
    }

    pub fn print_fixities(&self) {
        struct Show<'a>(&'a Printer<'a>);
        impl fmt::Display for Show<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.write_fixities(f)
            }
        }
        println!("{}", Show(self))
    }

    pub fn write_grouped(
        &mut self,
        f: &mut fmt::Formatter,
        print: impl FnOnce(&mut Self, &mut fmt::Formatter) -> fmt::Result,
    ) -> fmt::Result {
        use std::fmt::Display;
        let rainbow = Rainbow::new(self.stack.len());
        rainbow.highlight('(').fmt(f)?;
        print(self, f)?;
        rainbow.highlight(')').fmt(f)?;
        Ok(())
    }

    pub fn write_pat(&mut self, pat: &Pat, f: &mut fmt::Formatter) -> fmt::Result {
        let write_sequence = |this: &mut Self, pats: &[Pat], f: &mut fmt::Formatter| {
            match &pats[..] {
                [] => (),
                [p, ps @ ..] => {
                    this.write_pat(p, f)?;
                    for p in ps {
                        write!(f, ", ")?;
                        this.write_pat(p, f)?;
                    }
                }
            };
            Ok(())
        };
        match pat {
            Pat::Wild => write!(f, "_"),
            Pat::Lit(lit) => write!(f, "{lit}"),
            Pat::Var(s) => write!(f, "{s}"),
            Pat::Neg(pat) => {
                write!(f, "(")?;
                match &**pat {
                    Pat::Wild | Pat::Lit(_) | Pat::Var(_) => {
                        write!(f, "-")?;
                        self.write_pat(pat, f)?;
                    }
                    _ => {
                        write!(f, "-")?;
                        self.write_grouped(f, |this, f| this.write_pat(pat, f))?;
                    }
                };
                write!(f, ")")
            }
            Pat::Con(con, args) => {
                if args.is_empty() {
                    write!(f, "{con}")
                } else {
                    write!(f, "({con}")?;
                    for arg in args {
                        write!(f, " ")?;
                        self.write_pat(arg, f)?;
                    }
                    write!(f, ")")
                }
            }
            Pat::Tup(pats) => {
                write!(f, "(")?;
                write_sequence(self, pats, f)?;
                write!(f, ")")
            }
            Pat::Arr(pats) => {
                write!(f, "[")?;
                write_sequence(self, pats, f)?;
                write!(f, "]")
            }
            Pat::Lnk(l, r) => {
                let parens = |p: &Pat, this: &mut Self, f: &mut fmt::Formatter| {
                    if let Pat::Lnk(..) | Pat::As(..) = p {
                        this.write_grouped(f, |this, f| this.write_pat(p, f))
                    } else {
                        this.write_pat(p, f)
                    }
                };
                self.stack.push(Fixity::CONS);
                self.write_grouped(f, |this, f| {
                    parens(l, this, f)?;
                    write!(f, ":")?;
                    parens(r, this, f)
                })?;
                self.stack.pop();
                Ok(())
            }
            Pat::As(id, pat) => {
                write!(f, "{id}@")?;
                self.write_pat(pat, f)
            }
        }
    }

    pub fn write_expr(&mut self, expr: &Expr, f: &mut fmt::Formatter) -> fmt::Result {
        match expr {
            Expr::Lit(lit) => write!(f, "{lit}"),
            Expr::Var(ident) => {
                if ident.is_infix() {
                    write!(f, "({ident})")
                } else {
                    write!(f, "{ident}")
                }
            }
            Expr::App(func, arg) => {
                self.write_expr(func, f)?;
                write!(f, " ")?;
                self.write_expr(arg, f)
            }
            Expr::Bin(l, op, r) => {
                let fixity = self.fixities.get(op);
                self.stack.push(fixity);
                let no_paren = |e: &Expr| {
                    matches!(
                        e,
                        Expr::Grp(..)
                            | Expr::List(..)
                            | Expr::Lit(..)
                            | Expr::Tup(..)
                            | Expr::Var(..)
                    )
                };
                let ppr = |this: &mut Self, e, f: &mut fmt::Formatter| {
                    if no_paren(e) {
                        this.write_expr(e, f)
                    } else {
                        this.write_grouped(f, |this, f| this.write_expr(e, f))
                    }
                };

                ppr(self, l, f)?;
                write!(f, " {op} ")?;
                ppr(self, r, f)?;
                self.stack.pop();
                Ok(())
            }
            Expr::Lam(pat, body) => {
                let (l, r) = if self.stack.is_empty() {
                    ("", "")
                } else {
                    ("(", ")")
                };
                write!(f, "{l}\\")?;
                let stack = std::mem::take(&mut self.stack);
                self.write_pat(pat, f)?;
                let mut body = &**body;
                while let Expr::Lam(pat, e) = body {
                    write!(f, " ")?;
                    self.write_pat(pat, f)?;
                    body = &**e;
                }
                write!(f, " -> ")?;
                self.stack = stack;
                self.write_expr(body, f)?;
                write!(f, "{r}")
            }
            Expr::Grp(e) => self.write_grouped(f, |this, f| this.write_expr(e, f)),
            Expr::Neg(_) => todo!(),
            Expr::Tup(es) => {
                let old = std::mem::take(&mut self.stack);
                write!(f, "(")?;
                match &es[..] {
                    [] => (),
                    [x, xs @ ..] => {
                        self.write_expr(x, f)?;
                        for x in xs {
                            write!(f, ", ")?;
                            self.write_expr(x, f)?;
                        }
                    }
                };
                write!(f, ")")?;
                self.stack = old;
                Ok(())
            }
            Expr::List(es) => {
                let old = std::mem::take(&mut self.stack);
                write!(f, "[")?;
                match &es[..] {
                    [] => (),
                    [x, xs @ ..] => {
                        self.write_expr(x, f)?;
                        for x in xs {
                            write!(f, ", ")?;
                            self.write_expr(x, f)?;
                        }
                    }
                };
                write!(f, "]")?;
                self.stack = old;
                Ok(())
            }
            Expr::Let(_, body) => self.write_expr(body, f),
        }
    }

    pub fn write_fixities(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.fixities.len() == 0 {
            return Ok(());
        }

        let fixities = self
            .fixities
            .data
            .values()
            .collect::<indexmap::IndexSet<&Fixity, fnv::FnvBuildHasher>>();
        let len = fixities.len();
        for (n, fixity) in fixities.into_iter().enumerate() {
            let mut infxs =
                self.fixities
                    .data
                    .iter()
                    .filter_map(|(op, fx)| if fixity == fx { Some(op) } else { None });
            if let Some(op) = infxs.next() {
                fixity.write_alignable(f)?;
                write!(f, " {op}")?;
                for op in infxs {
                    write!(f, ", {op}")?;
                }
                if n + 1 < len {
                    write!(f, "\n")?;
                }
            }
        }

        Ok(())
    }
}

type FixityEntry<'a> = (&'a Infix, &'a Fixity);

pub struct FixityEntries<I>(I);

impl<I> FixityEntries<I> {
    pub fn from_iter<'a>(iter: I) -> FixityEntries<I::IntoIter>
    where
        I: IntoIterator<Item = FixityEntry<'a>>,
    {
        FixityEntries(iter.into_iter())
    }

    pub fn then<J>(self, mut f: impl FnMut(I) -> J) -> FixityEntries<J> {
        FixityEntries(f(self.0))
    }

    pub fn print_fixities<'a>(self)
    where
        I: Iterator<Item = FixityEntry<'a>>,
    {
        use std::cell::RefCell;
        use std::marker::PhantomData;
        struct Show<'a, I>(
            RefCell<Option<FixityEntries<I>>>,
            PhantomData<FixityEntry<'a>>,
        );
        impl<'a, I> fmt::Display for Show<'a, I>
        where
            I: Iterator<Item = FixityEntry<'a>>,
        {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.0
                    .borrow_mut()
                    .take()
                    .expect(
                        "inner is always `Some` since this \
                        struct only exists within `print_fixities`, \
                        is created with a `Some` variant and is only \
                        consumed during this call",
                    )
                    .write_fixities(f)
            }
        }
        println!("{}", Show(RefCell::new(Some(self)), PhantomData))
    }

    pub fn write_fixities<'a>(self, f: &mut fmt::Formatter) -> fmt::Result
    where
        I: Iterator<Item = FixityEntry<'a>>,
    {
        let (ops, fixities): (Vec<&Infix>, Vec<&Fixity>) = self.0.unzip();
        let fxs = fixities
            .iter()
            .copied()
            .collect::<indexmap::IndexSet<&Fixity, fnv::FnvBuildHasher>>();
        let len = fxs.len();
        for (n, fixity) in fxs.into_iter().enumerate() {
            let mut infxs = ops.iter().zip(fixities.iter()).filter_map(|(op, fx)| {
                if fixity == *fx {
                    Some(op)
                } else {
                    None
                }
            });
            if let Some(infix) = infxs.next() {
                fixity.write_alignable(f)?;
                write!(f, " {infix}")?;
                for op in infxs {
                    write!(f, ", {op}")?;
                }
                if n + 1 < len {
                    write!(f, "\n")?;
                }
            }
        }
        Ok(())
    }
}

impl<I> IntoIterator for FixityEntries<I>
where
    I: Iterator,
{
    type Item = I::Item;

    type IntoIter = I;

    fn into_iter(self) -> Self::IntoIter {
        self.0
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::syntax::ast::Ident;
    use crate::syntax::parser;

    fn bin(l: Expr, op: Infix, r: Expr) -> Expr {
        Expr::Bin(Box::new(l), op, Box::new(r))
    }

    fn ident(s: &str) -> Ident {
        Ident::Lower(Symbol::intern(s))
    }

    fn var(s: &str) -> Expr {
        Expr::Var(ident(s))
    }

    #[test]
    fn test_fixity() {
        let src = r#"
infixr 5 :
a:b:c:d:[]
"#;
        let mut ast = parser::parse(src).expect("valid syntax");
        let mut resolver = Resolver::new();
        assert!(resolver.resolve_ast(&mut ast).is_ok());
        use crate::text::symbol;
        const COLON: Infix = Infix::Standard(Symbol::COLON);
        let [a, b, c, d] =
            symbol::intern_n(["a", "b", "c", "d"]).map(|e| Expr::Var(Ident::Lower(e)));
        let expected = bin(
            a,
            COLON,
            bin(b, COLON, bin(c, COLON, bin(d, COLON, Expr::List(vec![])))),
        );
        assert_eq!(ast.exprs[0].expr, expected)
    }

    #[test]
    fn local_fixities_stay_in_scope() {
        let src = r#"
infixl 6 +, -
let infixr 6 + in a + b + c + d
a + b + c + d
"#;
        let mut ast = parser::parse(src).expect("valid syntax");
        let mut resolver = Resolver::new();
        assert!(resolver.resolve_ast(&mut ast).is_ok());
        let plus = Infix::Standard(Symbol::intern("+"));
        let expected1 = bin(
            var("a"),
            plus,
            bin(var("b"), plus, bin(var("c"), plus, var("d"))),
        );
        let expected2 = bin(
            bin(bin(var("a"), plus, var("b")), plus, var("c")),
            plus,
            var("d"),
        );

        assert_eq!(
            if let Expr::Let(_, e) = &ast.exprs[0].expr {
                &**e
            } else {
                unreachable!("we know this expression is a let expression")
            },
            &expected1
        );
        assert_eq!(&ast.exprs[1].expr, &expected2);
    }
}
