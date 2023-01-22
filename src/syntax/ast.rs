use crate::text::symbol::Symbol;

use super::{fixity::Fixity, token::Literal};

#[derive(Clone, Debug, PartialEq)]
pub struct Ast {
    pub kinds: Vec<DeclKind>,
    pub infxs: Vec<InfixDecl>,
    pub exprs: Vec<ExprDecl>,
}

impl Default for Ast {
    fn default() -> Self {
        Self {
            kinds: Default::default(),
            infxs: Default::default(),
            exprs: Default::default(),
        }
    }
}

impl Ast {
    pub fn push(&mut self, decl: Decl) {
        self.kinds.push(decl.kind());
        match decl {
            Decl::Infix(decl) => {
                self.infxs.push(decl);
            }
            Decl::Expr(decl) => {
                self.exprs.push(decl);
            }
        }
    }

    pub fn into_iter(self) -> AstIntoIter {
        AstIntoIter::new(self)
    }

    pub fn iter(&self) -> AstIter<'_> {
        AstIter::new(self)
    }

    pub fn iter_mut(&mut self) -> AstIterMut<'_> {
        AstIterMut::new(self)
    }
}

macro_rules! iter_decls {
    (@tick $method:ident) => {
        fn $method(&mut self) -> Option<Self::Item> {
            use Decl as D;
            use DeclKind as Dk;
            match self.kinds.$method() {
                None => None,
                Some(i) => match i {
                    Dk::Infix => self.infxs.$method().map(D::Infix),
                    Dk::Expr => self.exprs.$method().map(D::Expr),
                },
            }
        }
    };
    (
        $(
            $name:ident$(<$lt:lifetime>)? {
                :$item:ident
                :$idx_iter:ident -> $decl_iter:ident
                $(:deriving $tr0:path $(, $trs:path)*)?
            }
        )*
    ) => {
        $(
            $(#[derive($tr0 $(, $trs)*)])?
            pub struct $name$(<$lt>)? {
                kinds: iter_decls!(#$idx_iter $(, $lt, )? DeclKind),
                infxs: iter_decls!(#$decl_iter $(, $lt, )? InfixDecl),
                exprs: iter_decls!(#$decl_iter $(, $lt, )? ExprDecl)
            }

            impl$(<$lt>)? $name$(<$lt>)? {
                pub(crate) fn new(
                    ast: iter_decls!(:$decl_iter $(, $lt, )? Ast)
                ) -> Self {
                    Self {
                        kinds: iter_decls!(.$idx_iter ast kinds),
                        infxs: iter_decls!(.$decl_iter ast infxs),
                        exprs: iter_decls!(.$decl_iter ast exprs),
                    }
                }

                pub fn len(&self) -> usize {
                    self.kinds.as_slice().len()
                }

                pub fn is_empty(&self) -> bool {
                    self.len() == 0
                }
            }

            impl$(<$lt>)? Iterator for $name$(<$lt>)? {
                type Item = $item$(<$lt>)?;

                iter_decls! { @tick next }
            }

            impl$(<$lt>)? ExactSizeIterator for $name$(<$lt>)? {}

            impl$(<$lt>)? DoubleEndedIterator for $name$(<$lt>)? {
                iter_decls! { @tick next_back }
            }

            impl$(<$lt>)? IntoIterator
            for iter_decls!(:$decl_iter $(, $lt, )? Ast) {
                type Item = $item$(<$lt>)?;

                type IntoIter = $name$(<$lt>)?;

                fn into_iter(self) -> Self::IntoIter {
                    $name::new(self)
                }
            }
        )*
    };
    (#Owned $(, $lt:lifetime, )? $ty:ty) => { std::vec::IntoIter<$ty> };
    (#Ref $(, $lt:lifetime, )? $ty:ty) => { std::slice::Iter<$($lt,)? $ty> };
    (#Mut $(, $lt:lifetime, )? $ty:ty) => { std::slice::IterMut<$($lt,)? $ty> };
    (:Owned $(, $lt:lifetime, )? $name:ident) => { $name };
    (:Ref $(, $lt:lifetime, )? $name:ident) => { $(&$lt)? $name };
    (:Mut $(, $lt:lifetime, )? $name:ident) => { $(&$lt mut)? $name };
    (.Owned $name:ident $field:ident) => { $name.$field.into_iter() };
    (.Ref $name:ident $field:ident) => { $name.$field.iter() };
    (.Mut $name:ident $field:ident) => { $name.$field.iter_mut() };
}

iter_decls! {
    AstIntoIter {
        :Decl
        :Owned -> Owned
        :deriving Clone, Debug
    }
    AstIter<'a> {
        :DeclRef
        :Ref -> Ref
        :deriving Clone, Debug
    }
    AstIterMut<'a> {
        :DeclMut
        :Ref -> Mut
        :deriving Debug
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Infix,
    Expr,
}

#[derive(Clone, Debug)]
pub enum Decl<I = InfixDecl, E = ExprDecl> {
    Infix(I),
    Expr(E),
}

impl<I, E> Decl<I, E> {
    pub fn kind(&self) -> DeclKind {
        match self {
            Decl::Infix(_) => DeclKind::Infix,
            Decl::Expr(_) => DeclKind::Expr,
        }
    }
}

type DeclRef<'a> = Decl<&'a InfixDecl, &'a ExprDecl>;
type DeclMut<'a> = Decl<&'a mut InfixDecl, &'a mut ExprDecl>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InfixDecl {
    pub infixes: Vec<Infix>,
    pub fixity: Fixity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprDecl {
    pub expr: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Lit(Literal),
    Var(Ident),
    App(Box<Self>, Box<Self>),
    Bin(Box<Self>, Infix, Box<Self>),
    Lam(Pat, Box<Self>),
    Grp(Box<Self>),
    Neg(Box<Self>),
    Tup(Vec<Self>),
    List(Vec<Self>),
    /// Local infix declarations introduce fixities scoped only within
    /// the body
    Let(InfixDecl, Box<Self>),
}

impl Expr {
    pub const UNIT: Self = Self::Tup(vec![]);
}

#[derive(Clone, Copy, Debug)]
pub enum Infix {
    Standard(Symbol),
    Promoted(Symbol),
}

impl Infix {
    pub const fn symbol(&self) -> Symbol {
        match self {
            Infix::Standard(s) | Infix::Promoted(s) => *s,
        }
    }

    pub fn as_ident(self) -> Ident {
        match self {
            Infix::Standard(sym) => Ident::Infix(sym),
            Infix::Promoted(sym) => (if sym.starts_with(|c: char| c.is_uppercase()) {
                Ident::Upper
            } else {
                Ident::Lower
            })(sym),
        }
    }
}

impl PartialEq<Symbol> for Infix {
    fn eq(&self, other: &Symbol) -> bool {
        self.symbol() == *other
    }
}

impl PartialEq<Ident> for Infix {
    fn eq(&self, other: &Ident) -> bool {
        match (self, other) {
            (Self::Promoted(pr), Ident::Upper(s) | Ident::Lower(s)) => pr == s,
            (Self::Standard(op), Ident::Infix(s)) => op == s,
            _ => false,
        }
    }
}

impl PartialEq for Infix {
    fn eq(&self, other: &Self) -> bool {
        self.symbol() == other.symbol()
    }
}

impl Eq for Infix {}

impl std::hash::Hash for Infix {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.symbol().hash(state)
    }
}

impl std::fmt::Display for Infix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Infix::Standard(s) => write!(f, "{s}"),
            Infix::Promoted(s) => {
                if s.len() == 1 && s.ends_with("'") {
                    write!(f, "`{s}`")
                } else {
                    write!(f, "'{s}")
                }
            }
        }
    }
}

impl From<Infix> for Ident {
    fn from(infix: Infix) -> Self {
        infix.as_ident()
    }
}

impl std::borrow::Borrow<Symbol> for Infix {
    fn borrow(&self) -> &Symbol {
        match self {
            Infix::Standard(s) | Infix::Promoted(s) => s,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ident {
    Nil,
    Commas(usize),
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
}

impl Ident {
    pub const fn is_unit(&self) -> bool {
        matches!(self, Self::Commas(0))
    }

    pub const fn is_infix(&self) -> bool {
        matches!(self, Self::Infix(_))
    }

    /// Returns the length of the identifier, where `Infix`
    /// identifiers are wrapped in parentheses
    pub fn width(&self) -> usize {
        self.len() + if self.is_infix() { 2 } else { 0 }
    }

    pub fn len(&self) -> usize {
        match self {
            Ident::Nil => 2,
            Ident::Commas(n) => 2 + n,
            Ident::Upper(s) | Ident::Lower(s) | Ident::Infix(s) => s.len(),
        }
    }

    pub fn as_str<'a>(&'a self) -> &'a str {
        match self {
            Ident::Nil => "[]",
            Ident::Commas(k) => {
                let mut buf = vec![];
                '('.encode_utf8(&mut buf);
                for _ in 0..*k {
                    ','.encode_utf8(&mut buf);
                }
                ')'.encode_utf8(&mut buf);
                unsafe { std::mem::transmute::<_, &'a str>(&buf[..]) }
            }
            Ident::Upper(_) => todo!(),
            Ident::Lower(_) => todo!(),
            Ident::Infix(_) => todo!(),
        }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ident::Nil => write!(f, "[]"),
            Ident::Commas(k) => {
                write!(f, "(")?;
                for _ in 0..*k {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            Ident::Upper(s) | Ident::Lower(s) | Ident::Infix(s) => s.fmt(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pat {
    Wild,
    Lit(Literal),
    Var(Symbol),
    Neg(Box<Self>),
    Con(Symbol, Vec<Self>),
    Tup(Vec<Self>),
    Arr(Vec<Self>),
    Lnk(Box<Self>, Box<Self>),
    As(Symbol, Box<Self>),
}

macro_rules! from_empty {
    ($ty:tt $name:ident $variant:ident $($e:expr)?) => {
        impl From<$ty> for $name {
            fn from(_: $ty) -> Self {
                $name::$variant$(($e))?
            }
        }
    };
    (
        $($t0:tt $t1:tt $t2:tt $($t3:expr)?),*
    ) => {
        $(
            from_empty! { $t0 $t1 $t2 $($t3)? }
        )*
    };
}

from_empty! {
    () Expr Tup vec![],
    () Pat Tup vec![],
    () Ident Commas 0,
    [(); 0] Expr List vec![],
    [(); 0] Pat Arr vec![],
    [(); 0] Ident Nil
}

pub trait Visit
where
    Self: Sized,
{
    fn visit_ast(&mut self, ast: &Ast) {
        walk_ast(self, ast)
    }

    fn visit_expr(&mut self, expr: &Expr) {
        walk_expr(self, expr)
    }
}

pub trait VisitMut
where
    Self: Sized,
{
    fn visit_ast_mut(&mut self, ast: &mut Ast) {
        walk_ast_mut(self, ast)
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        walk_expr_mut(self, expr)
    }
}

pub fn walk_ast<V>(visitor: &mut V, ast: &Ast)
where
    V: Visit,
{
    ast.exprs
        .iter()
        .for_each(|decl| visitor.visit_expr(&decl.expr))
}

pub fn walk_ast_mut<V>(visitor: &mut V, ast: &mut Ast)
where
    V: VisitMut,
{
    ast.exprs
        .iter_mut()
        .for_each(|decl| visitor.visit_expr_mut(&mut decl.expr))
}

pub fn walk_expr<V>(visitor: &mut V, expr: &Expr)
where
    V: Visit,
{
    match expr {
        Expr::Lit(_) | Expr::Var(_) => (),
        Expr::App(f, x) => {
            visitor.visit_expr(f);
            visitor.visit_expr(x);
        }
        Expr::Bin(l, _, r) => {
            visitor.visit_expr(l);
            visitor.visit_expr(r);
        }
        Expr::Lam(_, expr) => visitor.visit_expr(expr),
        Expr::Grp(expr) | Expr::Neg(expr) => visitor.visit_expr(expr),
        Expr::Tup(xs) | Expr::List(xs) => xs.iter().for_each(|expr| visitor.visit_expr(expr)),
        Expr::Let(_, body) => visitor.visit_expr(body),
    }
}

pub fn walk_expr_mut<V>(visitor: &mut V, expr: &mut Expr)
where
    V: VisitMut,
{
    match expr {
        Expr::Lit(_) | Expr::Var(_) => (),
        Expr::App(l, r) | Expr::Bin(l, _, r) => {
            visitor.visit_expr_mut(l);
            visitor.visit_expr_mut(r);
        }
        Expr::Lam(_, expr) => visitor.visit_expr_mut(expr),
        Expr::Grp(expr) | Expr::Neg(expr) => visitor.visit_expr_mut(expr),
        Expr::Tup(xs) | Expr::List(xs) => {
            xs.iter_mut().for_each(|expr| visitor.visit_expr_mut(expr))
        }
        Expr::Let(_, body) => visitor.visit_expr_mut(body),
    }
}
