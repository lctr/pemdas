use std::mem;

use fnv::FnvHashMap;

use super::symbol::Symbol;

type Str = &'static str;

/// String interner. Instead of allocating a new string during the
/// compilation process, all strings are instead interned and mapped
/// to instances of type `Symbol`, which is `Copy` (unlike `String`)
/// and hence more lightweight.
#[derive(Debug)]
struct Lexicon {
    map: FnvHashMap<Str, Symbol>,
    vec: Vec<Str>,
    buf: String,
    all: Vec<String>,
}

impl Lexicon {
    // /// Initial value just randomly guessed.
    // /// This could/should maybe be optimized later.
    // pub const BASE_CAPACITY: usize = 100;

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            map: FnvHashMap::with_capacity_and_hasher(cap, Default::default()),
            vec: Vec::new(),
            buf: String::with_capacity(cap),
            all: Vec::new(),
        }
    }

    #[allow(unused)]
    fn with_reserved(strings: &[&'static str]) -> Self {
        let mut this = Self::with_capacity(strings.len());
        for s in strings {
            this.intern(*s);
        }
        this
    }

    fn intern(&mut self, string: &str) -> Symbol {
        if let Some(&id) = self.map.get(string) {
            return id;
        }

        let string = unsafe { self.alloc(string) };
        let id = Symbol(self.map.len() as u32);

        self.map.insert(string, id);
        self.vec.push(string);

        debug_assert!(self.lookup(id) == string);
        debug_assert!(self.intern(string) == id);

        id
    }

    fn lookup(&self, id: Symbol) -> &'static str {
        self.vec[id.0 as usize]
    }

    unsafe fn alloc(&mut self, string: &str) -> &'static str {
        let cap = self.buf.capacity();
        if cap < self.buf.len() + string.len() {
            // just doubling isn't enough -- need to ensure the new string
            // actually fits
            let new_cap = (cap.max(string.len()) + 1).next_power_of_two();
            let new_buf = String::with_capacity(new_cap);
            let old_buf = mem::replace(&mut self.buf, new_buf);
            self.all.push(old_buf);
        }

        let interned = {
            let start = self.buf.len();
            self.buf.push_str(string);
            &self.buf[start..]
        };

        &*(interned as *const str)
    }
}

macro_rules! __force_expr {
    ($e:expr) => {{
        $e
    }};
}

macro_rules! count {
    ($t:tt) => {{
        1
    }};
    ($t:tt $($ts:tt)+) => {{
        __force_expr! { 1 $(+ count! { $ts })+ }
    }};
}

macro_rules! symbols {
    (
        | $name:ident $txt:literal $(.$pred:ident)?
        $(| $ns:ident $ts:literal $(.$ps:ident)?)*
    ) => {
        pub const $name: Symbol = Symbol(0);

        symbols! {
            [$name $txt $(.$pred)?] $(| $ns $ts $(.$ps)?)*
        }
    };
    ( [$($name:ident $txt:literal $(.$pred:ident)?)+]) => {

        const PRE_COUNT: usize = count! { $($txt)+ };
        /// An array containing string literals corresponding to
        /// predefined `Symbol`s, i.e., strings for which a known
        /// `Symbol` exists (and thus allowing specific `Symbol`
        /// instances to be cached and referenced by name).
        ///
        /// The index of a given `&str` in `PREDEFINED` is a usize
        /// value `n` that, when coerced, is equal to the inner `u32`
        /// value held by the corresponding `Symbol`. In other words,
        /// the following expression returns `true`, where `INTERNER`
        /// is the (thread-local) interner:
        ///
        /// ```ignore
        /// PREDEFINED.into_iter()
        ///     .enumerate()
        ///     .map(|(n, s)| (s, Symbol(n as u32)))
        ///     .all(|(string, symbol)| INTERNER.intern(string) == symbol)
        /// ```
        pub const PREDEFINED: [&'static str; PRE_COUNT] = [
            $($txt),+
        ];

        impl Default for Lexicon {
            fn default() -> Self {
                Self::with_reserved(&PREDEFINED)
            }
        }

        thread_local! {
            static LEXICON: Shared<Lexicon> = {
                use std::rc::Rc;
                use std::cell::RefCell;
                Rc::new(RefCell::new(Lexicon::default()))
            };
        }

        impl Symbol {
            pub const PREDEFINED: [&'static str; PRE_COUNT] = PREDEFINED;

            $(
                pub const $name: Self = $name;

                $(
                    #[inline]
                    pub fn $pred(&self) -> bool {
                        *self == Self::$name
                    }
                )?
            )+
        }

    };
    (
        [$($names:ident $txts:literal $(.$preds:ident)?)+]
        | $name:ident $txt:literal $(.$pred:ident)?
        $(| $ns:ident $ts:literal $(.$ps:ident)?)*
    ) => {
        pub const $name: Symbol = Symbol(count! { $($txts)+ });

        symbols! {
            [$($names $txts $(.$preds)?)+ $name $txt $(.$pred)?]
            $(| $ns $ts $(.$ps)?)*
        }
    };
}

pub type Shared<X> = std::rc::Rc<std::cell::RefCell<X>>;

#[derive(Clone, Copy)]
pub struct Interner(&'static std::thread::LocalKey<Shared<Lexicon>>);

impl Interner {
    #[inline]
    pub fn lookup(&self, sym: Symbol) -> &'static str {
        self.0.with(|lex| lex.borrow().lookup(sym))
    }

    #[inline]
    pub fn intern(&self, s: impl AsRef<str>) -> Symbol {
        self.0.with(|lex| lex.borrow_mut().intern(s.as_ref()))
    }

    pub fn intern_iter<I, J>(&self, iter: I) -> J
    where
        I: IntoIterator,
        I::Item: AsRef<str>,
        J: FromIterator<Symbol>,
    {
        self.0.with(|lex| {
            let mut lex = lex.borrow_mut();
            iter.into_iter().map(|s| lex.intern(s.as_ref())).collect()
        })
    }

    pub fn intern_n<S, const N: usize>(&self, ss: [S; N]) -> [Symbol; N]
    where
        S: AsRef<str>,
    {
        let mut array: [Symbol; N] = [Symbol(0); N];
        self.0.with(|lex| {
            let mut lex = lex.borrow_mut();
            for (s, sym) in ss.iter().zip(array.iter_mut()) {
                *sym = lex.intern(s.as_ref());
            }
        });
        array
    }
}

/// Alias to circumvent importing `INTERNER`.
#[inline]
pub fn intern(s: impl AsRef<str>) -> Symbol {
    INTERNER.intern(s)
}

/// Alias to circumvent importing `INTERNER`.
#[inline]
pub fn lookup(sym: Symbol) -> &'static str {
    INTERNER.lookup(sym)
}

symbols! {
    | EMPTY             ""          .is_empty
    | UNDERSCORE        "_"         .is_underscore
    | UNIT              "()"        .is_unit
    | NIL               "[]"        .is_nil
    | ARROW             "->"        .is_arrow
    | AT                "@"         .is_at
    | COLON             ":"         .is_colon
    | DOT               "."         .is_dot
    | DOT2              ".."        .is_2_dots
    | CASH              "$"         .is_cash
    | PLUS              "+"         .is_plus
    | DASH              "-"         .is_dash
    | STAR              "*"         .is_star
    | STAR2             "**"        .is_2_stars
    | CARET             "^"         .is_caret
    | CARET2            "^^"        .is_2_carets
    | FSLASH            "/"         .is_f_slash
    | BSLASH            "\\"        .is_b_slash
    | PERCENT           "%"         .is_percent
    | PIPE              "|"         .is_pipe
    | PIPE2             "||"        .is_2_pipes
    | AMPERSAND         "&"         .is_ampersand
    | AMPERSAND2        "&&"        .is_2_ampersands
    | FIXITY            "fixity"    .is_fixity
    | LEFT              "left"      .is_left
    | RIGHT             "right"     .is_right
    | UPPER_L           "L"         .is_upper_l
    | UPPER_R           "R"         .is_upper_r
}

pub static INTERNER: Interner = Interner(&LEXICON);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_predefined_count() {
        assert_eq!(PREDEFINED.len(), PRE_COUNT);
        assert_eq!(INTERNER.0.with(|lex| lex.borrow().map.len()), PRE_COUNT);
        assert!(INTERNER
            .0
            .with(|lex| lex.borrow().vec.as_slice() == PREDEFINED.as_slice()));
    }
}
