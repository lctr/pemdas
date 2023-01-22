use std::fmt;

use super::color::{AnsiColor, Color, Rainbow, Rgb};

macro_rules! __len {
    () => { 0 };
    ($t:tt $($ts:tt)*) => {
        1 $(+ __len! { $ts})*
    };
}

macro_rules! variant_bytetypes {
    (
        #$config:ident
        $(#[$outer:meta])*
        $vis:vis enum $name:ident {
            $(#[$inner:meta])*
            $(
                #$field:ident
                $(? $pred:ident)?
                $(. $get:ident)?
                : $set:ident
                $(^ $toggle:ident)?
                $variant:ident = $discr:literal
            ),+ $(,)?
        }
    ) => {
        $(#[$outer])*
        $vis enum $name {
            $(#[$inner])*
            $($variant = $discr),+
        }

        impl PartialEq<u8> for $name {
            fn eq(&self, other: &u8) -> bool {
                (*self as u8) == *other
            }
        }

        impl PartialEq<$name> for u8 {
            fn eq(&self, other: &$name) -> bool {
                *self == (*other as u8)
            }
        }


        impl $name {
            const VARIANT_COUNT: usize = __len! { $($variant)+ };
            pub const ALL: [Self; Self::VARIANT_COUNT] = [$(Self::$variant,)+];

            pub const fn as_str(&self) -> &'static str {
                match self {
                    $(Self::$variant => { stringify! { $discr }}),+
                }
            }

            /// Returns the variant whose discriminant is equal to the
            /// given byte. If no such variant exists, then the first
            /// variant defined is returned.
            ///
            /// To return an `Option` instead, use `maybe_from_u8`.
            pub const fn from_u8(b: u8) -> Self {
                $(if b == $discr { return Self::$variant })+
                let all = [ $(Self::$variant,)+ ];
                all[0]
            }

            pub const fn maybe_from_u8(b: u8) -> Option<Self> {
                 $(if b == $discr { return Some(Self::$variant) })+
                 None
            }
        }

        $(
            #[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
            $vis struct $variant;

            impl From<$variant> for $name {
                fn from(_: $variant) -> Self {
                    Self::$variant
                }
            }

            impl $variant {
                pub const BYTE: u8 = $discr;

                pub const STR: &'static str = stringify!($discr);

                pub const fn as_str(&self) -> &str {
                    Self::STR
                }

                pub const fn as_byte(self) -> u8 {
                    Self::BYTE
                }
            }

            impl AsRef<str> for $variant {
                fn as_ref(&self) -> &str {
                    Self::STR
                }
            }

            impl std::ops::Deref for $variant {
                type Target = $name;

                fn deref(&self) -> &Self::Target {
                    &$name::$variant
                }
            }

            impl PartialEq<u8> for $variant {
                fn eq(&self, other: &u8) -> bool {
                    *other == $discr
                }
            }

            impl PartialEq<$variant> for u8 {
                fn eq(&self, _other: &$variant) -> bool {
                    *self == $discr
                }
            }

            impl PartialEq<$name> for $variant {
                fn eq(&self, other: &$name) -> bool {
                    matches!(other, $name::$variant)
                }
            }

            impl PartialEq<$variant> for $name {
                fn eq(&self, _other: &$variant) -> bool {
                    matches!(self, Self::$variant)
                }
            }
        )+

        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $config {
            $(pub(crate) $field: Option<$variant>,)+
            pub(crate) fg_color: Option<Color>,
            pub(crate) bg_color: Option<Color>,
        }

        impl Default for $config {
            fn default() -> Self {
                Self::DEFAULT
            }
        }

        impl $config {
            const DEFAULT: Self = Self {
                $($field: None,)+
                fg_color: None,
                bg_color: None
            };

            pub fn new() -> Self {
                Default::default()
            }

            #[inline]
            pub(crate) fn set_format(self, setting: $name) -> Self {
                match setting {
                    $($name::$variant => self.$set($variant)),+
                }
            }

            pub(crate) fn reset_format(mut self, setting: $name) -> Self {
                match setting {
                    $($name::$variant => {
                        self.$field.take();
                    }),+
                };
                self
            }

            pub(crate) fn toggle_format(mut self, setting: $name) -> Self {
                match setting {
                    $($name::$variant => {
                        match &mut self.$field {
                            x@ Some(_) => *x = None,
                            x @ None => *x = Some($variant)
                        };
                    }),+
                };
                self
            }

            pub(crate) fn bytes(&self) -> impl Iterator<Item = u8> {
                self.non_color_bytes()
                    .chain(self.color_bytes())

            }

            pub(crate) fn non_color_bytes(&self) -> impl Iterator<Item = u8> {
                [$(self.$field.map(|_| $variant::BYTE),)+]
                    .into_iter()
                    .filter_map(|x| x)
            }

            pub(crate) fn color_bytes(&self) -> impl Iterator<Item = u8> {
                self.fg_color
                    .into_iter()
                    .flat_map(|c| c.fg_bytes())
                    .chain(self.bg_color
                        .into_iter()
                        .flat_map(|c| c.bg_bytes())
                    )
            }
        }

        #[allow(unused)]
        impl $config {
            $(
                pub const fn $set(self, value: $variant) -> Self {
                    Self {
                        $field: Some(value),
                        ..self
                    }
                }

                $(
                    pub(crate) const fn $pred(&self) -> bool {
                        matches!(&self.$field, Some(_))
                    }
                )?

                $(
                    pub(crate) const fn $toggle(self) -> Self {
                        Self {
                            $field: match self.$field {
                                Some(_) => None,
                                None => Some($variant)
                            },
                            ..self
                        }
                    }
                )?

                $(
                    pub(crate) const fn $get(&self) -> Option<&$variant> {
                        &self.$field
                    }
                )?
            )+
        }
    };
}

variant_bytetypes! {
    #Config
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    #[repr(u8)]
    pub enum AnsiFormat {
        # reset_prev
        ? has_reset
        : set_reset
        ^ toggle_reset
        Reset = 0,
        # bold
        ? is_bold
        : set_bold
        ^ toggle_bold
        Bold = 1,
        # dim
        ? is_dim
        : set_dim
        ^ toggle_dim
        Dim = 2,
        # italic
        ? is_italic
        : set_italic
        ^ toggle_italic
        Italic = 3,
        # underlined
        ? is_underlined
        : set_underlined
        ^ toggle_underlined
        Underlined = 4,
        # blinking
        ? is_blinking
        : set_blinking
        ^ toggle_blinking
        Blinking = 5,
        # invert
        ? is_inverted
        : set_inverted
        ^ toggle_inverted
        Inverted = 7,
        # hidden
        ? is_hidden
        : set_hidden
        ^ toggle_hidden
        Hidden = 8,
        # strikethrough
        ? is_strikethrough
        : set_strikethrough
        Strikethrough = 9,
    }
}

impl Config {
    pub(crate) const fn set_fg_color(self, color: Color) -> Self {
        Self {
            fg_color: Some(color),
            ..self
        }
    }

    pub(crate) fn set_bg_color(self, color: Color) -> Self {
        Self {
            bg_color: Some(color),
            ..self
        }
    }

    pub(crate) fn reset_colors(mut self) -> Self {
        self.fg_color.take();
        self.bg_color.take();
        self
    }

    pub(crate) fn write_start(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\u{1b}[")?;
        let mut empty = Some(());
        let mut bytes = self.bytes();
        if let Some(n) = bytes.next() {
            empty.take();
            write!(f, "{n}")?;
        }
        for esc in bytes {
            empty.take();
            write!(f, ";{esc}")?;
        }
        if empty.is_some() {
            write!(f, "0")?;
        }
        write!(f, "m")?;
        Ok(())
    }

    pub(crate) fn write_end(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\u{1b}[0m")
    }

    #[allow(unused)]
    pub(crate) fn style_str_start(&self) -> String {
        let mut buf = String::with_capacity(16);
        buf.push_str("\u{1b}[");
        let len = buf.len();
        let mut iter = self.bytes();
        if let Some(b) = iter.next() {
            buf.push_str(&*format!("{b}"));
        }
        iter.for_each(|s| {
            buf.push(';');
            buf.push_str(&*format!("{s}"));
        });
        if buf.len() == len {
            buf.push_str("0")
        }
        buf.push('m');
        buf
    }

    #[allow(unused)]
    pub(crate) fn fmt_display<S>(&self, item: S, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        S: fmt::Display,
    {
        self.write_start(f)?;
        write!(f, "{item}")?;
        self.write_end(f)
    }

    #[allow(unused)]
    pub(crate) fn fmt_debug<S>(&self, item: S, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        S: fmt::Debug,
    {
        self.write_start(f)?;
        write!(f, "{item:?}")?;
        self.write_end(f)
    }
}

pub struct Style<S>(S, Config);

impl<S> Style<S> {
    pub fn new(item: S) -> Self {
        Self(item, Config::default())
    }

    pub(crate) const fn config(&self) -> &Config {
        &self.1
    }

    pub const fn inner(&self) -> &S {
        &self.0
    }

    pub fn into_inner(self) -> S {
        self.0
    }

    #[inline]
    fn set_fg(mut self, color: Color) -> Self {
        self.1 = self.1.set_fg_color(color);
        self
    }

    #[inline]
    fn set_bg(mut self, color: Color) -> Self {
        self.1 = self.1.set_bg_color(color);
        self
    }

    #[inline]
    pub fn set_fg_rgb(self, r: u8, g: u8, b: u8) -> Self {
        self.set_fg(Color::Rgb(Rgb(r, g, b)))
    }

    #[inline]
    pub fn set_bg_rgb(self, r: u8, g: u8, b: u8) -> Self {
        self.set_bg(Color::Rgb(Rgb(r, g, b)))
    }

    pub fn share_iter<'s, I>(&'s self, iter: I) -> impl Iterator<Item = Style<I::Item>> + '_
    where
        I: IntoIterator + 's,
    {
        iter.into_iter().map(|item| Style(item, self.1))
    }

    pub fn prepend<T>(self, other: T) -> Style<And<T, S>> {
        Style(And(other, self.0), self.1)
    }

    pub fn append<T>(self, other: T) -> Style<And<S, T>> {
        Style(And(self.0, other), self.1)
    }

    pub fn then_with<T>(
        self,
        other: T,
        mut f: impl FnMut(Style<T>) -> Style<T>,
    ) -> Then<Style<S>, Style<T>> {
        let code = self.1;
        Then(self, f(Style(other, code)))
    }

    pub const fn fresh_suffix<R>(self, right: R) -> Then<Self, R> {
        Then(self, right)
    }

    pub const fn fresh_prefix<L>(self, left: L) -> Then<L, Self> {
        Then(left, self)
    }

    pub fn map<F, T>(self, mut f: F) -> Style<T>
    where
        F: FnMut(S, Config) -> (T, Config),
    {
        let Self(s, style) = self;
        let (t, style) = f(s, style);
        Style(t, style)
    }

    pub fn map_ref<F, T>(&self, mut f: F) -> Style<T>
    where
        F: FnMut(&S, Config) -> (T, Config),
    {
        let Self(s, style) = self;
        let (t, style) = f(s, *style);
        Style(t, style)
    }

    pub fn reset_colors(self) -> Self {
        let Self(s, style) = self;
        Self(s, style.reset_colors())
    }

    pub fn fmt_display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        Self: fmt::Display,
    {
        // self.config().fmt_display(self.inner(), f)
        fmt::Display::fmt(&self, f)
    }

    pub fn fmt_debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        Self: fmt::Debug,
    {
        fmt::Debug::fmt(&self, f)
    }

    pub fn debug(&self) -> Debug<'_, S> {
        Debug(self)
    }

    pub fn print(&self, nl: bool)
    where
        Self: fmt::Display,
    {
        if nl {
            println!("{}", &self)
        } else {
            print!("{}", self)
        }
    }
}

/// Helper struct for handling styled items in debug mode.
///
/// In debug mode, this struct will simply print the same thing as the
/// inner item, with no styling.
///
/// In display mode, this struct will apply the associated styling,
/// printing the inner item as though it were in debug mode.
pub struct Debug<'a, S>(&'a Style<S>);

impl<S> std::fmt::Display for Debug<'_, S>
where
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.config().fmt_debug(self.0.inner(), f)
    }
}

impl<S> std::fmt::Debug for Debug<'_, S>
where
    S: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        std::fmt::Debug::fmt(self.0.inner(), f)
    }
}

impl<S> Style<Result<S, fmt::Error>> {
    pub fn lift(self) -> Result<Style<S>, fmt::Error> {
        let Self(res, style) = self;
        res.map(|s| Style(s, style))
    }
}

impl<S> Clone for Style<S>
where
    S: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1)
    }
}

impl<S> Copy for Style<S> where S: Copy {}

macro_rules! style_setters {
    (
        $([$name:ident.$id0:ident$(($cat:ident))?] { $($ts:tt)+ })*
    ) => {
        $(style_setters! { [$name.$id0$(($cat))?] $($ts)+ })*
        style_setters! {
            >> $(
                #{ $name.$id0$(($cat))? } { $($ts)+ }
            )*
        }
    };
    (
        [$name:ident.FORMAT]
        $(| $format:ident/$setter:ident/$unsetter:ident/$toggler:ident)+
    ) => {
        impl<S> $name<S> {
            $(
                pub fn $setter(mut self) -> Self {
                    self.1 = self.1.set_format(AnsiFormat::$format);
                    self
                }

                pub fn $unsetter(mut self) -> Self {
                    self.1 = self.1.reset_format(AnsiFormat::$format);
                    self
                }

                pub fn $toggler(mut self) -> Self {
                    self.1 = self.1.toggle_format(AnsiFormat::$format);
                    self
                }
            )+
        }
    };
    (
        [$name:ident.COLOR(ANSI)]
        $(
            $(| $color:ident/$fgsetter:ident/$bgsetter:ident)+
        ),+
    ) => {
        impl<S> $name<S> {
            $(
                $(
                    pub fn $fgsetter(self) -> Self {
                        self.set_fg(Color::Ansi(AnsiColor::$color))
                    }

                    pub fn $bgsetter(self) -> Self {
                        self.set_bg(Color::Ansi(AnsiColor::$color))
                    }
                )+
            )+
        }
    };
    (
        [$name:ident.COLOR(RGB)]
        $(
            $(
                $(#[$above:meta])*
                | $color:ident (
                    $(r =)? $r:literal,
                    $(g =)? $g:literal,
                    $(b =)? $b:literal
                ) /$fgsetter:ident /$bgsetter:ident
            )+
        ),+
    ) => {
        impl<S> $name<S> {
            $(
                $(
                    #[doc = "Sets the foreground color to `"]
                    #[doc = stringify!($color)]
                    #[doc = "` (R = "]
                    #[doc = ", G = "]
                    #[doc = stringify!($g)]
                    #[doc = ", B = "]
                    #[doc = stringify!($b)]
                    #[doc = ")"]
                    pub fn $fgsetter(self) -> Self {
                        self.set_fg(Color::Rgb(Rgb($r, $g, $b)))
                    }

                    #[doc = concat!(
                        "Sets the background color to `", stringify!($color),
                        "` (R = ", $r, ", G = ", $g, ", B = ", $b, ")"
                    )]
                    pub fn $bgsetter(self) -> Self {
                        self.set_bg(Color::Rgb(Rgb($r, $g, $b)))
                    }
                )+
            )+
        }
    };
    (
        >> $(
            #{
                $name:ident.$id0:ident$(($cat:ident))?
            } {
                $(
                    // portions from previous macro invocations that
                    // won't be included in the trait definition's methods
                    | $lbl:ident $(($($lit:literal),+))?
                    $(/ $methods:ident)+
                )+
            }
        )*
    ) => {
        style_setters! {
            #Paint {
                $($($($methods)+)+)*
            }
        }
    };
    (
        #$paint:ident { $($method:ident)+ }
    ) => {
        /// A public interface providing shortcuts to wrap types in a
        /// `Style` instance so as to skip having to call
        /// `Style::new(...)` before styling. However, unlike simply
        /// calling `Style::new(...)` with a given type, these methods
        /// wrap a *reference* of a given type.
        ///
        /// All of the methods in this trait are effectively shared by
        /// the `Style` type.
        ///
        /// Note that all types will implement this trait so as to
        /// allow styling types for both `Display` and `Debug`
        /// implementations.
        pub trait $paint<T>
        where T: std::fmt::Display
        {
            fn style_owned(self) -> Style<Self>
            where Self: Sized {
                Style::new(self)
            }

            $(fn $method<'a>(&'a self) -> Style<&'a T>;)+
        }

        impl<T> $paint<T> for T
        where T: std::fmt::Display
        {
            $(
                fn $method<'a>(&'a self) -> Style<&'a T> {
                    Style::new(self).$method()
                }
            )+
        }
    };
}

style_setters! {
    [Style.FORMAT] {
        | Bold              /set_bold
                            /unset_bold
                            /toggle_bold
        | Dim               /set_dim
                            /unset_dim
                            /toggle_dim
        | Italic            /set_italic
                            /unset_italic
                            /toggle_italic
        | Underlined        /set_underlined
                            /unset_underlined
                            /toggle_underlined
        | Blinking          /set_blinking
                            /unset_blinking
                            /toggle_blinking
        | Inverted          /set_inverted
                            /unset_inverted
                            /toggle_inverted
        | Hidden            /set_hidden
                            /unset_hidden
                            /toggle_hidden
        | Strikethrough     /set_strikethrough
                            /unset_strikethrough
                            /toggle_strikethrough
    }
    [Style.COLOR(ANSI)] {
        | Normal        /reset_fg               /reset_bg
        | Black         /set_fg_black           /set_bg_black
        | Red           /set_fg_red             /set_bg_red
        | Green         /set_fg_green           /set_bg_green
        | Yellow        /set_fg_yellow          /set_bg_yellow
        | Blue          /set_fg_blue            /set_bg_blue
        | Magenta       /set_fg_magenta         /set_bg_magenta
        | Cyan          /set_fg_cyan            /set_bg_cyan
        | White         /set_fg_white           /set_bg_white
        | LightBlack    /set_fg_light_black     /set_bg_light_black
        | LightRed      /set_fg_light_red       /set_bg_light_red
        | LightGreen    /set_fg_light_green     /set_bg_light_green
        | LightYellow   /set_fg_light_yellow    /set_bg_light_yellow
        | LightBlue     /set_fg_light_blue      /set_bg_light_blue
        | LightMagenta  /set_fg_light_magenta   /set_bg_light_magenta
        | LightCyan     /set_fg_light_cyan      /set_bg_light_cyan
        | LightWhite    /set_fg_light_white     /set_bg_light_white
    }
    [Style.COLOR(RGB)] {
        | Maroon        (128, 0, 0)     /set_fg_maroon  /set_bg_maroon
        | Orange        (255, 128, 0)   /set_fg_orange  /set_bg_orange
        | Crimson       (220, 20, 60)   /set_fg_crimson /set_bg_crimson
        | Teal          (0, 128, 128)   /set_fg_teal    /set_bg_teal
        | Azure         (0, 128, 255)   /set_fg_azure   /set_bg_azure
        | Purple        (128, 0, 128)   /set_fg_purple  /set_bg_purple
        | Indigo        (75, 0, 130)    /set_fg_indigo  /set_bg_indigo
        | Violet        (238, 130, 238) /set_fg_violet  /set_bg_violet
    }
}

pub struct And<A, B>(A, B);

impl<A, B> And<A, B> {
    pub fn new(a: A, b: B) -> Self {
        Self(a, b)
    }

    pub fn and<C>(self, other: C) -> And<And<A, B>, C> {
        And(self, other)
    }

    pub fn display_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        A: fmt::Display,
        B: fmt::Display,
    {
        write!(f, "{}", self)
    }

    pub fn print(&self, nl: bool)
    where
        Self: fmt::Display,
    {
        if nl {
            println!("{}", &self)
        } else {
            print!("{}", self)
        }
    }
}

impl<A: Clone, B: Clone> Clone for And<A, B> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }
}

impl<A: Copy, B: Copy> Copy for And<A, B> {}

pub struct Then<A, B>(A, B);

impl<A, B> Then<A, B> {
    pub fn then<C>(self, other: C) -> Then<Then<A, B>, C> {
        Then(self, other)
    }

    pub fn styled(self) -> Style<Self> {
        Style::new(self)
    }

    pub fn display_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        A: fmt::Display,
        B: fmt::Display,
    {
        write!(f, "{}", self)
    }

    pub fn print(&self, nl: bool)
    where
        Self: fmt::Display,
    {
        if nl {
            println!("{}", &self)
        } else {
            print!("{}", self)
        }
    }
}

macro_rules! impl_style_fmts {
    (
        for Style: $($tr:ident),+ $(| $($ts:tt)+)?
    ) => {
        $(impl<S> fmt::$tr for Style<S>
        where
            S: fmt::$tr,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.config().write_start(f)
                    .and(self.0.fmt(f))
                    .and(self.config().write_end(f))
            }
        })+

        $(
            impl_style_fmts! { for $($ts)+ }
        )?
    };
    (
        for $id:ident<'_, $a:ident, $b:ident>(0, 1):
            $($tr:ident),+
            $(| $($ts:tt)+)?
    ) => {
        $(
            impl<$a, $b> fmt::$tr for $id<'_, $a, $b>
            where
                $a: fmt::$tr,
                $b: fmt::$tr,
            {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    self.0.fmt(f).and(self.1.fmt(f))
                }
            }
        )+

        $(
            impl_style_fmts! { for $($ts)+ }
        )?
    };
        (
        for $id:ident<$a:ident, $b:ident>(0, 1):
            $($tr:ident),+
            $(| $($ts:tt)+)?
    ) => {
        $(
            impl<$a, $b> fmt::$tr for $id<$a, $b>
            where
                $a: fmt::$tr,
                $b: fmt::$tr,
            {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    self.0.fmt(f).and(self.1.fmt(f))
                }
            }
        )+

        $(
            impl_style_fmts! { for $($ts)+ }
        )?
    };
}

impl_style_fmts! {
    for Style:
        Display, Debug, Binary, Octal, LowerHex, LowerExp, UpperHex, UpperExp, Pointer
    | And<A, B>(0, 1):
        Display, Debug, Binary, Octal, LowerHex, LowerExp, UpperHex, UpperExp, Pointer
    | Then<A, B>(0, 1):
        Display, Debug, Binary, Octal, LowerHex, LowerExp, UpperHex, UpperExp, Pointer
}

pub fn red<S>(item: S) -> Style<S> {
    Style::new(item).set_fg_red()
}

pub fn blue<S>(item: S) -> Style<S> {
    Style::new(item).set_fg_blue()
}

pub fn green<S>(item: S) -> Style<S> {
    Style::new(item).set_fg_green()
}

pub fn yellow<S>(item: S) -> Style<S> {
    Style::new(item).set_fg_yellow()
}

pub fn wrapped_blue<L, R, S>((left, right): (L, R), item: S) -> Style<And<And<L, Style<S>>, R>> {
    let a = Style::new(left).append(blue(item)).append(right);
    a
}

pub struct Highlighted<T>(T, Color);

impl<T> From<Style<T>> for Highlighted<T> {
    fn from(style: Style<T>) -> Self {
        let color = style
            .config()
            .fg_color
            .unwrap_or_else(|| Color::Ansi(AnsiColor::Normal));
        let item = style.into_inner();
        Self(item, color)
    }
}

impl<T> From<Highlighted<T>> for Style<T> {
    fn from(hl: Highlighted<T>) -> Self {
        Style::new(hl.0).set_fg(hl.1)
    }
}

impl<T> fmt::Display for Highlighted<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Style::new(&self.0).set_fg(self.1).fmt_display(f)
    }
}

pub trait Highlighter {
    fn color(&self) -> Color;

    fn highlight<T>(&self, item: T) -> Highlighted<T> {
        Highlighted(item, self.color())
    }

    fn highlight_with<T>(&self, item: T, color: Color) -> Highlighted<T> {
        Highlighted(item, color)
    }
}

impl Highlighter for Rainbow {
    fn color(&self) -> Color {
        Rainbow::color(self)
    }
}

#[macro_export]
macro_rules! Show {
    ($id:ident =<< $ex:expr) => {
        struct Show<'t, T>(&'t T);
        impl<'t, T> Show<'t, T>
        where
            T: std::fmt::Display,
        {
            #[inline]
            #[allow(unused)]
            pub fn print(&self) {
                print!("{}", self)
            }

            #[inline]
            #[allow(unused)]
            pub fn println(&self) {
                println!("{}", self)
            }
        }
        impl<T> std::fmt::Display for Show<'_, T>
        where
            T: std::fmt::Display,
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        let $id = $ex;
        let $id = Show(&$id);
    };
    (| $m:ident(.)) => {
        struct Show<'t, T>(&'t T);
        impl<'t, T> Show<'t, T>
        where
            T: std::fmt::Display,
        {
            #[inline]
            fn print(&self) {
                print!("{}", self)
            }

            #[inline]
            fn println(&self) {
                println!("{}", self)
            }
        }
        impl<T> std::fmt::Display for Show<'_, T>
        where
            T: std::fmt::Display,
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.$m(f)
            }
        }
    };
    ($name:ty | $m:ident(.)) => {
        struct Show<'t>(&'t $name);
        impl<'t> Show<'t> {
            #[inline]
            fn print(&self) {
                print!(f, "{}", self)
            }

            #[inline]
            fn println(&self) {
                println!(f, "{}", self)
            }
        }
        impl std::fmt::Display for Show<'_>
        where
            $name: std::fmt::Display,
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.$m(f)
            }
        }
    };
    ($name:ty) => {
        struct Show<'t>(&'t $name);
        impl<'t> Show<'t>
        where
            $name: std::fmt::Display,
        {
            #[inline]
            fn print(&self) {
                print!(f, "{}", self)
            }

            #[inline]
            fn println(&self) {
                println!(f, "{}", self)
            }
        }
        impl std::fmt::Display for Show<'_>
        where
            $name: std::fmt::Display,
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }
    };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn rainbow_paren() {
        let rb = Rainbow::default();
        struct Group(i32, char, Option<Box<Group>>);
        let g = (0..5)
            .zip(['+', '-', '*'].into_iter().cycle())
            .fold(Group(6, '~', None), |grp, (n, c)| {
                Group(n, c, Some(Box::new(grp)))
            });
        struct P<'a>(&'a Rainbow, &'a Group);
        impl fmt::Display for P<'_> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let Self(rb, grp) = self;
                let Group(n, c, g) = grp;
                write!(f, "{n} {c}")?;
                if let Some(g) = g {
                    let color = rb.tick().color();
                    write!(f, " ")?;
                    rb.highlight_with('(', color).fmt(f)?;
                    write!(f, "{}", P(rb, g.as_ref()))?;
                    rb.highlight_with(')', color).fmt(f)?;
                }
                Ok(())
            }
        }
        println!("{}", P(&rb, &g))
    }
}
