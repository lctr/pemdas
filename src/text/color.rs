#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum AnsiColor {
    Normal = 0,
    Black = 0x1E,
    Red = 0x1F,
    Green = 0x20,
    Yellow = 0x21,
    Blue = 0x22,
    Magenta = 0x23,
    Cyan = 0x24,
    White = 0x25,
    LightBlack = 0x5A,
    LightRed = 0x5B,
    LightGreen = 0x5C,
    LightYellow = 0x5D,
    LightBlue = 0x5E,
    LightMagenta = 0x5F,
    LightCyan = 0x60,
    LightWhite = 0x61,
}

impl Default for AnsiColor {
    fn default() -> Self {
        Self::Normal
    }
}

impl AnsiColor {
    /// Colors of the rainbow. Uses light red as orange, magenta as
    /// indigo and light magenta as violet.
    pub const RAINBOW: [Self; 7] = {
        use AnsiColor::*;
        [Red, LightRed, Yellow, Green, Blue, Magenta, LightMagenta]
    };

    /// All colors except for the default "normal" color.
    pub const ALL: [Self; 16] = {
        use AnsiColor::*;
        [
            Black,
            Red,
            Green,
            Yellow,
            Blue,
            Magenta,
            Cyan,
            White,
            LightBlack,
            LightRed,
            LightGreen,
            LightYellow,
            LightBlue,
            LightMagenta,
            LightCyan,
            LightWhite,
        ]
    };

    pub const fn fg(&self) -> Fg {
        Fg(*self)
    }

    pub const fn as_fg(&self) -> u8 {
        *self as u8
    }

    pub const fn bg(&self) -> Bg {
        Bg(*self)
    }

    pub const fn as_bg(&self) -> u8 {
        *self as u8
    }

    pub const fn rainbow(n: u8) -> Self {
        Self::RAINBOW[n as usize % Self::RAINBOW.len()]
    }

    pub const fn as_str(&self) -> &'static str {
        match self {
            AnsiColor::Normal => "0",
            AnsiColor::Black => "30",
            AnsiColor::Red => "31",
            AnsiColor::Green => "32",
            AnsiColor::Yellow => "33",
            AnsiColor::Blue => "34",
            AnsiColor::Magenta => "35",
            AnsiColor::Cyan => "36",
            AnsiColor::White => "37",
            AnsiColor::LightBlack => "90",
            AnsiColor::LightRed => "91",
            AnsiColor::LightGreen => "92",
            AnsiColor::LightYellow => "93",
            AnsiColor::LightBlue => "94",
            AnsiColor::LightMagenta => "95",
            AnsiColor::LightCyan => "96",
            AnsiColor::LightWhite => "97",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fg(pub(crate) AnsiColor);

pub const FG_VAL: u8 = 38;
pub const FG_BYTES: [u8; 2] = [b'3', b'8'];
pub const BG_VAL: u8 = 48;
pub const BG_BYTES: [u8; 2] = [b'4', b'8'];

impl std::fmt::Display for Fg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (self.0 as u8).fmt(f)
    }
}

impl std::fmt::Debug for Fg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (self.0 as u8).fmt(f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bg(pub(crate) AnsiColor);

impl std::fmt::Display for Bg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (self.0 as u8 + 10).fmt(f)
    }
}

impl std::fmt::Debug for Bg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (self.0 as u8 + 10).fmt(f)
    }
}

macro_rules! sat {
    ((+) $id:expr, x:expr) => {
        ($id).saturating_add($x:ident)
    };
    ((+) $($name:ident)?($(($es:expr, $rhs:expr)),+)) => {
        $($name)?($(($es).saturating_add($rhs)),+)
    };
    ((-) $id:expr, x:expr) => {
        ($id).saturating_sub($x:ident)
    };
    ((-) $($name:ident)?($(($es:expr, $rhs:expr)),+)) => {
        $($name)?($(($es).saturating_sub($rhs)),+)
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Rgb(pub u8, pub u8, pub u8);

impl Rgb {
    pub const MAX: Self = Self(u8::MAX, u8::MAX, u8::MAX);
    pub const MIN: Self = Self(0, 0, 0);
    pub const WHITE: Self = Self::MAX;
    pub const BLACK: Self = Self::MIN;

    pub const fn new(red: u8, green: u8, blue: u8) -> Self {
        Self(red, green, blue)
    }

    pub const fn from_hex_checked(val: u32) -> Option<Self> {
        if val < (2 << 23) {
            let r = ((val >> 16) & (u8::MAX as u32)) as u8;
            let g = ((val >> 8) & (u8::MAX as u32)) as u8;
            let b = (val & (u8::MAX as u32)) as u8;
            Some(Self(r, g, b))
        } else {
            None
        }
    }

    pub const unsafe fn from_hex_unchecked(val: u32) -> Self {
        let r = ((val >> 16) & (u8::MAX as u32)) as u8;
        let g = ((val >> 8) & (u8::MAX as u32)) as u8;
        let b = (val & (u8::MAX as u32)) as u8;
        Self(r, g, b)
    }

    pub fn from_hex_be_bytes(val: u32) -> Self {
        let bs = &val.to_be_bytes()[1..];
        Self(bs[0], bs[1], bs[2])
    }

    pub const fn brighten(self, by: u8) -> Self {
        sat! { (+) Self((self.0, by), (self.1, by), (self.1, by)) }
    }

    pub const fn incr(self, dr: u8, dg: u8, db: u8) -> Self {
        sat! { (+) Self((self.0, dr), (self.1, dg), (self.1, db)) }
    }

    pub const fn decr(self, dr: u8, dg: u8, db: u8) -> Self {
        sat! { (-) Self((self.0, dr), (self.1, dg), (self.1, db)) }
    }

    pub fn incr_red(mut self, by: u8) -> Self {
        self.0 = self.0.saturating_add(by);
        self
    }

    pub fn decr_red(mut self, by: u8) -> Self {
        self.0 = self.0.saturating_sub(by);
        self
    }

    pub fn incr_blued(mut self, by: u8) -> Self {
        self.1 = self.1.saturating_add(by);
        self
    }

    pub fn decr_blue(mut self, by: u8) -> Self {
        self.1 = self.1.saturating_sub(by);
        self
    }

    pub fn incr_green(mut self, by: u8) -> Self {
        self.2 = self.2.saturating_add(by);
        self
    }

    pub fn decr_green(mut self, by: u8) -> Self {
        self.2 = self.2.saturating_sub(by);
        self
    }
}

impl std::fmt::Display for Rgb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{};{};{}", self.0, self.1, self.2)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Color {
    Ansi(AnsiColor),
    Rgb(Rgb),
}

impl From<AnsiColor> for Color {
    fn from(color: AnsiColor) -> Self {
        Self::Ansi(color)
    }
}

impl From<Rgb> for Color {
    fn from(color: Rgb) -> Self {
        Self::Rgb(color)
    }
}

impl Color {
    // pub const RAINBOW: [Self; 7] = [];
    pub const fn rgb(r: u8, g: u8, b: u8) -> Self {
        Self::Rgb(Rgb::new(r, g, b))
    }

    pub const fn from_hex_saturated(hex: u32) -> Self {
        Self::Rgb(if let Some(rgb) = Rgb::from_hex_checked(hex) {
            rgb
        } else {
            Rgb::MAX
        })
    }

    pub fn fg_bytes(self) -> ColorBytes {
        match self {
            Color::Ansi(c) => {
                let mut bs = [0; 5];
                bs[4] = c.as_fg();
                let mut bs = bs.into_iter();
                for _ in 0..4 {
                    bs.next();
                }
                ColorBytes(bs)
            }
            Color::Rgb(Rgb(r, g, b)) => ColorBytes([38, 2, r, g, b].into_iter()),
        }
    }

    pub fn bg_bytes(self) -> ColorBytes {
        match self {
            Color::Ansi(c) => {
                let mut bs = [0; 5];
                bs[4] = c.as_bg();
                let mut bs = bs.into_iter();
                for _ in 0..4 {
                    bs.next();
                }
                ColorBytes(bs)
            }
            Color::Rgb(Rgb(r, g, b)) => ColorBytes([48, 2, r, g, b].into_iter()),
        }
    }
}

impl std::fmt::Display for Color {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Color::Ansi(c) => write!(f, "{}", c.as_str()),
            Color::Rgb(rgb) => write!(f, "{}", rgb),
        }
    }
}

pub type Bytes = std::array::IntoIter<u8, 5>;

#[derive(Clone)]
pub struct ColorBytes(Bytes);

impl Iterator for ColorBytes {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl ExactSizeIterator for ColorBytes {
    fn len(&self) -> usize {
        self.0.len()
    }
}

#[derive(Clone, Default)]
pub struct Rainbow {
    state: std::cell::Cell<usize>,
}

impl Rainbow {
    ///! Safe since these hex codes are hardcoded
    pub const ROYGBIV: [Color; 7] = unsafe {
        let hex = Rgb::from_hex_unchecked;
        // Red
        [
            Color::Rgb(hex(0xE40303)),
            Color::Rgb(hex(0xFF8C00)),
            Color::Rgb(hex(0xFFED00)),
            Color::Rgb(hex(0x008026)),
            Color::Rgb(hex(0x004Dff)),
            Color::Rgb(hex(0x750787)),
            Color::Rgb(hex(0x812BA6)),
        ]
    };
    pub fn new(state: usize) -> Self {
        Self {
            state: std::cell::Cell::new(state),
        }
    }

    pub fn tick(&self) -> &Self {
        let n = self.state.get().wrapping_add(1);
        self.state.set(n);
        self
    }

    pub fn untick(&self) -> &Self {
        let n = self.state.get().wrapping_sub(1);
        self.state.set(n);
        self
    }

    pub fn color(&self) -> Color {
        Self::ROYGBIV[self.state.get() % 7]
    }
}

impl From<usize> for Rainbow {
    fn from(value: usize) -> Self {
        Self {
            state: std::cell::Cell::new(value),
        }
    }
}
