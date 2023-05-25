use std::cmp::Ordering::{self, Equal, Greater, Less};
use std::f64::consts::{E, LOG10_2};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use itertools::Itertools;

/** Quickly made up, missing many features */
#[derive(Clone)]
pub struct OmegaNum {
    pub top: f64,
    pub array: Vec<u64>,
    pub neg: bool,
}

const MAX_SAFE_INTEGER_U64: u64 = 9007199254740991;
const MAX_SAFE_INTEGER_F64: f64 = 9007199254740991.0;
const MAX_E: f64 = 15.9545897701910032981; // OmegaNum::TOP_HIGH_THRESHOLD.log10()
impl OmegaNum {
    pub fn new(top: f64, array: Vec<u64>, neg: bool) -> Self {
        let mut value = OmegaNum { top, array, neg };
        value.normalize();
        value
    }
    const fn new_no_normalize(top: f64, array: Vec<u64>, neg: bool) -> Self {
        OmegaNum { top, array, neg }
    }
    fn safe_array_set(&mut self, i: usize, value: u64) -> () {
        while self.array.len() < i + 1 {
            self.array.push(0)
        }
        self.array[i] = value
    }
    fn safe_array_get(&self, i: usize) -> u64 {
        *self.array.get(i).unwrap_or(&0)
    }
    fn normalize(&mut self) {
        if self.top < 0.0 && self.array.len() == 0 {
            self.top = -self.top;
            self.neg = !self.neg;
        }
        loop {
            let mut modified = false;
            while self.array.len() > 0 && self.array[self.array.len() - 1] == 0 {
                self.array.pop();
                modified = true;
            }
            if self.top > MAX_SAFE_INTEGER_F64 {
                self.top = self.top.log10();
                self.safe_array_set(0, self.safe_array_get(0) + 1);
                modified = true;
            }
            while self.top < MAX_E && self.safe_array_get(0) > 0 {
                self.top = 10.0_f64.powf(self.top);
                self.array[0] -= 1;
                modified = true;
            }
            if self.array.len() > 1 && self.safe_array_get(0) == 0 {
                let i = self.array.iter().find_position(|&&a| a > 0).unwrap().0;
                self.top = 1.0;
                self.array[i - 1] = self.top.trunc() as u64;
                self.array[i] -= 1;
                modified = true;
            }
            for i in 1..self.array.len() {
                if self.array[i] > MAX_SAFE_INTEGER_U64 {
                    self.top = self.array[i] as f64;
                    for i in self.array[1..i].iter_mut() {
                        *i = 0
                    }
                    self.safe_array_set(i + 1, self.safe_array_get(i + 1) + 1);
                    modified = true;
                }
            }
            if !modified {
                break;
            }
        }
        if self.top < 0.0 && self.array.len() > 0 {
            panic!()
        }
    }
}
pub mod consts {
    use super::*;

    pub const ZERO: OmegaNum = OmegaNum::new_no_normalize(0.0, vec![], false);
    pub const ONE: OmegaNum = OmegaNum::new_no_normalize(1.0, vec![], false);
    pub const MAX_SAFE_INTEGER: OmegaNum =
        OmegaNum::new_no_normalize(MAX_SAFE_INTEGER_F64, vec![], false);
    pub fn e_max_safe_integer() -> OmegaNum {
        OmegaNum::new_no_normalize(MAX_SAFE_INTEGER_F64, vec![1], false)
    }
    pub fn ee_max_safe_integer() -> OmegaNum {
        OmegaNum::new_no_normalize(MAX_SAFE_INTEGER_F64, vec![2], false)
    }
    pub(super) fn arrow_max_safe_integer(arrows: usize) -> OmegaNum {
        let mut array = vec![0; arrows];
        array[0] = 1;
        array[arrows - 1] = 1;
        OmegaNum::new_no_normalize(MAX_E, array, false)
    }
}

impl From<f64> for OmegaNum {
    fn from(value: f64) -> Self {
        let abs = value.abs();
        if abs > MAX_SAFE_INTEGER_F64 {
            OmegaNum::new_no_normalize(abs.log10(), vec![1], value.is_sign_negative())
        } else {
            OmegaNum::new_no_normalize(abs, vec![], value.is_sign_negative())
        }
    }
}

impl From<OmegaNum> for f64 {
    fn from(value: OmegaNum) -> Self {
        (if value.array.len() == 0 {
            value.top
        } else if value.array.len() == 1 && value.array[0] == 1 {
            10.0_f64.powf(value.top)
        } else {
            f64::INFINITY
        }) * value.signum_f64()
    }
}

impl ToString for OmegaNum {
    fn to_string(&self) -> String {
        (if self.neg { "-" } else { "" }).to_owned()
            + &self
                .array
                .iter()
                .enumerate()
                .skip(1)
                .rev()
                .filter(|(_, &a)| a > 0)
                .map({
                    |(i, &a)| {
                        let arrows = i + 1;
                        let q = &if arrows >= 5 {
                            format!("{{{}}}", arrows)
                        } else {
                            "^".repeat(arrows)
                        };
                        match a {
                            1 => "10".to_owned() + q,
                            _ => format!("(10{})^{} ", q, a),
                        }
                    }
                })
                .join("")
            + &match self.safe_array_get(0) {
                0 => self.top.to_string(),
                1 => {
                    let i = self.top.trunc();
                    let f = self.top - i;
                    format!("{}e{}", 10.0_f64.powf(f), i as u64)
                }
                2 => {
                    let i = self.top.trunc();
                    let f = self.top - i;
                    format!("e{}e{}", 10.0_f64.powf(f), i as u64)
                }
                h @ (3 | 4 | 5 | 6 | 7) => "e".repeat(h as usize) + &self.top.to_string(),
                h => format!("(10^)^{} {}", h, self.top),
            }
    }
}
impl OmegaNum {
    fn is_zero(&self) -> bool {
        self.top == 0.0 && self.array.len() == 0
    }
    fn is_sign_negative(&self) -> bool {
        self.neg && !self.is_zero()
    }
    fn is_sign_positive(&self) -> bool {
        !self.neg && !self.is_zero()
    }
}

impl PartialEq for OmegaNum {
    fn eq(&self, other: &Self) -> bool {
        self.is_zero() && other.is_zero()
            || self.top == other.top && self.array == other.array && self.neg == other.neg
    }
}

impl PartialOrd for OmegaNum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.is_zero() && other.is_zero() {
            Some(Equal)
        } else if self.neg != other.neg {
            Some(if self.neg { Less } else { Greater })
        } else {
            match self.array.len().cmp(&other.array.len()) {
                Equal => self
                    .array
                    .iter()
                    .zip(other.array.iter())
                    .rev()
                    .find_map(|(&a, &b)| match a.cmp(&b) {
                        Equal => None,
                        o => Some(o),
                    })
                    .or_else(|| self.top.partial_cmp(&other.top)),
                o => Some(o),
            }
        }
    }
}

impl OmegaNum {
    pub fn signum_f64(&self) -> f64 {
        if self.neg {
            -1.0
        } else {
            1.0
        }
    }
    pub fn signum(&self) -> Self {
        OmegaNum::new_no_normalize(1.0, vec![], self.neg)
    }
    pub fn abs(self) -> Self {
        OmegaNum::new_no_normalize(self.top, self.array, false)
    }
    pub fn is_integer(&self) -> bool {
        self.array.len() > 0 || self.top == self.top.floor()
    }
    pub fn floor(self) -> Self {
        if self.is_integer() {
            self
        } else {
            OmegaNum::from(f64::from(self).floor())
        }
    }
    pub fn ceil(self) -> Self {
        if self.is_integer() {
            self
        } else {
            OmegaNum::from(f64::from(self).ceil())
        }
    }
    pub fn round(self) -> Self {
        if self.is_integer() {
            self
        } else {
            OmegaNum::from(f64::from(self).round())
        }
    }
}
impl Neg for OmegaNum {
    type Output = OmegaNum;
    fn neg(self) -> Self::Output {
        OmegaNum::new_no_normalize(self.top, self.array, !self.neg)
    }
}

impl Add for OmegaNum {
    type Output = OmegaNum;
    fn add(self, rhs: Self) -> Self::Output {
        if self.neg {
            return -(-self + -rhs);
        }
        if rhs.neg {
            return self - -rhs;
        }
        if self == consts::ZERO {
            return rhs;
        }
        if rhs == consts::ZERO {
            return self;
        }
        let (p, q) = if self < rhs { (self, rhs) } else { (rhs, self) };
        if q > consts::e_max_safe_integer() || q.clone() / p.clone() > consts::MAX_SAFE_INTEGER {
            q
        } else {
            match q.safe_array_get(0) {
                0 => OmegaNum::from(p.top + q.top),
                1 => {
                    let a = match p.safe_array_get(0) {
                        0 => p.top.log10(),
                        1 => p.top,
                        _ => panic!(),
                    };
                    OmegaNum::new(a + (10.0_f64.powf(q.top - a) + 1.0).log10(), vec![1], false)
                }
                _ => panic!(),
            }
        }
    }
}
impl AddAssign for OmegaNum {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}
impl Sub for OmegaNum {
    type Output = OmegaNum;
    fn sub(self, rhs: Self) -> Self::Output {
        if self.neg {
            return -(-self - -rhs);
        }
        if rhs.neg {
            return self + -rhs;
        }
        if self == rhs {
            return consts::ZERO;
        }
        if rhs == consts::ZERO {
            return self;
        }
        let (p, q, n) = if self < rhs {
            (self, rhs, true)
        } else {
            (rhs, self, false)
        };
        let t = if q > consts::e_max_safe_integer()
            || q.clone() / p.clone() > consts::MAX_SAFE_INTEGER
        {
            q
        } else {
            match q.safe_array_get(0) {
                0 => OmegaNum::from(p.top + q.top),
                1 => {
                    let a = match p.safe_array_get(0) {
                        0 => p.top.log10(),
                        1 => p.top,
                        _ => panic!(),
                    };
                    OmegaNum::new(a + (10.0_f64.powf(q.top - a) + 1.0).log10(), vec![1], false)
                }
                _ => panic!(),
            }
        };
        if n {
            -t
        } else {
            t
        }
    }
}
impl SubAssign for OmegaNum {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}
impl Mul for OmegaNum {
    type Output = OmegaNum;
    fn mul(self, rhs: Self) -> Self::Output {
        if self.neg != rhs.neg {
            return -(self.abs() * rhs.abs());
        }
        if self.neg {
            return self.abs() * rhs.abs();
        }
        if rhs == consts::ZERO {
            return consts::ZERO;
        }
        if rhs == consts::ONE {
            return self;
        }
        let q = if self > rhs {
            self.clone()
        } else {
            rhs.clone()
        };
        if q > consts::ee_max_safe_integer() {
            return q;
        }
        let n = f64::from(self.clone()) * f64::from(rhs.clone());
        if n <= MAX_SAFE_INTEGER_F64 {
            OmegaNum::from(n)
        } else {
            OmegaNum::pow(OmegaNum::from(10.0), self.log10() + rhs.log10())
        }
    }
}
impl MulAssign for OmegaNum {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}
impl Div for OmegaNum {
    type Output = OmegaNum;
    fn div(self, rhs: Self) -> Self::Output {
        if self.neg != rhs.neg {
            return -(self.abs() / rhs.abs());
        }
        if self.neg {
            return self.abs() / rhs.abs();
        }
        if rhs == consts::ZERO {
            todo!()
        }
        if rhs == consts::ONE {
            return self;
        }
        if self == rhs {
            return consts::ONE;
        }
        if self > rhs {
            if self > consts::ee_max_safe_integer() {
                return self;
            }
        } else {
            if rhs > consts::ee_max_safe_integer() {
                return consts::ZERO;
            }
        }
        let n = f64::from(self.clone()) / f64::from(rhs.clone());
        if n <= MAX_SAFE_INTEGER_F64 {
            return OmegaNum::from(n);
        }
        let pw = OmegaNum::pow(OmegaNum::from(10.0), self.log10() - rhs.log10());
        let fp = pw.clone().floor();
        if pw.clone() - fp.clone() < OmegaNum::from(1e-9) {
            fp
        } else {
            pw
        }
    }
}
impl DivAssign for OmegaNum {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.clone() / rhs;
    }
}
impl OmegaNum {
    pub fn recip(self) -> Self {
        if self.clone().abs() > OmegaNum::new_no_normalize(323.0 + LOG10_2, vec![1], false) {
            consts::ZERO
        } else {
            OmegaNum::from(f64::from(self).recip())
        }
    }
    pub fn pow(self, mut rhs: Self) -> Self {
        if rhs == consts::ZERO {
            return consts::ONE;
        }
        if rhs == consts::ONE {
            return self;
        }
        if rhs.neg {
            return self.pow(-rhs).recip();
        }
        if self < consts::ZERO {
            if rhs.is_integer() {
                return match f64::from(rhs.clone()) as i64 % 2 {
                    0 => self.abs().pow(rhs),
                    _ => -self.abs().pow(rhs),
                };
            } else {
                panic!()
            }
        }
        if self == consts::ONE {
            return consts::ONE;
        }
        if self == consts::ZERO {
            return consts::ZERO;
        }
        let q = if self > rhs {
            self.clone()
        } else {
            rhs.clone()
        };
        if q >= consts::arrow_max_safe_integer(2) {
            return q;
        }
        if self == OmegaNum::from(10.0) {
            return if rhs > consts::ZERO {
                rhs.safe_array_set(0, rhs.safe_array_get(0) + 1);
                rhs.normalize();
                rhs
            } else {
                OmegaNum::from(10.0_f64.powf(f64::from(rhs)))
            };
        }
        if rhs < consts::ONE {
            todo!()
        }

        let n = f64::from(self.clone()).powf(f64::from(rhs.clone()));
        if n <= MAX_SAFE_INTEGER_F64 {
            OmegaNum::from(n)
        } else {
            OmegaNum::pow(OmegaNum::from(10.0), self.log10() * rhs)
        }
    }
    pub fn log10(mut self) -> Self {
        if self <= consts::ZERO {
            panic!();
        }
        if self <= consts::MAX_SAFE_INTEGER {
            return OmegaNum::from(f64::from(self).log10());
        }
        if self > consts::arrow_max_safe_integer(2) {
            return self;
        }
        self.array[0] -= 1;
        self.normalize();
        self
    }
    pub fn logbase(self, base: Self) -> Self {
        self.log10() / base.log10()
    }
    pub fn iter_pow(self, mut rhs: Self, payload: Self) -> Self {
        if payload != consts::ONE {
            rhs += payload.slog(self.clone());
        }
        if rhs < OmegaNum::from(-2.0) {
            panic!()
        }
        if self == consts::ZERO {
            return if rhs == consts::ZERO {
                panic!()
            } else if f64::from(rhs.clone()) % 2.0 == 0.0 {
                consts::ZERO
            } else {
                return consts::ONE;
            };
        }
        if self == consts::ONE {
            return if rhs == consts::ONE.neg() {
                panic!()
            } else {
                consts::ONE
            };
        }
        if rhs == consts::ONE.neg() {
            return consts::ZERO;
        }
        if rhs == consts::ZERO {
            return consts::ONE;
        }
        if rhs == consts::ONE {
            return self;
        }
        if rhs == OmegaNum::from(2.0) {
            return self.clone().pow(self);
        }
        if self == OmegaNum::from(2.0) {
            if rhs == OmegaNum::from(3.0) {
                return OmegaNum::from(16.0);
            }
            if rhs == OmegaNum::from(4.0) {
                return OmegaNum::from(65536.0);
            }
        }
        let m = if self > rhs {
            self.clone()
        } else {
            rhs.clone()
        };
        if m > consts::arrow_max_safe_integer(3) {
            return m;
        }
        if self > consts::arrow_max_safe_integer(2) || rhs > consts::MAX_SAFE_INTEGER {
            return if self < OmegaNum::from((1.0_f64 / E).exp()) {
                panic!()
            } else {
                let mut j = self.slog(OmegaNum::from(10.0)) + rhs;
                j.safe_array_set(1, j.safe_array_get(1) + 1);
                j.normalize();
                j
            };
        }
        let y = f64::from(rhs.clone());
        let f = y.floor();
        let mut r = self.clone().pow(OmegaNum::from(y - f));
        let mut f = f as i64;
        let mut l = consts::ZERO;
        let m = consts::e_max_safe_integer();
        let mut i = 0;
        while f != 0 && r < m && i < 100 {
            if f > 0 {
                r = self.clone().pow(r);
                if l == r {
                    f = 0;
                    break;
                }
                l = r.clone();
                f -= 1;
            } else {
                r = r.logbase(self.clone());
                if l == r {
                    f = 0;
                    break;
                }
                l = r.clone();
                f += 1;
            }
            i += 1
        }
        if i == 100 || self < OmegaNum::from((1.0_f64 / E).exp()) {
            f = 0
        }
        r.safe_array_set(0, (r.safe_array_get(0) as i64 + f) as u64);
        r.normalize();
        r
    }
    pub fn tetr(self, rhs: Self) -> Self {
        self.iter_pow(rhs, consts::ONE)
    }
    pub fn slog(mut self, base: Self) -> Self {
        if self < consts::ONE {
            return consts::ONE.neg();
        }
        if self == consts::ONE {
            return consts::ZERO;
        }
        if self == base {
            return consts::ONE;
        }
        if base < OmegaNum::from((1.0_f64 / E).exp()) {
            panic!()
        }

        if self > base {
            if self > consts::arrow_max_safe_integer(3) {
                return self;
            }
            if self > consts::arrow_max_safe_integer(2) {
                self.array[1] -= 1;
                self.normalize();
                return self;
            };
        } else {
            if base > consts::arrow_max_safe_integer(2) {
                return consts::ZERO;
            }
        };
        let mut r = 0_i64;
        let t = (self.safe_array_get(0) - base.safe_array_get(0)) as i64;
        if t > 3 {
            let l = t - 3;
            r += l;
            self.safe_array_set(0, self.safe_array_get(0) - l as u64);
        }
        for _ in 0..100 {
            if self < consts::ZERO {
                self = base.clone().pow(self);
                r -= 1;
            } else if self <= consts::ONE {
                return OmegaNum::from(r as f64 + f64::from(self) - 1.0);
            } else {
                self = self.logbase(base.clone());
                r += 1;
            }
        }
        OmegaNum::from(r as f64)
    }
    pub fn arrow(self, rhs: Self, arrows: usize) -> Self {
        match arrows {
            0 => self * rhs,
            1 => self.pow(rhs),
            2 => self.tetr(rhs),
            _ => {
                if rhs < consts::ZERO {
                    panic!()
                }
                if rhs == consts::ZERO {
                    return consts::ONE;
                }
                if rhs == consts::ONE {
                    return self;
                }
                if rhs == OmegaNum::from(2.0) {
                    return self.clone().arrow(self, arrows - 1);
                }

                let m = if self > rhs {
                    self.clone()
                } else {
                    rhs.clone()
                };
                if m > consts::arrow_max_safe_integer(arrows + 1) {
                    return m;
                }
                if self > consts::arrow_max_safe_integer(arrows) || rhs > consts::MAX_SAFE_INTEGER {
                    let r = if self > consts::arrow_max_safe_integer(arrows) {
                        let mut r = self;
                        r.array[arrows] -= 1;
                        r.normalize();
                        r
                    } else if self > consts::arrow_max_safe_integer(arrows - 1) {
                        OmegaNum::from(self.array[arrows - 1] as f64)
                    } else {
                        consts::ZERO
                    };
                    let mut j = r + rhs;
                    j.safe_array_set(arrows, j.safe_array_get(arrows) + 1);
                    j.normalize();
                    return j;
                }
                let y = f64::from(rhs.clone());
                let f = y.floor();
                let mut r = self.clone().arrow(OmegaNum::from(y - f), arrows - 1);
                let mut f = f as i64;
                let m = consts::arrow_max_safe_integer(arrows - 1);
                let mut i = 0;
                while f != 0 && r < m && i < 100 {
                    if f > 0 {
                        r = self.clone().arrow(r, arrows - 1);
                        f -= 1;
                    }
                }
                if i == 100 {
                    f = 0
                }
                r.safe_array_set(arrows - 1, (r.safe_array_get(arrows - 1) as i64 + f) as u64);
                r.normalize();
                r
            }
        }
    }
    pub fn hyper(x: Self, y: Self, z: usize) -> Self {
        match z {
            0 => {
                if y == consts::ZERO {
                    x
                } else {
                    x + consts::ONE
                }
            }
            1 => x + y,
            _ => x.arrow(y, z - 2),
        }
    }
    pub fn chain(x: Self, y: Self, z: usize) -> Self {
        x.arrow(y, z)
    }
}
