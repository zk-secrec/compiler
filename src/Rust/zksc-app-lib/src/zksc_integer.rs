/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

 use std::fmt;
use std::fmt::Display;

use crate::zksc_types::NatType;
use crate::value::*;
use num_bigint::{BigInt,Sign::Plus};
use num_integer::Integer;
use num_traits::One;
use num_traits::Zero;
use num_traits::ToPrimitive;

#[macro_export]
macro_rules! small_modulus_struct {
    ($typename:tt,$value_type:tt,$modulus:literal) => {
        pub struct $typename {
            value : $value_type
        }

        impl $typename {
            const USIZE_BYTES : usize = std::mem::size_of::<usize>();
            const TYPE_BYTES : usize = std::mem::size_of::<$value_type>();
            const MODULUS : $value_type = $modulus;
        }
    }
}

pub fn inverse(a : i128, modulus : i128) -> i128 {
    let mut t : i128 = 0;
    let mut newt : i128 = 1;
    let mut r : i128 = modulus;
    let mut newr : i128 = a;

    while newr != 0 {
        let quotient = r / newr;
        (t, newt) = (newt, t - quotient * newt);
        (r, newr) = (newr, r - quotient * newr);
    }

    if r > 1 {
        panic!("a is not invertible")
    };

    return if t < 0 {t + modulus} else {t}
}

#[macro_export]
macro_rules! small_modulus_nattype {
    ($typename:tt,$value_type:tt,$modulus:literal) => {
        NatType {
            tag : $typename :: TAG - BigInt :: TAG,
            modulus : Some({
                const modulus_value : u128 = $modulus;
                BigInt::from(modulus_value)
            }),
            modulus_value : || {
                const modulus_value : u128 = $modulus;
                Value::new::<BigInt>(BigInt::from(modulus_value))
            },
            is_zero : |x| {x.unwrap::<$typename>().value % $modulus == 0},
            is_one : |x| {x.unwrap::<$typename>().value % $modulus ==1},
            eq : |x,y| {x.unwrap::<$typename>().value == y.unwrap::<$typename>().value},
            lt : |x,y| {x.unwrap::<$typename>().value < y.unwrap::<$typename>().value},
            add : |x,y| {
                let (x_val,y_val) = (x.unwrap::<$typename>().value,y.unwrap::<$typename>().value);
                let res_val : u128 = ((u128::from(x_val) + u128::from(y_val)) % $modulus);
                Value::new::<$typename>($typename { value : res_val as $value_type})
            },
            mul : |x,y| {
                let (x_val,y_val) = (x.unwrap::<$typename>().value,y.unwrap::<$typename>().value);
                let res_val : u128 = ((u128::from(x_val) * u128::from(y_val)) % $modulus);
                Value::new::<$typename>($typename { value : res_val as $value_type})
            },
            sub : |x,y| {
                let (x_val,y_val) = (x.unwrap::<$typename>().value,y.unwrap::<$typename>().value);
                let res_val : u128 = ((u128::from(x_val) + $modulus - u128::from(y_val)) % $modulus);
                Value::new::<$typename>($typename { value : res_val as $value_type})
            },
            div : |x,y| {
                let (x_val,y_val) = (x.unwrap::<$typename>().value,y.unwrap::<$typename>().value);
                let res_val : u128 = u128::from(x_val) / u128::from(y_val);
                Value::new::<$typename>($typename { value : res_val as $value_type})
            },
            hmod : |x,y| {
                let (x_val,y_val) = (x.unwrap::<$typename>().value,y.unwrap::<$typename>().value);
                let res_val : u128 = ((u128::from(x_val) % u128::from(y_val)));
                Value::new::<$typename>($typename { value : res_val as $value_type})
            },
            mod_div : |x,y| {
                let (x_val,y_val) = (x.unwrap::<$typename>().value,y.unwrap::<$typename>().value);
                let r = crate::zksc_integer::inverse(i128::from(y_val),$modulus).unsigned_abs();
                let res_val : u128 = ((u128::from(x_val) * u128::from(r)) % $modulus);
                Value::new::<$typename>($typename { value : res_val as $value_type})},
            to_bigint : |x| {
                let x_val = x.unwrap::<$typename>().value;
                BigInt::from(x_val)
            },
            from_bigint : |x| {
                const modulus_u128 : u128 = $modulus;
                let x_reduced : $value_type = match TryFrom::try_from(x) {
                    Ok(v) => {
                        let help : $value_type = v;
                        help % $modulus
                    },
                    Err(_) => TryFrom::try_from(&x.mod_floor(&BigInt::from(modulus_u128))).unwrap(),
                };
                Value::new::<$typename>($typename { value : x_reduced})
            },
            fmt: |x, f| {
                match x.view() {
                    ValueView::Bool(b) => if *b { write!(f, "1") } else { write!(f, "0") },
                    ValueView::ZkscDefined() => { write!(f, "{}", x.unwrap::<$typename>().value) },
                    _ => panic!("small_modulus_nattype.fmt didn't get bool or own type",)
                }
            }
        }
    }
}


#[macro_export]
macro_rules! fixed_modulus_struct {
    ($typename:tt,$modulus_be_hexstring:expr) => {
        pub struct $typename {
            value : BigInt
        }

        impl $typename {
            fn modulus() -> &'static BigInt {
            static MODULUS : OnceCell<BigInt> = OnceCell::new();
            MODULUS.get_or_init(|| {
            let bi_bytes = $modulus_be_hexstring.as_bytes();
            BigInt::parse_bytes(bi_bytes,16).unwrap()
            })
            }
        }
    }
}

#[macro_export]
macro_rules! fixed_modulus_nattype {
    ($typename:tt) => {
        NatType {
            tag : $typename :: TAG - BigInt :: TAG,
            modulus : Some($typename::modulus().clone()),
            modulus_value : || { Value::new::<BigInt>($typename::modulus().clone())},
            is_zero : |x| {x.unwrap::<$typename>().value.is_zero()},
            is_one : |x| {x.unwrap::<$typename>().value.is_one()},
            eq : |x,y| {x.unwrap::<$typename>().value == y.unwrap::<$typename>().value},
            lt : |x,y| {x.unwrap::<$typename>().value < y.unwrap::<$typename>().value},
            add : |x,y| {
                let value = (&x.unwrap::<$typename>().value + &y.unwrap::<$typename>().value) % $typename::modulus();
                Value::new::<$typename>($typename {value})
            },
            mul : |x,y| {
                let value = (&x.unwrap::<$typename>().value * &y.unwrap::<$typename>().value) % $typename::modulus();
                Value::new::<$typename>($typename {value})
            },
            sub : |x,y| {
                let value = (&x.unwrap::<$typename>().value - &y.unwrap::<$typename>().value + $typename::modulus()) % $typename::modulus();
                Value::new::<$typename>($typename {value})
            },
            div : |x,y| {
                let value = (&x.unwrap::<$typename>().value / &y.unwrap::<$typename>().value) % $typename::modulus();
                Value::new::<$typename>($typename {value})
            },
            hmod : |x,y| {
                let value = x.unwrap::<$typename>().value.mod_floor(&y.unwrap::<$typename>().value);
                Value::new::<$typename>($typename {value})
            },
            mod_div : |x,y| {
                let xval = &x.unwrap::<$typename>().value;
                let yval = &y.unwrap::<$typename>().value;
                let m = $typename::modulus();
                let e = num_integer::Integer::extended_gcd(yval,m);
                let mod_inv = e.x.mod_floor(m);
                assert_eq!(e.gcd, BigInt::one(), "Value {} not invertible modulo {}", yval, m);
                let value = (xval * mod_inv) % m;
                Value::new::<$typename>($typename {value})
            },
            to_bigint : |x| {
                x.unwrap::<$typename>().value.clone()
            },
            from_bigint : |x| {
                let v1 = x.clone() % $typename::modulus();
                let v2 = if v1.sign()==Sign::Minus {v1 + $typename::modulus()} else {v1};
                Value::new::<$typename>($typename {value : (v2)})
            },
            fmt: |x, f| {
                match x.view() {
                    ValueView::Bool(b) => if *b { write!(f, "1") } else { write!(f, "0") } ,
                    ValueView::ZkscDefined() => { write!(f, "{}", x.unwrap::<$typename>().value) },
                    _ => panic!("fixed_modulus_nattype.to_string didn't get bool or own type",)
                }
            },
        }
    }
}

// u8
pub fn nattype_256(tag : u64) -> NatType {
    NatType {
        tag : tag,
        modulus : Some(BigInt::from(256u64)),
        modulus_value : || {panic!("modulus_value called on u8 modulus")},
        is_zero : |x| {x.unwrap::<u8>().is_zero()},
        is_one : |x| {x.unwrap::<u8>().is_one()},
        eq : |x,y| {
            x.unwrap::<u8>() == y.unwrap::<u8>()
        },
        lt : |x,y| {
            x.unwrap::<u8>() < y.unwrap::<u8>()
        },
        add : |x, y| {
            Value::new::<u8>(x.unwrap::<u8>().wrapping_add(*y.unwrap::<u8>()))
        },
        mul : |x, y| {
            Value::new::<u8>(x.unwrap::<u8>().wrapping_mul(*y.unwrap::<u8>()))
        },
        sub : |x, y| {
            Value::new::<u8>(x.unwrap::<u8>().wrapping_sub(*y.unwrap::<u8>()))
        },
        div : |x, y| {
            let (x_val,y_val) = (x.unwrap::<u8>(),y.unwrap::<u8>());
            Value::new::<u8>(x_val.div_floor(y_val))
        },
        hmod : |x, y| {
            Value::new::<u8>(x.unwrap::<u8>().mod_floor(y.unwrap::<u8>()))
        },
        mod_div : |_x, _y| {
            panic!("u8 modulus not supported for mod_div")
        },
        to_bigint : |x| {
            BigInt::from(*x.unwrap::<u8>())
        },
        from_bigint : |x| {
            Value::new::<u8>(x.mod_floor(&BigInt::from(256u64)).to_u8().unwrap())
        },
        fmt: |x, f| {
            match x.view() {
                ValueView::Bool(b) => if *b { write!(f, "1") } else { write!(f, "0") } ,
                ValueView::ZkscDefined() => { write!(f, "{}", x.unwrap::<u8>()) },
                _ => panic!("u8.to_string didn't get bool or own type",)
            }
        }
    }
}

// u16
pub fn nattype_65536(tag : u64) -> NatType {
    NatType {
        tag : tag,
        modulus : Some(BigInt::from(65536u64)),
        modulus_value : || {panic!("modulus_value called on u16 modulus")},
        is_zero : |x| {x.unwrap::<u16>().is_zero()},
        is_one : |x| {x.unwrap::<u16>().is_one()},
        eq : |x,y| {
            x.unwrap::<u16>() == y.unwrap::<u16>()
        },
        lt : |x,y| {
            x.unwrap::<u16>() < y.unwrap::<u16>()
        },
        add : |x, y| {
            Value::new::<u16>(x.unwrap::<u16>().wrapping_add(*y.unwrap::<u16>()))
        },
        mul : |x, y| {
            Value::new::<u16>(x.unwrap::<u16>().wrapping_mul(*y.unwrap::<u16>()))
        },
        sub : |x, y| {
            Value::new::<u16>(x.unwrap::<u16>().wrapping_sub(*y.unwrap::<u16>()))
        },
        div : |x, y| {
            let (x_val,y_val) = (x.unwrap::<u16>(),y.unwrap::<u16>());
            Value::new::<u16>(x_val.div_floor(y_val))
        },
        hmod : |x, y| {
            Value::new::<u16>(x.unwrap::<u16>().mod_floor(y.unwrap::<u16>()))
        },
        mod_div : |_x, _y| {
            panic!("u16 modulus not supported for mod_div")
        },
        to_bigint : |x| {
            BigInt::from(*x.unwrap::<u16>())
        },
        from_bigint : |x| {
            Value::new::<u16>(x.mod_floor(&BigInt::from(65536u64)).to_u16().unwrap())
        },
        fmt: |x, f| {
            match x.view() {
                ValueView::Bool(b) => if *b { write!(f, "1") } else { write!(f, "0") } ,
                ValueView::ZkscDefined() => { write!(f, "{}", x.unwrap::<u16>()) },
                _ => panic!("u16.to_string didn't get bool or own type",)
            }
        },
    }
}

// u32
pub fn nattype_4294967296(tag : u64) -> NatType {
    NatType {
        tag : tag,
        modulus : Some(BigInt::from(4294967296u64)),
        modulus_value : || {panic!("modulus_value called on u32 modulus")},
        is_zero : |x| {x.unwrap::<u32>().is_zero()},
        is_one : |x| {x.unwrap::<u32>().is_one()},
        eq : |x,y| {
            x.unwrap::<u32>() == y.unwrap::<u32>()
        },
        lt : |x,y| {
            x.unwrap::<u32>() < y.unwrap::<u32>()
        },
        add : |x, y| {
            Value::new::<u32>(x.unwrap::<u32>().wrapping_add(*y.unwrap::<u32>()))
        },
        mul : |x, y| {
            Value::new::<u32>(x.unwrap::<u32>().wrapping_mul(*y.unwrap::<u32>()))
        },
        sub : |x, y| {
            Value::new::<u32>(x.unwrap::<u32>().wrapping_sub(*y.unwrap::<u32>()))
        },
        div : |x, y| {
            let (x_val,y_val) = (x.unwrap::<u32>(),y.unwrap::<u32>());
            Value::new::<u32>(x_val.div_floor(y_val))
        },
        hmod : |x, y| {
            Value::new::<u32>(x.unwrap::<u32>().mod_floor(y.unwrap::<u32>()))
        },
        mod_div : |_x, _y| {
            panic!("u32 modulus not supported for mod_div")
        },
        to_bigint : |x| {
            BigInt::from(*x.unwrap::<u32>())
        },
        from_bigint : |x| {
            Value::new::<u32>(x.mod_floor(&BigInt::from(4294967296u64)).to_u32().unwrap())
        },
        fmt: |x, f| {
            match x.view() {
                ValueView::Bool(b) => if *b { write!(f, "1") } else { write!(f, "0") } ,
                ValueView::ZkscDefined() => { write!(f, "{}", x.unwrap::<u32>()) },
                _ => panic!("u32.to_string didn't get bool or own type",)
            }
        }
    }
}

// u64
pub fn nattype_18446744073709551616(tag : u64) -> NatType {
    NatType {
        tag : tag,
        modulus : Some(BigInt::from(18446744073709551616u128)),
        modulus_value : || {panic!("modulus_value called on u64 modulus")},
        is_zero : |x| {x.unwrap::<u64>().is_zero()},
        is_one : |x| {x.unwrap::<u64>().is_one()},
        eq : |x,y| {
            x.unwrap::<u64>() == y.unwrap::<u64>()
        },
        lt : |x,y| {
            x.unwrap::<u64>() < y.unwrap::<u64>()
        },
        add : |x, y| {
            Value::new::<u64>(x.unwrap::<u64>().wrapping_add(*y.unwrap::<u64>()))
        },
        mul : |x, y| {
            Value::new::<u64>(x.unwrap::<u64>().wrapping_mul(*y.unwrap::<u64>()))
        },
        sub : |x, y| {
            Value::new::<u64>(x.unwrap::<u64>().wrapping_sub(*y.unwrap::<u64>()))
        },
        div : |x, y| {
            let (x_val,y_val) = (x.unwrap::<u64>(),y.unwrap::<u64>());
            Value::new::<u64>(x_val.div_floor(y_val))
        },
        hmod : |x, y| {
            Value::new::<u64>(x.unwrap::<u64>().mod_floor(y.unwrap::<u64>()))
        },
        mod_div : |_x, _y| {
            panic!("u64 modulus not supported for mod_div")
        },
        to_bigint : |x| {
            BigInt::from(*x.unwrap::<u64>())
        },
        from_bigint : |x| {
            Value::new::<u64>(x.mod_floor(&BigInt::from(18446744073709551616u128)).to_u64().unwrap())
        },
        fmt: |x, f| {
            match x.view() {
                ValueView::Bool(b) => if *b { write!(f, "1") } else { write!(f, "0") } ,
                ValueView::ZkscDefined() => { write!(f, "{}", x.unwrap::<u64>()) },
                _ => panic!("u64.to_string didn't get bool or own type",)
            }
        }
    }
}

// u128
pub fn nattype_340282366920938463463374607431768211456(tag : u64) -> NatType {
    NatType {
        tag : tag,
        modulus : Some(BigInt::from(340282366920938463463374607431768211455u128) + 1),
        modulus_value : || {panic!("modulus_value called on u128 modulus")},
        is_zero : |x| {x.unwrap::<u128>().is_zero()},
        is_one : |x| {x.unwrap::<u128>().is_one()},
        eq : |x,y| {
            x.unwrap::<u128>() == y.unwrap::<u128>()
        },
        lt : |x,y| {
            x.unwrap::<u128>() < y.unwrap::<u128>()
        },
        add : |x, y| {
            Value::new::<u128>(x.unwrap::<u128>().wrapping_add(*y.unwrap::<u128>()))
        },
        mul : |x, y| {
            Value::new::<u128>(x.unwrap::<u128>().wrapping_mul(*y.unwrap::<u128>()))
        },
        sub : |x, y| {
            Value::new::<u128>(x.unwrap::<u128>().wrapping_sub(*y.unwrap::<u128>()))
        },
        div : |x, y| {
            let (x_val,y_val) = (x.unwrap::<u128>(),y.unwrap::<u128>());
            Value::new::<u128>(x_val.div_floor(y_val))
        },
        hmod : |x, y| {
            Value::new::<u128>(x.unwrap::<u128>().mod_floor(y.unwrap::<u128>()))
        },
        mod_div : |_x, _y| {
            panic!("u128 modulus not supported for mod_div")
        },
        to_bigint : |x| {
            BigInt::from(*x.unwrap::<u128>())
        },
        from_bigint : |x| {
            Value::new::<u128>(x.mod_floor(&(BigInt::from(340282366920938463463374607431768211455u128) + 1)).to_u128().unwrap())
        },
        fmt: |x, f| {
            match x.view() {
                ValueView::Bool(b) => if *b { write!(f, "1") } else { write!(f, "0") } ,
                ValueView::ZkscDefined() => { write!(f, "{}", x.unwrap::<u128>()) },
                _ => panic!("u128.to_string didn't get bool or own type",)
            }
        }
    }
}

pub fn infinite_nattype() -> NatType {
    NatType {
        tag : 0,
        modulus : None,
        modulus_value : || {panic!("modulus_value called on infinite modulus")},
        is_zero : |x| {x.unwrap::<BigInt>().is_zero()},
        is_one : |x| {x.unwrap::<BigInt>().is_one()},
        eq : |x,y| {
            x.unwrap::<BigInt>() == y.unwrap::<BigInt>()
        },
        lt : |x,y| {
            x.unwrap::<BigInt>() < y.unwrap::<BigInt>()
        },
        add : |x, y| {
            Value::new::<BigInt>(x.unwrap::<BigInt>() + y.unwrap::<BigInt>())
        },
        mul : |x, y| {
            Value::new::<BigInt>(x.unwrap::<BigInt>() * y.unwrap::<BigInt>())
        },
        sub : |x, y| {
            Value::new::<BigInt>(x.unwrap::<BigInt>() - y.unwrap::<BigInt>())
        },
        div : |x, y| {
            let (x_val,y_val) = (x.unwrap::<BigInt>(),y.unwrap::<BigInt>());
            Value::new::<BigInt>(x_val.div_floor(y_val))
        },
        hmod : |x, y| {
            Value::new::<BigInt>(x.unwrap::<BigInt>().mod_floor(y.unwrap::<BigInt>()))
        },
        mod_div : |_x, _y| {
            panic!("infinite modulus not supported for mod_div")
        },
        to_bigint : |x| {x.unwrap::<BigInt>().clone()},
        from_bigint : |x| {Value::new::<BigInt>(x.clone())},
        fmt: |x, f| {
            match x.view() {
                ValueView::Bool(b) => if *b { write!(f, "1") } else { write!(f, "0") } ,
                ValueView::ZkscDefined() => { write!(f, "{}", x.unwrap::<BigInt>()) },
                _ => panic!("BigInt.to_string didn't get bool or own type",)
            }
        }
    }
}

pub struct ZkscIntDisplay<'a> {
    modulus: &'a NatType,
    value: &'a Value,
}

impl<'a> ZkscIntDisplay<'a> {
    pub fn new(modulus: &'a NatType, value: &'a Value) -> ZkscIntDisplay<'a> {
        ZkscIntDisplay {
            modulus,
            value,
        }
    }
}

impl<'a> Display for ZkscIntDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.modulus.fmt)(self.value, f)
    }
}
