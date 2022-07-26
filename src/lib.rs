/// # rusted25519
/// 
/// Prototyping library for ec ops
/// Not for production use
/// Reference: https://eprint.iacr.org/2008/013.pdf
/// MIT License

use blake2::{Blake2s256, Digest};
use num::bigint::{BigInt, Sign};
use std::{str, ops, format};
use rand_core::RngCore;
use hex;

// enumerations
#[derive(PartialEq)]
enum VectorOp {
    Add,
    Sub,
    Div,
    Mul,
    Had, // Hadamard product
}
// end enumerations

/// # Curve
///
/// rusted25519 curve parameters
struct Curve {
        d: BigInt,
        i: BigInt,
        q: BigInt,
        l: BigInt,
        h: BigInt,
        zero: BigInt,
        one: BigInt,
        two: BigInt,
}

impl Curve {
    /// Create a new curve struct for parameter access.
    pub fn new() -> Curve {
        let zero: BigInt = BigInt::from(0_u8);
        let one: BigInt = BigInt::from(1_u8);
        let two:BigInt =  BigInt::from(2_u8);
        let q: BigInt = two.pow(255) - BigInt::from(19_u8);
        let d1: i32 = -121665;
        let d: BigInt = BigInt::from(d1) * invert(&BigInt::from(121666_u32), &q);
        let four: BigInt = BigInt::from(4_u8);
        let i: BigInt = exponent(&two, &((&q - &one) / four), &q);
        let l: BigInt = two.pow(252) + BigInt::from(27742317777372353535851937790883648493_u128);
        let h: BigInt = BigInt::from(8_u8);
        Curve { d, i, q, l, h, zero, one, two }
    }
}

#[derive(Debug)]
#[derive(PartialEq)]
/// # Scalar
/// 
/// Our scalar values range 0 -> l -1
/// 
/// Overflow is reduced mod l
///
/// ## Panic
/// 
/// Panics on invalid value
/// 
/// ## Example construction
/// 
/// `Scalar::new(BigInt::from(1_u8))`
pub struct Scalar {
    value: BigInt,
    hex_value: String,
}

// Scalar Operator Overloads
impl ops::Add<Scalar> for Scalar {
    type Output = Scalar;
    fn add (self, _rhs: Scalar) -> Scalar {
        let c = Curve::new();
        let v = self.value + _rhs.value;
        scalar_unwrap(Scalar::new(&v.modpow(&c.one, &c.l)))
    }
}

impl ops::Sub<Scalar> for Scalar {
    type Output = Scalar;
    fn sub(self, _rhs: Scalar) -> Scalar {
        let c = Curve::new();
        let v = (self.value - _rhs.value) % Curve::new().l;
        scalar_unwrap(Scalar::new(&v.modpow(&c.one, &c.l)))
    }
}

impl ops::Mul<Scalar> for Scalar {
    type Output = Scalar;
    fn mul(self, _rhs: Scalar) -> Scalar {
       let v = (self.value * _rhs.value) % Curve::new().l;
       scalar_unwrap(Scalar::new(&v))
    }
}

impl ops::Div<Scalar> for Scalar {
    type Output = Scalar;
    fn div(self, _rhs: Scalar) -> Scalar {
        let c = Curve::new();
        let q = self.value * invert(&_rhs.value, &c.l);
        let p = (&_rhs.value * q).modpow(&c.one, &c.l);
        scalar_unwrap(Scalar::new(&p))
    }
}

impl ops::Div<&Scalar> for &Scalar {
    type Output = Scalar;
    fn div(self, _rhs: &Scalar) -> Scalar {
        let c = Curve::new();
        let q = &self.value * invert(&_rhs.value, &c.l);
        let p = (&_rhs.value * q).modpow(&c.one, &c.l);
        scalar_unwrap(Scalar::new(&p))
    }
}
// End Scalar Operator Overloads

impl Scalar {
    /// Create a new valid scalar
    pub fn new (n: &BigInt) -> Result<Scalar, &'static str> {
        let c = Curve::new();
        if n < &c.zero || n > &(c.l - &c.one) {
            return Err("Invalid initialization value")
        }
        let v = n.to_bytes_le().1;
        // Omg rust why? How tf is this better than cloning???
        Ok(Scalar { 
            value: BigInt::from_bytes_le(Sign::Plus, &v), 
            hex_value: to_hex(BigInt::from_bytes_le(Sign::Plus, &v))
        })
    }

    /// Scalar exponentiation
    pub fn pow (&self, e: &Scalar) -> Scalar {
        scalar_unwrap(Scalar::new(&self.value.modpow(&e.value, &Curve::new().l)))
    }

    /// Scalar negation
    pub fn neg (self) -> Scalar {
        let z = Scalar::new(&BigInt::from(0_u8));
        let s = scalar_unwrap(z);
        s - self
    }

    /// Random 32-byte array reduced mod l
    pub fn random_scalar () -> Scalar {
        let c = Curve::new();
        let mut data = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut data);
        let n = BigInt::from_bytes_le(Sign::Plus, &mut data);
        scalar_unwrap(Scalar::new(&(&n % &c.l)))
    }
}

#[derive(Debug)]
#[derive(PartialEq)]
/// # Point
/// 
/// Instantiate a new Point.
/// We don't usually do this.
/// Multiply scalars by `Point::base_generator()`
/// Or use `hash_to_point()`
/// 
/// ## Panic
/// 
/// Panics on `!p.on_curve()`
/// 
/// ## Example construction
/// 
/// `Point::new("hexstring")`
pub struct Point {
    x: BigInt,
    y: BigInt,
    hex_value: String,
}

// Point Operator Overloads
impl ops::Add<Point> for Point {
    type Output = Point;
    fn add (self, _rhs: Point) -> Point {
        let c = Curve::new();
        let vx1 = self.x.to_bytes_le().1;
        let vy1 = self.y.to_bytes_le().1;
        let vx2 = _rhs.x.to_bytes_le().1;
        let vy2 = _rhs.y.to_bytes_le().1;
        let x1 = BigInt::from_bytes_le(Sign::Plus, &vx1);
        let y1 = BigInt::from_bytes_le(Sign::Plus, &vy1);
        let x2 = BigInt::from_bytes_le(Sign::Plus, &vx2);
        let y2 = BigInt::from_bytes_le(Sign::Plus, &vy2);
        let x3 = (&x1 * &y2 + &x2 * &y1) * invert(&(&c.one + &c.d * &x1 * &x2 * &y1 * &y2), &c.q);
        let y3 = (&y1 * &y2 + &x1 * &x2) * invert(&(&c.one - &c.d * &x1 * &x2 * &y1 * &y2), &c.q);
        let y3b = (&y3 % &c.q).to_bytes_le().1;
        let hex = to_hex(BigInt::from_bytes_le(Sign::Plus, &y3b));
        let p = Point { x: x3 % &c.q, y: y3 % &c.q, hex_value: hex };
        p
    }
}

impl ops::Add<&Point> for &Point {
    type Output = Point;
    fn add (self, _rhs: &Point) -> Point {
        let c = Curve::new();
        let vx1 = self.x.to_bytes_le().1;
        let vy1 = self.y.to_bytes_le().1;
        let vx2 = _rhs.x.to_bytes_le().1;
        let vy2 = _rhs.y.to_bytes_le().1;
        let x1 = BigInt::from_bytes_le(Sign::Plus, &vx1);
        let y1 = BigInt::from_bytes_le(Sign::Plus, &vy1);
        let x2 = BigInt::from_bytes_le(Sign::Plus, &vx2);
        let y2 = BigInt::from_bytes_le(Sign::Plus, &vy2);
        let x3 = (&x1 * &y2 + &x2 * &y1) * invert(&(&c.one + &c.d * &x1 * &x2 * &y1 * &y2), &c.q);
        let y3 = (&y1 * &y2 + &x1 * &x2) * invert(&(&c.one - &c.d * &x1 * &x2 * &y1 * &y2), &c.q);
        let y3b = (&y3 % &c.q).to_bytes_le().1;
        let hex = to_hex(BigInt::from_bytes_le(Sign::Plus, &y3b));
        let p = Point { x: x3 % &c.q, y: y3 % &c.q, hex_value: hex };
        p
    }
}

impl ops::Sub<Point> for Point {
    type Output = Point;
    fn sub(self, _rhs: Point) -> Point {
        let c = Curve::new();
        let vx1 = self.x.to_bytes_le().1;
        let vy1 = self.y.to_bytes_le().1;
        let vx2 = _rhs.x.to_bytes_le().1;
        let vy2 = _rhs.y.to_bytes_le().1;
        let x1 = BigInt::from_bytes_le(Sign::Plus, &vx1);
        let y1 = BigInt::from_bytes_le(Sign::Plus, &vy1);
        let x2 = BigInt::from_bytes_le(Sign::Minus, &vx2);
        let y2 = BigInt::from_bytes_le(Sign::Plus, &vy2);
        let x3 = (&x1 * &y2 + &x2 * &y1) * invert(&(&c.one + &c.d * &x1 * &x2 * &y1 * &y2), &c.q);
        let y3 = (&y1 * &y2 + &x1 * &x2) * invert(&(&c.one - &c.d * &x1 * &x2 * &y1 * &y2), &c.q);
        let y3b = (&y3 % &c.q).to_bytes_le().1;
        let hex = to_hex(BigInt::from_bytes_le(Sign::Plus, &y3b));
        let p = Point { x: x3 % &c.q, y: y3 % &c.q, hex_value: hex };
        p
    }
}

impl ops::Sub<&Point> for &Point {
    type Output = Point;
    fn sub(self, _rhs: &Point) -> Point {
        let c = Curve::new();
        let vx1 = self.x.to_bytes_le().1;
        let vy1 = self.y.to_bytes_le().1;
        let vx2 = _rhs.x.to_bytes_le().1;
        let vy2 = _rhs.y.to_bytes_le().1;
        let x1 = BigInt::from_bytes_le(Sign::Plus, &vx1);
        let y1 = BigInt::from_bytes_le(Sign::Plus, &vy1);
        let x2 = BigInt::from_bytes_le(Sign::Minus, &vx2);
        let y2 = BigInt::from_bytes_le(Sign::Plus, &vy2);
        let x3 = (&x1 * &y2 + &x2 * &y1) * invert(&(&c.one + &c.d * &x1 * &x2 * &y1 * &y2), &c.q);
        let y3 = (&y1 * &y2 + &x1 * &x2) * invert(&(&c.one - &c.d * &x1 * &x2 * &y1 * &y2), &c.q);
        let y3b = (&y3 % &c.q).to_bytes_le().1;
        let hex = to_hex(BigInt::from_bytes_le(Sign::Plus, &y3b));
        let p = Point { x: x3 % &c.q, y: y3 % &c.q, hex_value: hex };
        p
    }
}

impl ops::Mul<Scalar> for Point {
    type Output = Point;
    fn mul(self, _rhs: Scalar) -> Point {
        let rb = _rhs.value.to_bytes_le().1;
        if BigInt::from_bytes_le(Sign::Plus, &rb) == BigInt::from(0_u8) {
            return Point::zero_point();
        }
        if BigInt::from_bytes_le(Sign::Plus, &rb) == BigInt::from(1_u8) {
            return self;
        }
        let sb = self.y.to_bytes_le().1;
        let mut count: BigInt = BigInt::from(0_u8);
        let end: BigInt = BigInt::from_bytes_le(Sign::Plus, &rb) - BigInt::from(1_u8);
        let mut q: Point = point_unwrap(Point::new(&to_hex(BigInt::from_bytes_le(Sign::Plus, &sb))));
        loop {
            q = q + point_unwrap(Point::new(&to_hex(BigInt::from_bytes_le(Sign::Plus, &sb))));
            count += BigInt::from(1_u8);
            if count == end { break; }
        }
        q
    }
}
// End Point Operator Overloads

impl Point {
    /// Create a new valid point from a hex string
    pub fn new (h: &str) -> Result<Point, &'static str> {
        let c = Curve::new();
        let x1 = hex::decode(h);
        let hu1 = &hex_unwrap(&x1);
        let hu2 = &hex_unwrap(&x1);
        let hu3 = &hex_unwrap(&x1);
        let y = BigInt::from_bytes_le(Sign::Plus, hu1);
        let y2 = BigInt::from_bytes_le(Sign::Plus, hu2);
        let mut x = xfromy(&y);
        if &x & BigInt::from(1_u8) != BigInt::from(bit(&hu3, 255)) {
            x = c.q - &x
        }
        let p = Point { x, y, hex_value: to_hex(y2) };
        {
            if !p.on_curve() {
                return Err("Point not on curve!");
            }
        }
        Ok(p)
    }

    /// Membership
    fn on_curve(&self) -> bool {
        let c = Curve::new();
        let vx = self.x.to_bytes_le().1;
        let vy = self.y.to_bytes_le().1;
        // fml
        let x = BigInt::from_bytes_le(Sign::Plus, &vx);
        let y = BigInt::from_bytes_le(Sign::Plus, &vy);
        (-&x * &x + &y * &y - BigInt::from(1_u8) - c.d * &x * &x * &y * &y) % c.q == c.zero
    }

    /// Create a random point
    pub fn random_point () -> Point {
        let mut data = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut data);
        let n = BigInt::from_bytes_le(Sign::Plus, &mut data);
        match Point::new(&to_hex(n)) {
            Ok(p) => p,
            _=> Point::random_point()
        }
    }

    /// Return { 0, 1 }
    pub fn zero_point () -> Point {
        let c = Curve::new();
        Point {
            x: BigInt::from(0_u8),
            y: c.one,
            hex_value: to_hex(BigInt::from(1_u8))
        }
    }

    /// Return { Gx, Gy }
    pub fn base_generator () -> Point {
        let c = Curve::new();
        let gy: BigInt = BigInt::from(4_u8) * invert(&BigInt::from(5_u8), &c.q);
        let gy2: BigInt = BigInt::from(4_u8) * invert(&BigInt::from(5_u8), &c.q);
        let gx: BigInt = xfromy(&gy);
        Point { x: gx, y: gy, hex_value: to_hex(gy2) }
    }

    /// Point negation
    pub fn neg (self) -> Point {
        let z = Point::base_generator();
        z - self
    }
}

#[derive(Debug)]
struct ScalarVector {
    value: Vec<Scalar>,   
}

// ScalarVector Operator Overloads
impl ops::Add<ScalarVector> for ScalarVector {
    type Output = ScalarVector;
    fn add(self, _rhs: ScalarVector) -> ScalarVector {
        sv_unwrap(scalar_vector_decomposition(&self, Some(_rhs), None, VectorOp::Add))
    }
}

impl ops::Sub<ScalarVector> for ScalarVector {
    type Output = ScalarVector;
    fn sub(self, _rhs: ScalarVector) -> ScalarVector {
        sv_unwrap(scalar_vector_decomposition(&self, Some(_rhs), None, VectorOp::Sub))
    }
}

/// Hadamard product
impl ops::Mul<ScalarVector> for ScalarVector {
    type Output = ScalarVector;
    fn mul(self, _rhs: ScalarVector) -> ScalarVector {
       sv_unwrap(scalar_vector_decomposition(&self, Some(_rhs), None, VectorOp::Mul))
    }
}

impl ops::Mul<Scalar> for ScalarVector {
    type Output = ScalarVector;
    fn mul(self, _rhs: Scalar) -> ScalarVector {
       sv_unwrap(scalar_vector_decomposition(&self, None, Some(_rhs), VectorOp::Had))
    }
}

impl ops::Div<ScalarVector> for ScalarVector {
    type Output = ScalarVector;
    fn div(self, _rhs: ScalarVector) -> ScalarVector {
        sv_unwrap(scalar_vector_decomposition(&self, Some(_rhs), None, VectorOp::Div))
    }
}
// End ScalarVector Operator Overloads

/// # ScalarVector
/// 
/// A valid scalar vector
impl ScalarVector {
    /// Create a new valid scalar vector
    pub fn new (v: &Vec<BigInt>) -> ScalarVector {
        let mut r: Vec<Scalar> = Vec::new();
        for b in v {
            r.push(scalar_unwrap(Scalar::new(&b)));
        }
        ScalarVector { value: r }
    }

    /// Aggrate Scalars into one value
    pub fn sum_of_all (self) -> Scalar {
        let mut b: Vec<BigInt> = Vec::new();
        for s in self.value {
            b.push(s.value)
        }
        let sum: BigInt = b.iter().sum();
        scalar_unwrap(Scalar::new(&sum))
    }

    /// Negate all scalars in a vector
    pub fn neg (self) -> ScalarVector {
        let mut r: Vec<Scalar> = Vec::new();
        for s in self.value {
            r.push(s.neg())
        }
        ScalarVector { value: r }
    }

    /// ScalarVector**ScalarVector: inner product
    pub fn pow (self, sv: ScalarVector) -> Result<Scalar, &'static str> {
        let l = &self.value.len();
        if l != &sv.value.len() {
            panic!("Vectors must be the same length");
        }
        let rsv = self * sv;
        let r = rsv.sum_of_all();
        return Ok(r)
    }

    /// Append scalar and return new scalar vector
    pub fn append (mut self, s: Scalar) -> ScalarVector {
        self.value.push(s);
        self
    }
}

#[derive(Debug)]
struct PointVector {
    value: Vec<Point>,   
}

// PointVector operator overloads
impl ops::Add<PointVector> for PointVector {
    type Output = PointVector;
    fn add(self, _rhs: PointVector) -> PointVector {
        pv_unwrap(point_vector_decomposition(&self, Some(_rhs), None, VectorOp::Add))
    }
}

impl ops::Sub<PointVector> for PointVector {
    type Output = PointVector;
    fn sub(self, _rhs: PointVector) -> PointVector {
        pv_unwrap(point_vector_decomposition(&self, Some(_rhs), None, VectorOp::Sub))
    }
}
// End PointVector operator overloads

/// # PointVector
/// 
/// A valid point vector
impl PointVector {
    /// Create a new valid point vector
    pub fn new (v: &Vec<&str>) -> PointVector {
        let mut r: Vec<Point> = Vec::new();
        for b in v {
            r.push(point_unwrap(Point::new(&b)));
        }
        PointVector { value: r }
    }

    /// Negate all points in a vector
    pub fn neg (self) -> PointVector {
        let mut r: Vec<Point> = Vec::new();
        for p in self.value {
            r.push(p.neg())
        }
        PointVector { value: r }
    }

    /// Append point and return new point vector
    pub fn append (mut self, p: Point) -> PointVector {
        self.value.push(p);
        self
    }
}

// Helper methods
fn bit (h: &Vec<u8>, i: u8) -> u8 {
    let a: usize = num::integer::div_floor(i.into(), 8);
    (h[a] >> i % 8 ) & 1
}

/// Exponent
fn exponent (b: &BigInt, e: &BigInt, m: &BigInt) -> BigInt {
    b.modpow(e, m)
}

/// Invert
fn invert (x: &BigInt, p: &BigInt) -> BigInt  {
    exponent(x, &(p - BigInt::from(2_u8)), p)
}

/// Derive the x point
fn xfromy (y: &BigInt) -> BigInt {
    let three = BigInt::from(3_u8);
    let c = Curve::new();
    let temp = (y * y - &c.one) * invert(&(c.d * y * y + &c.one), &c.q);
    let mut x = exponent(&temp, &((&c.q + &three) / &c.h), &c.q);
    if (&x * &x - temp) % &c.q != c.zero {
        x = (&x * c.i) % &c.q;
    }
    if &x % c.two != c.zero {
        x = &c.q - x;
    }
    x
}

/// Convert BigInt to hex string
fn to_hex (mut n: BigInt) -> String {
    let mut a = [0u8; 32];
    for i in 0..a.len() {
        let b: BigInt = &n & BigInt::from(255_u8);
        let s: &str = &format!("{b}");
        let parse = match s.parse::<u8>() {
            Ok(v) => v,
            _=> 0,
        };
        a[i] = parse;
        n = (&n - b) / BigInt::from(256_u16);
    }
    hex::encode(a)
}

/// Create random scalars by hashing the string slice
pub fn hash_to_scalar (s: Vec<&str>) -> Scalar {
    let mut result = String::new();
    for v in &s {
        let mut hasher = Blake2s256::new();
        hasher.update(v);
        let hash = hasher.finalize().to_owned();
        result += &hex::encode(&hash[..]);
    }
    loop {
        let mut hasher = Blake2s256::new();
        hasher.update(&result);
        let hash = hasher.finalize().to_owned();
        // why is big endian needed here?
        let b = BigInt::from_bytes_be(Sign::Plus, &hash[..]);
        if b < Curve::new().l {
            return scalar_unwrap(Scalar::new(&b))
        }
        result = hex::encode(&hash[..]);
    }
}

/// Create random points by hashing the string slice
pub fn hash_to_point (s: Vec<&str>) -> Point {
    let mut result = String::new();
    for v in &s {
        let mut hasher = Blake2s256::new();
        hasher.update(v);
        let hash = hasher.finalize().to_owned();
        result += &hex::encode(&hash[..]);
    }
    loop {
        let mut hasher = Blake2s256::new();
        hasher.update(&result);
        let hash = hasher.finalize().to_owned();
        result = hex::encode(&hash[..]);
        println!("htp result: {}", result);
        // why is big endian needed here?
        let b = BigInt::from_bytes_be(Sign::Plus, &hash[..]);
        let b2 = BigInt::from_bytes_be(Sign::Plus, &hash[..]);
            let p1 = point_unwrap(Point::new(&to_hex(b)));
        let p2 = point_unwrap(Point::new(&to_hex(b2)));
        if p1 != Point::zero_point() {
            return p2 * scalar_unwrap(Scalar::new(&Curve::new().h));
        }
    }
}

/// Helper for ScalarVector Operator Overloading
fn scalar_vector_decomposition (
    sv1: &ScalarVector,
    sv2: Option<ScalarVector>,
    s: Option<Scalar>,
    o: VectorOp) -> Result<ScalarVector, &'static str> {
    let l = sv1.value.len();
    let mut l2 = 0;
    match &sv2 {
        Some(sv2) => l2 = sv2.value.len(),
        _=> (),
    }
    if l != l2 && s.is_none() {
        panic!("Vectors must be the same length!")
    }
    let mut r: Vec<Scalar> = Vec::new();
    for i in 0..l {
        let sa1 = sv1.value[i].value.to_bytes_le().1;
        let mut sa2: Vec<u8> = Vec::new();
        match &sv2 {
            Some(sv2) => sa2 = sv2.value[i].value.to_bytes_le().1,
            _=> (),
        }
        let sb1 = BigInt::from_bytes_le(Sign::Plus, &sa1);
        let sb2 = BigInt::from_bytes_le(Sign::Plus, &sa2);
        let s3 = scalar_unwrap(Scalar::new(&sb1));
        let s4 = scalar_unwrap(Scalar::new(&sb2));
            match o {
                VectorOp::Add => r.push(s3 + s4),
                VectorOp::Sub => r.push(s3 - s4),
                VectorOp::Mul => r.push(s3 * s4),
                // Not tested yet
                VectorOp::Had => {
                    match &s {
                        Some(s) => {
                            let sb = s.value.to_bytes_le().1;
                            let s2 = Scalar::new(&BigInt::from_bytes_le(Sign::Plus, &sb));
                            r.push(s3 * scalar_unwrap(s2));
                        },
                        _=> (),
                    }
                },
                VectorOp::Div => r.push(s3 - s4),
            }
        }
        Ok(ScalarVector { value: r })
}

/// Helper for ScalarVector Operator Overloading
fn point_vector_decomposition (
    pv1: &PointVector,
    pv2: Option<PointVector>,
    s: Option<Scalar>,
    o: VectorOp) -> Result<PointVector, &'static str> {
    let l = pv1.value.len();
    let mut l2 = 0;
    match &pv2 {
        Some(pv2) => l2 = pv2.value.len(),
        _=> (),
    }
    if l != l2 && s.is_none() {
        panic!("Vectors must be the same length!")
    }
    let mut r: Vec<Point> = Vec::new();
    let mut pv3: &Vec<Point> = &Vec::new();
    for i in 0..l {
        match &pv2 {
            Some(pv2) => pv3 = &pv2.value,
            _=> (),
        }
            match o {
                VectorOp::Add => r.push(&pv1.value[i] + &pv3[i]),
                VectorOp::Sub => r.push(&pv1.value[i] - &pv3[i]),
                _=> ()
            }
        }
        Ok(PointVector { value: r })
}

/// Helper method for unwrapping scalars in various functions
fn scalar_unwrap (s: Result<Scalar, &'static str>) -> Scalar {
    let value: BigInt = BigInt::from(0_u8);
    let hex_value = to_hex(BigInt::from(0_u8));
    let default: Scalar = Scalar { value, hex_value };
    match s {
        Ok(s) => s,
        _=> default
    }
}

/// Helper method for unwrapping points in various functions
fn point_unwrap (p: Result<Point, &'static str>) -> Point {
    match p {
        Ok(p) => p,
        _=> Point::zero_point()
    }
}

/// Helper method for unwrapping scalar vectors in various functions
fn sv_unwrap (sv: Result<ScalarVector, &'static str>) -> ScalarVector {
    let default: Vec<Scalar> = Vec::new();
    match sv {
        Ok(sv) => sv,
        _=> ScalarVector { value: default }
    }
}

/// Helper method for unwrapping point vectors in various functions
fn pv_unwrap (pv: Result<PointVector, &'static str>) -> PointVector {
    let default: Vec<Point> = Vec::new();
    match pv {
        Ok(pv) => pv,
        _=> PointVector { value: default }
    }
}

/// Helper method for unwrapping hex bytes in various functions
fn hex_unwrap (b: &Result<Vec<u8>, hex::FromHexError>) -> Vec<u8> {
    let default: Vec<u8> = Vec::new();
    match b {
        Ok(b) => b.to_vec(),
        _=> default
    }
}
// End helper methods


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negate_scalar() {
        let s = Scalar::new(&BigInt::from(1_u8));
        let e = Curve::new().l - BigInt::from(1_u8);
        assert_eq!(s.unwrap().neg().value, e)
    }

    /// return scalar vectors for testing
    fn get_sv() -> (ScalarVector, ScalarVector) {
        let start: u8 = 1;
        let end: u8 = 7;
        let mut v1: Vec<Scalar> = Vec::new();
        let mut v2: Vec<Scalar> = Vec::new();
        for i in start..end {
            if i < 4 {
                v1.push(Scalar::new(&BigInt::from(i)).unwrap());
            } else {
                v2.push(Scalar::new(&BigInt::from(i)).unwrap());
            }
        }
        (ScalarVector { value: v1 }, ScalarVector { value: v2 })
    }

    #[test]
    fn new_sv() {
        let bv: Vec<BigInt> = vec![BigInt::from(1_u8), BigInt::from(2_u8)];
        let sv = ScalarVector::new(&bv);
        assert_eq!(sv.value.len(), 2);
    }

    #[test]
    fn new_pv() {
        let v: Vec<&str> = vec![
            "5866666666666666666666666666666666666666666666666666666666666666",
            "c9a3f86aae465f0e56513864510f3997561fa2c9e85ea21dc2292309f3cd6022"
            ];
        let pv = PointVector::new(&v);
        assert_eq!(pv.value.len(), 2);
    }

    #[test]
    fn sum_of_all() {
        let svs = get_sv();
        let sv1 = svs.0;
        let e = Scalar::new(&BigInt::from(6_u8)).unwrap();
        assert_eq!(e, sv1.sum_of_all());
    }

    #[test]
    fn append_sv() {
        let svs = get_sv();
        let sv1 = svs.0;
        let sv2 = sv1.append(Scalar::new(&BigInt::from(7_u8)).unwrap());
        assert_eq!(sv2.value.len(), 4);
    }

    #[test]
    fn append_pv() {
        let v: Vec<&str> = vec![
            "5866666666666666666666666666666666666666666666666666666666666666",
            "c9a3f86aae465f0e56513864510f3997561fa2c9e85ea21dc2292309f3cd6022"
            ];
        let pv = PointVector::new(&v);
        let pv2 = pv.append(Point::new("d4b4f5784868c3020403246717ec169ff79e26608ea126a1ab69ee77d1b16712").unwrap());
        assert_eq!(pv2.value.len(), 3);
    }

    #[test]
    fn sum_points() {
        let p1 = Point::base_generator() + Point::zero_point();
        let p2 = Point::base_generator();
        assert_eq!(p1, p2);
    }
}
