///|
priv enum Expr[V] {
  Var(V)
  Zero
  One
  Plus(Expr[V], Expr[V])
  Times(Expr[V], Expr[V])
} derive(Show)

///|
pub trait SemiRing {
  zero() -> Self
  one() -> Self
  plus(Self, Self) -> Self
  times(Self, Self) -> Self
}

///|
impl SemiRing for Int with zero() {
  0
}

///|
impl SemiRing for Int with one() {
  1
}

///|
impl SemiRing for Int with plus(x, y) {
  x + y
}

///|
impl SemiRing for Int with times(x, y) {
  x * y
}

///|
impl[V] SemiRing for Expr[V] with zero() {
  Zero
}

///|
impl[V] SemiRing for Expr[V] with one() {
  One
}

///|
impl[V] SemiRing for Expr[V] with plus(x, y) {
  Plus(x, y)
}

///|
impl[V] SemiRing for Expr[V] with times(x, y) {
  Times(x, y)
}

///|
fn eval[D : SemiRing, V](self : Expr[V], f : (V) -> D) -> D {
  match self {
    Var(v) => f(v)
    Zero => D::zero()
    One => D::one()
    Plus(x, y) => D::plus(x.eval(f), y.eval(f))
    Times(x, y) => D::times(x.eval(f), y.eval(f))
  }
}

///|
fn evalS[D, V](self : Expr[V], ring : Semiring[D], f : (V) -> D) -> D {
  match self {
    Var(v) => f(v)
    Zero => ring.zero
    One => ring.one
    Plus(x, y) => (ring.plus)(x.evalS(ring, f), y.evalS(ring, f))
    Times(x, y) => (ring.times)(x.evalS(ring, f), y.evalS(ring, f))
  }
}

///|
test {
  enum Var {
    X
  } derive(Show, Eq)
  let example1 = Times(Var(X), Plus(Var(X), One))
  let res = example1.eval(fn { X => 5 })
  inspect!(res, content="30")
  let res2 = derivative(example1, X)
  inspect!(
    res2,
    content="Plus(Times(Var(X), Plus(One, Zero)), Times(Plus(Var(X), One), One))",
  )
}

///|
fn derivative[V : Eq](self : Expr[V], x : V) -> Expr[V] {
  match self {
    Var(y) => if y == x { SemiRing::one() } else { SemiRing::zero() }
    Zero | One => SemiRing::zero()
    Plus(e1, e2) => SemiRing::plus(derivative(e1, x), derivative(e2, x))
    Times(e1, e2) =>
      SemiRing::plus(
        SemiRing::times(e1, derivative(e2, x)),
        SemiRing::times(e2, derivative(e1, x)),
      )
  }
}

///|
pub struct Dual[D] {
  pri : D
  tan : D
}

///|
pub trait Monoid {
  zero() -> Self
  plus(Self, Self) -> Self
}

///|
pub struct Module[D, M] {
  scale : (D, M) -> M
}

///|
pub struct Kronecker[V, D, E] {
  _phantom : D
  delta : (V) -> E
}

///|
pub struct Nagata[D, E] {
  priN : D
  tanN : E
}

///|
pub struct Semiring[D] {
  zero : D
  one : D
  plus : (D, D) -> D
  times : (D, D) -> D
}

///|
fn Nagata::fmap[D, E, F](self : Nagata[D, E], f : (E) -> F) -> Nagata[D, F] {
  { priN: self.priN, tanN: f(self.tanN) }
}

///|
fn induceNagataRing[D : SemiRing, E : Monoid](
  self : Module[D, E]
) -> Semiring[Nagata[D, E]] {
  {
    zero: { priN: D::zero(), tanN: E::zero() },
    one: { priN: D::one(), tanN: E::zero() },
    plus: fn {
      x, y => { priN: D::plus(x.priN, y.priN), tanN: E::plus(x.tanN, y.tanN) }
    },
    times: fn {
      x, y =>
        {
          priN: D::times(x.priN, y.priN),
          tanN: E::plus(
            (self.scale)(x.priN, y.tanN),
            (self.scale)(y.priN, x.tanN),
          ),
        }
    },
  }
}

///|
pub type Dense[V, D] (V) -> D

///|
fn ap[V, D](self : Dense[V, D], arg : V) -> D {
  (self._)(arg)
}

///|
impl[D : SemiRing, V] Monoid for Dense[V, D] with zero() {
  fn { _ => D::zero() }
}

///|
impl[D : SemiRing, V] Monoid for Dense[V, D] with plus(x, y) {
  fn { v => D::plus((x._)(v), (y._)(v)) }
}

///|
fn induceKronecker[V : Eq, D : SemiRing]() -> Kronecker[V, D, Dense[V, D]] {
  {
    _phantom: D::one(),
    delta: fn { v => fn { w => if v == w { D::one() } else { D::zero() } } },
  }
}

///|
fn abstractD[V : Eq, D : SemiRing, E : Monoid](
  self : Kronecker[V, D, E],
  m : Module[D, E],
  var : (V) -> D,
  expr : Expr[V]
) -> Nagata[D, E] {
  let gen = fn { x => { priN: var(x), tanN: (self.delta)(x) } }
  let ring = induceNagataRing(m)
  expr.evalS(ring, gen)
}

///|
fn induceModule[D : SemiRing, V]() -> Module[D, Dense[V, D]] {
  { scale: fn { x, y => fn { v => D::times(x, (y._)(v)) } } }
}

///|
fn forwardAD_Dense[V : Eq, D : SemiRing](
  self : Expr[V],
  var : (V) -> D
) -> Nagata[D, Dense[V, D]] {
  abstractD(induceKronecker(), induceModule(), var, self)
}

///|
test {
  enum XY {
    X
    Y
  } derive(Eq)
  // example = (X * Y + X) + 1
  let example = Plus(Plus(Times(Var(X), Var(Y)), Var(X)), One)
  let var = fn {
    X => 5
    Y => 3
  }
  let e = forwardAD_Dense(example, var).tanN
  inspect!(e.ap(X), content="4")
  inspect!(e.ap(Y), content="5")
}

///|
impl[D : SemiRing] SemiRing for Dual[D] with zero() {
  { pri: D::zero(), tan: D::zero() }
}

///|
impl[D : SemiRing] SemiRing for Dual[D] with one() {
  { pri: D::one(), tan: D::zero() }
}

///|
impl[D : SemiRing] SemiRing for Dual[D] with plus(x, y) {
  { pri: D::plus(x.pri, y.pri), tan: D::plus(x.tan, y.tan) }
}

///|
impl[D : SemiRing] SemiRing for Dual[D] with times(x, y) {
  {
    pri: D::times(x.pri, y.pri),
    tan: D::plus(D::times(x.pri, y.tan), D::times(x.tan, y.pri)),
  }
}

///|
fn symbolic[V : Eq](self : Expr[V], x : V) -> Dual[Expr[V]] {
  forwardAD(self, Expr::Var, x)
}

///|
fn forwardAD[V : Eq, D : SemiRing](
  self : Expr[V],
  var : (V) -> D,
  x : V
) -> Dual[D] {
  fn deltaY(y) {
    if x == y {
      SemiRing::one()
    } else {
      SemiRing::zero()
    }
  }

  fn gen(y) {
    { pri: var(y), tan: deltaY(y) }
  }

  self.eval(gen)
}
