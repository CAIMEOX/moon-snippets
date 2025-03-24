///|
pub type TypeRep String derive(Eq, Hash)

///|
pub type Dyn Error

///|
trait Dynamic {
  to_dynamic(Self) -> Dyn
  from_dynamic(Dyn) -> Self
  type_rep() -> TypeRep
}

///|
pub(open) trait SumTuple {
  sumOf(Self) -> Int
}

///|
priv trait Unfold {
  sum(Self) -> Int
  concat(Self) -> String
  fmap(Self, (Int) -> Int) -> Self
}

///|
impl Unfold for Int with fmap(n, f) {
  f(n)
}

///|
impl Unfold for Int with sum(n) {
  n
}

///|
impl Unfold for Int with concat(n) {
  n.to_string()
}

///|
impl Unfold for String with fmap(n, f) {
  f(n.length()).to_string()
}

///|
impl Unfold for String with sum(n) {
  n.length()
}

///|
impl Unfold for String with concat(n) {
  n
}

///|
impl[U : Unfold, V : Unfold] Unfold for (U, V) with sum(n) {
  let (u, v) = n
  U::sum(u) + V::sum(v)
}

///|
impl[U : Unfold, V : Unfold] Unfold for (U, V) with concat(uv) {
  let (u, v) = uv
  U::concat(u) + V::concat(v)
}

///|
impl[U : Unfold, V : Unfold] Unfold for (U, V) with fmap(n, f) {
  let (u, v) = n
  (U::fmap(u, f), V::fmap(v, f))
}

///|
impl SumTuple for Int with sumOf(self) {
  self
}

///|
impl[R : SumTuple] SumTuple for (R, Int) with sumOf(r) {
  let (r, i) = r
  R::sumOf(r) + i
}

///|
fn _tuple_bomb[A](x : A) -> (((A, (A, A)), A), ((A, A), A)) {
  (((x, (x, x)), x), ((x, x), x))
}

///|
test {
  let x = (((113, ("0", 4)), (3, 4)), (1, 2))
  let y = (113, (2, 4))
  let z = ((((x.fmap(fn(x) { x / 200 }), x), y), y), x)
  let w = ((z, (z, z)), ((z, z), (z, z)))
  inspect!(x.sum(), content="128")
  inspect!(
    x.fmap(fn(x) { x * 4 }),
    content=
      #|(((452, ("4", 16)), (12, 16)), (4, 8))
    ,
  )
  inspect!(x.concat(), content="113043412")
  inspect!(y.sum(), content="119")
  inspect!(z.sum(), content="495")
  inspect!(z.concat(), content="00000001130434121132411324113043412")
  inspect!(
    w.concat(),
    content=
      #|00000001130434121132411324113043412000000011304341211324113241130434120000000113043412113241132411304341200000001130434121132411324113043412000000011304341211324113241130434120000000113043412113241132411304341200000001130434121132411324113043412
    ,
  )
  inspect!(w.sum(), content="3465")
}

///|
pub type! UnitE Unit

///|
pub type! StringE String

///|
pub type! IntE Int

///|
pub type! UIntE UInt

///|
pub type! ShowE &Show

///|
impl Dynamic for Unit with type_rep() {
  "Unit"
}

///|
impl Dynamic for Int with type_rep() {
  "Int"
}

///|
impl Dynamic for String with type_rep() {
  "String"
}

///|
impl Dynamic for UInt with type_rep() {
  "UInt"
}

///|
impl Dynamic for &Show with type_rep() {
  "&Show"
}

///|
impl Dynamic for Unit with to_dynamic(_self) {
  UnitE(()) |> Dyn
}

///|
impl Dynamic for Unit with from_dynamic(self) {
  match self {
    Dyn(UnitE(_)) => ()
    _ => abort("expected Unit")
  }
}

///|
impl Dynamic for Int with to_dynamic(self) {
  IntE(self) |> Dyn
}

///|
impl Dynamic for Int with from_dynamic(self) {
  match self {
    Dyn(IntE(x)) => x
    _ => abort("expected Int")
  }
}

///|
impl Dynamic for String with to_dynamic(self) {
  StringE(self) |> Dyn
}

///|
impl Dynamic for String with from_dynamic(self) {
  match self {
    Dyn(StringE(x)) => x
    _ => abort("expected String")
  }
}

///|
impl Dynamic for UInt with to_dynamic(self) {
  UIntE(self) |> Dyn
}

///|
impl Dynamic for UInt with from_dynamic(self) {
  match self {
    Dyn(UIntE(x)) => x
    _ => abort("expected UInt")
  }
}

///|
impl Dynamic for &Show with to_dynamic(self) {
  ShowE(self) |> Dyn
}

///|
impl Dynamic for &Show with from_dynamic(self) {
  match self {
    Dyn(ShowE(x)) => x
    _ => abort("exepcted ShowE")
  }
}

///|
type DynMap Map[TypeRep, Dyn]

///|
pub fn insert[T : Dynamic](self : DynMap, value : T) -> Unit {
  self._.set(T::type_rep(), value.to_dynamic())
}

///|
pub fn query[T : Dynamic](self : DynMap) -> T? {
  self._.get(T::type_rep()).map(T::from_dynamic)
}

///|
test {
  let map : DynMap = {}
  map.insert(42)
  map.insert("Hello")
  inspect!((map.query() : UInt?), content="None")
  inspect!((map.query().unwrap() : String), content="Hello")
  inspect!((map.query().unwrap() : Int), content="42")
  map.insert(114514U)
  inspect!((map.query().unwrap() : UInt), content="114514")
}
