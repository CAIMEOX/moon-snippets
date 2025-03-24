///|
typealias Z[A, B] = (Zip[A, B]) -> Iter[(A, B)]

///|
priv struct Zip[A, B] {
  runZip : (A) -> (Z[A, B]) -> Iter[(A, B)]
}

///|
pub fn zip_[A, B](xs : Iter[A], ys : Iter[B]) -> Iter[(A, B)] {
  fn f(x : A, xk : Z[A, B]) -> Z[A, B] {
    fn(yk) { (yk.runZip)(x)(xk) }
  }

  let b : Z[A, B] = fn(_) { Iter::empty() }
  let xz : Z[A, B] = foldr(xs, b, f)
  fn g(y, yk) {
    { runZip: fn(x) { fn(xk) { xk(yk).prepend((x, y)) } } }
  }

  let c = { runZip: fn(_) { fn(_) { Iter::empty() } } }
  let yz = foldr(ys, c, g)
  xz(yz)
}

///|
test {
  let i1 = [1, 2, 3, 5].iter()
  let i2 = [7, 8, 9, 4].iter()
  let z = zip_(i1, i2)
  inspect!(z, content="[(1, 7), (2, 8), (3, 9), (5, 4)]")
}

///| Hyperfunction version of zip
priv struct Hyper[A, B] {
  invoke : (Hyper[B, A]) -> B
}

///|
fn foldr[A, B](xs : Iter[A], a : B, f : (A, B) -> B) -> B {
  fn g(r, x) {
    fn(a) { r(f(x, a)) }
  }

  xs.fold(init=fn(x) { x }, g)(a)
}

///|
pub fn zip[A, B](xs : Iter[A], ys : Iter[B]) -> Iter[(A, B)] {
  fn f(x, xk) {
    {
      invoke: fn(yk : Hyper[Iter[(A, B)], (A) -> Iter[(A, B)]]) {
        (yk.invoke)(xk)(x)
      },
    }
  }

  fn g(y : B, yk : Hyper[Iter[(A, B)], (A) -> Iter[(A, B)]]) {
    { invoke: fn(xk) { fn(x) { (xk.invoke)(yk).prepend((x, y)) } } }
  }

  (foldr(xs, { invoke: fn { _ => Iter::empty() } }, f).invoke)(
    foldr(ys, { invoke: fn { _ => fn { _ => Iter::empty() } } }, g),
  )
}

///|
test {
  let i1 = [1, 2, 3].iter()
  let i2 = [4, 5, 6].iter()
  let i3 = [0, 7, 8, 9].iter()
  inspect!(zip(i2, i1), content="[(4, 1), (5, 2), (6, 3)]")
  inspect!(zip(i1, i2), content="[(1, 4), (2, 5), (3, 6)]")
  inspect!(zip(i1, i3), content="[(1, 0), (2, 7), (3, 8)]")
  inspect!(zip(i3, i1), content="[(0, 1), (7, 2), (8, 3)]")
}

///|
test "effect" {
  let i1 = [1, 2, 3].iter().map(println)
  let i2 = [4, 5, 6].iter().map(println)
  inspect!(zip(i2, i1), content="[((), ()), ((), ()), ((), ())]")
}
