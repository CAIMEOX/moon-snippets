///|
let ty_int : Type = TConst("int")

///|
let ty_bool : Type = TConst("bool")

///|
fn forall(x : Int) -> Type {
  TVar({ val: Generic(x) })
}

///|
let assumptions : @immut/hashmap.T[String, Type] = @immut/hashmap.from_array([
  ("zero", ty_int),
  ("succ", TArr([ty_int], ty_int)),
  ("true", ty_bool),
  ("false", ty_bool),
  ("id", TArr([forall(1)], forall(1))),
])

///|
fn run_test(self : Expr) -> String {
  match infer?(self, 1, assumptions) {
    Ok(x) => x.generalize(0).to_string()
    Err(TypeError(e)) => e
  }
}

///|
test {
  inspect!(run_test(Var("zero")), content="int")
  inspect!(run_test(Var("succ")), content="(int) -> int")
  inspect!(run_test(Call(Var("succ"), [Var("zero")])), content="int")
  inspect!(run_test(Var("id")), content="forall a. (a) -> a")
  inspect!(run_test(Call(Var("id"), [Var("succ")])), content="(int) -> int")
  inspect!(run_test(Call(Var("id"), [Var("true")])), content="bool")
  inspect!(
    run_test(Let("x", Var("x"), Var("x"))),
    content="infer: unbound variable: x",
  )
  inspect!(
    run_test(Lam(["f"], Call(Var("f"), [Var("f")]))),
    content="occurs: recursive type",
  )
  inspect!(
    Lam(["x"], Let("y", Lam(["z"], Var("z")), Var("y"))).run_test(),
    content="forall a b. (a) -> (b) -> b",
  )
}
