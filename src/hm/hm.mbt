///|
let ty_int : Type = TConst("int")

///|
let ty_bool : Type = TConst("bool")

///| Helper function to create generic type variables for testing.
/// This represents polymorphic type parameters like 'a', 'b', etc.
fn forall(x : Int) -> Type {
  TVar({ val: Generic(x) })
}

///| Initial type environment with some basic functions and constants.
/// This demonstrates how built-in functions can have polymorphic types.
/// 
/// Notable examples:
/// - "id" has type "forall a. a -> a" (polymorphic identity function)
/// - "succ" has type "int -> int" (monomorphic successor function)
/// - Basic constants have their expected types
let assumptions : @immut/hashmap.T[String, Type] = @immut/hashmap.from_array([
  ("zero", ty_int), // 0 : int
  ("succ", TArr([ty_int], ty_int)), // succ : int -> int  
  ("true", ty_bool), // true : bool
  ("false", ty_bool), // false : bool
  ("id", TArr([forall(1)], forall(1))), // id : forall a. a -> a
])

///| Test helper that runs type inference and returns a readable result.
/// Starts inference at level 1 and generalizes to level 0, which means
/// any type variables created during inference become polymorphic.
fn run_test(expr : Expr) -> String {
  expr.infer(1, assumptions).generalize(0).to_string() catch {
    TypeError(e) => e
  }
}

///| Test suite demonstrating various aspects of HM type inference.
test {
  // Basic variable lookup: zero has type int
  inspect(run_test(Var("zero")), content="int")

  // Function types: succ is a function from int to int
  inspect(run_test(Var("succ")), content="(int) -> int")

  // Function application: applying succ to zero gives int
  inspect(run_test(Call(Var("succ"), [Var("zero")])), content="int")

  // Polymorphic function: id has a universal type
  inspect(run_test(Var("id")), content="forall a.(a) -> a")

  // Polymorphic instantiation: id applied to succ becomes int -> int
  // This shows how the polymorphic type gets specialized
  inspect(run_test(Call(Var("id"), [Var("succ")])), content="(int) -> int")

  // Another instantiation: id applied to true becomes bool
  // Same polymorphic function, different instantiation
  inspect(run_test(Call(Var("id"), [Var("true")])), content="bool")

  // Error case: unbound variable
  inspect(
    run_test(Let("x", Var("x"), Var("x"))),
    content="infer: unbound variable: x",
  )

  // Error case: occurs check prevents infinite types
  // λf. f f would require f : f -> a for some a, which is impossible
  inspect(
    run_test(Lam(["f"], Call(Var("f"), [Var("f")]))),
    content="occurs: recursive type",
  )

  // Let-polymorphism: the inner function λz.z gets polymorphic type
  // Even though it's used in a specific context, it remains general
  inspect(
    Lam(["x"], Let("y", Lam(["z"], Var("z")), Var("y"))) |> run_test(),
    content="forall a b.(a) -> (b) -> b",
  )

  // Partial application: calling the above with zero gives a polymorphic function
  inspect(
    Call(Lam(["x"], Let("y", Lam(["z"], Var("z")), Var("y"))), [Var("zero")])
    |> run_test(),
    content="forall a.(a) -> a",
  )

  // Full application: the polymorphic function applied to true gives bool
  // This shows the complete chain: create polymorphic function, instantiate it
  inspect(
    Call(
      // (fun x -> let y = fun z -> z in y)(zero)(true) : bool
      Call(Lam(["x"], Let("y", Lam(["z"], Var("z")), Var("y"))), [Var("zero")]),
      [Var("true")],
    )
    |> run_test(),
    content="bool",
  )
}
