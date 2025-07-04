/// Level represents the nesting depth of let-expressions in the type inference process.
/// This is a key optimization in the Hindley-Milner type system that prevents
/// premature generalization of type variables. Higher levels mean deeper nesting.
/// 
/// Example: In "let f = λx.x in let g = f in g", 
/// - f is at level 1, g is at level 2
/// - This prevents f's type from being generalized too early
type Level Int derive(Compare, Eq)

/// Enter a deeper level when processing nested let-expressions.
/// This is called when we encounter a let-binding to ensure proper
/// type variable scoping and generalization.
pub fn enter(self : Level) -> Level {
  self.inner() + 1
}

///|
const SEP : String = " "

/// Abstract syntax tree for expressions in our simple functional language.
/// This represents the programs we want to type-check.
enum Expr {
  /// Variable reference (e.g., "x", "f")
  Var(String)
  /// Let binding: "let x = e1 in e2"
  /// Introduces a new binding that can be polymorphic
  Let(String, Expr, Expr)
  /// Lambda abstraction: "λx y z. body"
  /// Creates a function with multiple parameters
  Lam(Array[String], Expr)
  /// Function application: "f(arg1, arg2, ...)"
  /// Applies a function to arguments
  Call(Expr, Array[Expr])
}

/// Types in our type system. This represents what types expressions can have.
enum Type {
  /// Type variable: can be unified with other types
  /// Contains a mutable reference to track unification state
  TVar(Ref[TypeVar])
  /// Function type: "(arg1, arg2, ...) -> return_type"
  /// Represents functions that take multiple arguments
  TArr(Array[Type], Type)
  /// Type application: "List[Int]", "Map[String, Bool]"
  /// Represents parameterized types (generics)
  TApp(Type, Array[Type])
  /// Constant type: "int", "bool", "string"
  /// Base types that cannot be further decomposed
  TConst(String)
}

/// Internal representation of type variables with different states.
/// This is the heart of the unification algorithm.
priv enum TypeVar {
  /// Unbound type variable waiting to be unified
  /// - id: unique identifier for this type variable
  /// - level: the nesting level where this variable was created
  Unbound(Int, Level)
  /// Type variable that has been unified with a concrete type
  /// - the Type it points to is the "solution" for this variable
  Link(Type)
  /// Generic type variable that represents a type parameter
  /// - used in polymorphic types like "forall a. a -> a"
  /// - id: identifier for printing (becomes 'a', 'b', etc.)
  Generic(Int)
}

/// Convert a type to a human-readable string representation.
impl Show for Type with to_string(self) {
  // Map to track generic variable names (ensures consistent naming)
  let m = Map::new()
  let mut name_c = -1
  let next_name = fn() {
    name_c += 1
    int_to_letter(name_c).to_string()
  }
  letrec string_of_ty = fn(t) {
    match t {
      TVar({ val: Link(t) }) => string_of_ty(t)
      TVar({ val: Unbound(id, _) }) => "_\{id}"
      TVar({ val: Generic(id) }) =>
        match m.get(id) {
          Some(x) => x
          None => {
            let name = next_name()
            m[id] = name
            name
          }
        }
      TArr(args, ret) => {
        let args = args.map(string_of_ty).join(" -> ")
        "(\{args}) -> \{string_of_ty(ret)}"
      }
      TApp(t, args) => {
        let s = args.map(string_of_ty).join(", ")
        "\{string_of_ty(t)}[\{s}]"
      }
      TConst(c) => c
    }
  }

  let s = string_of_ty(self)
  // Add "forall" quantifier if there are generic type variables
  guard m.size() > 0 else { s }
  "forall \{m.values().join(SEP)}.\{s}"
}

///|
impl Show for Type with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
impl Show for Expr with to_string(self) {
  match self {
    Var(x) => x
    Let(x, e1, e2) => "let \{x} = \{e1} in \{e2}"
    Lam(x, e) => "fun \{x.join(SEP)} -> \{e}"
    Call(e, args) => {
      let ar = args.map(Expr::to_string).join(", ")
      "\{e}(\{ar})"
    }
  }
}

///|
impl Show for Expr with output(self, logger) {
  logger.write_string(self.to_string())
}

fn int_to_letter(x : Int) -> Char {
  let base = Char::to_int('a')
  Int::unsafe_to_char(base + x)
}
