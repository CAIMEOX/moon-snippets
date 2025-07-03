///|
type Level Int derive(Compare, Eq)

///|
pub fn enter(self : Level) -> Level {
  self.inner() + 1
}

///|
const SEP : String = " "

///|
enum Expr {
  Var(String)
  Let(String, Expr, Expr)
  Lam(Array[String], Expr)
  Call(Expr, Array[Expr])
}

///|
enum Type {
  TVar(Ref[TypeVar])
  TArr(Array[Type], Type)
  TApp(Type, Array[Type])
  TConst(String)
}

///|
priv enum TypeVar {
  Unbound(Int, Level)
  Link(Type)
  Generic(Int)
}

///|
impl Show for Type with to_string(self) {
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

///|
fn int_to_letter(x : Int) -> Char {
  let base = Char::to_int('a')
  Int::unsafe_to_char(base + x)
}
