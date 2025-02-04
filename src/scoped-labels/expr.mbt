///|
type Level Int derive(Compare, Eq)

///|
pub fn enter(self : Level) -> Level {
  self._ + 1
}

///|
enum Expr {
  Var(String)
  Let(String, Expr, Expr)
  Lam(Array[String], Expr)
  Call(Expr, Array[Expr])
  RecordEmpty
  RecordExtend(String, Expr, Expr)
  RecordRestrict(Expr, String)
  RecordSelect(Expr, String)
}

///|
enum Type {
  TVar(Ref[TypeVar[Type]])
  TArr(Array[Type], Type)
  TApp(Type, Array[Type])
  TConst(String)
  TRecord(Row)
}

///|
enum Row {
  REmpty
  RExtend(String, Type, Row)
  RVar(Ref[TypeVar[Row]])
}

///|
enum TypeVar[T] {
  Unbound(Int, Level)
  Link(T)
  Generic(Int)
}

///|
impl Show for Row with to_string(self) {
  match self {
    REmpty => ""
    RExtend(label, typ, row_typ) =>
      "{" +
      (loop "\{label} = \{typ}", row_typ {
        cur, REmpty => cur
        cur, RExtend(label, expr, record) =>
          continue cur + ", \{label} : \{expr}", record
        cur, rest => "\{cur} | \{rest}"
      }) +
      "}"
    RVar({ val: Link(t) }) => t.to_string()
    RVar({ val: Unbound(id, _) }) => "_\{id}"
    RVar({ val: Generic(id) }) => "\{id}"
  }
}

///|
impl Show for Row with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
impl Show for Type with to_string(self) {
  let m = Map::new()
  let mut name_c = -1
  fn next_name() {
    name_c += 1
    int_to_letter(name_c).to_string()
  }

  fn string_of_ty {
    TVar({ val: Link(t) }) => string_of_ty(t)
    TVar({ val: Unbound(id, _) }) => "_\{id}"
    TVar({ val: Generic(id) }) =>
      match m[id] {
        Some(x) => x
        None => {
          let name = next_name()
          m[id] = name
          name
        }
      }
    TRecord(row) => "\{row}"
    TArr(args, ret) => {
      let args = join_string(" -> ", args.map(string_of_ty)[:])
      "(\{args}) -> \{string_of_ty(ret)}"
    }
    TApp(t, args) =>
      string_of_ty(t) + "[" + join_string(", ", args.map(string_of_ty)[:]) + "]"
    TConst(c) => c
  }

  let s = string_of_ty(self)
  let universals = if m.size() > 0 {
    "forall " + join_string(" ", m.values().to_array()[:]) + ". "
  } else {
    ""
  }
  universals + s
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
    Lam(x, e) => {
      let arg = join_string(" ", x.map(Show::to_string)[:])
      "fun \{arg} -> \{e}"
    }
    Call(e, args) => {
      let params = join_string(", ", args.map(Show::to_string)[:])
      "\{e}(\{params})"
    }
    RecordEmpty => "{}"
    RecordRestrict(record, label) => "\{record} - \{label}"
    RecordSelect(record, label) => "\{record}.\{label}"
    RecordExtend(label, expr, record) =>
      "{" +
      (loop "\{label} = \{expr}", record {
        cur, RecordEmpty => cur
        cur, RecordExtend(label, expr, record) =>
          continue cur + ", \{label} = \{expr}", record
        cur, rest => "\{cur} | \{rest}"
      }) +
      "}"
  }
}

///|
fn join_string(sep : String, strs : ArrayView[String]) -> String {
  match strs.length() {
    0 => ""
    1 => strs[0]
    _ => strs[0] + sep + join_string(sep, strs[1:])
  }
}

///|
impl Show for Expr with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
fn int_to_letter(x : Int) -> Char {
  let base = Char::to_int('a')
  Char::from_int(base + x)
}
