///| Pretty Printer (ref Philip Wadler's "A prettier printer")
enum DOC {
  NIL
  CONCAT(DOC, DOC)
  UNION(DOC, DOC)
  TEXT(String)
  LINE
  NEST(Int, DOC)
}

///|
enum Doc {
  Nil
  Text(String, Doc)
  Line(Int, Doc)
}

///|
impl Add for DOC with op_add(self : DOC, other : DOC) -> DOC {
  CONCAT(self, other)
}

///|
pub fn tr(self : DOC, other : String) -> DOC {
  self + text(other)
}

///|
pub fn tl(self : DOC, other : String) -> DOC {
  text(other) + self
}

///|
pub fn op_sub(self : DOC, other : DOC) -> DOC {
  self + text(" ") + other
}

///|
pub fn op_div(self : DOC, other : DOC) -> DOC {
  self + line() + other
}

///|
pub fn nil() -> DOC {
  NIL
}

///|
pub fn text(s : String) -> DOC {
  TEXT(s)
}

///|
pub fn line() -> DOC {
  LINE
}

///|
pub fn nest(i : Int, d : DOC) -> DOC {
  NEST(i, d)
}

///|
pub fn concat(x : DOC, y : DOC) -> DOC {
  CONCAT(x, y)
}

///|
pub fn group(d : DOC) -> DOC {
  UNION(d.flatten(), d)
}

///|
pub fn flatten(self : DOC) -> DOC {
  match self {
    NIL => NIL
    CONCAT(x, y) => CONCAT(x.flatten(), y.flatten())
    NEST(i, d) => NEST(i, d.flatten())
    UNION(x, _) => x.flatten()
    LINE => TEXT(" ")
    TEXT(s) => TEXT(s)
  }
}

///|
pub fn layout(self : Doc) -> String {
  match self {
    Nil => ""
    Text(s, d) => s + d.layout()
    Line(i, d) => "\n" + " ".repeat(i) + d.layout()
  }
}

///|
fn fits(w : Int, self : Doc) -> Bool {
  guard w >= 0 else { false }
  match self {
    Nil => true
    Text(s, d) => fits(w - s.length(), d)
    Line(_) => true
  }
}

///|
fn be(s : @immut/list.T[(Int, DOC)], w : Int, k : Int) -> Doc {
  fn better(w, k, x, y) {
    if fits(w - k, x) {
      x
    } else {
      y
    }
  }

  match s {
    Nil => Nil
    Cons((_, NIL), z) => be(z, w, k)
    Cons((i, CONCAT(x, y)), z) => be(Cons((i, x), Cons((i, y), z)), w, k)
    Cons((i, NEST(j, x)), z) => be(Cons((i + j, x), z), w, k)
    Cons((_, TEXT(s)), z) => Text(s, be(z, w, k + s.length()))
    Cons((i, LINE), z) => Line(i, be(z, w, i))
    Cons((i, UNION(x, y)), z) =>
      better(w, k, be(Cons((i, x), z), w, k), be(Cons((i, y), z), w, k))
  }
}

///|
pub fn best(self : DOC, w : Int, k : Int) -> Doc {
  be(Cons((0, self), Nil), w, k)
}

///|
pub fn pretty(self : DOC, w : Int) -> String {
  self.best(w, 0).layout()
}

///|
pub fn fold(ls : Array[DOC], f : (DOC, DOC) -> DOC) -> DOC {
  ls.rev_fold(init=nil(), f)
}

///|
pub fn spread(ls : Array[DOC]) -> DOC {
  fold(ls, DOC::op_sub)
}

///|
pub fn stack(ls : Array[DOC]) -> DOC {
  fold(ls, DOC::op_div)
}

///|
pub fn between(self : DOC, l : String, r : String) -> DOC {
  group(text(l) + nest(2, line() + self) + line() + text(r))
}

///|
pub fn op_mod(self : DOC, other : DOC) -> DOC {
  self + UNION(text(" "), line()) + other
}

///|
pub fn fill_words(words : Array[DOC]) -> DOC {
  let mut doc = nil()
  for word in words {
    doc = doc + word + text(" ")
  }
  doc
}

///|
impl Show for DOC with to_string(s) {
  s.pretty(80)
}

///|
impl Show for DOC with output(s, l) {
  l.write_string(s.to_string())
}

///|
test "show tree" {
  enum Tree {
    Node(String, Array[Tree])
  }
  letrec show_bracket = fn(ts : ArrayView[Tree]) -> DOC {
    match ts {
      [] => nil()
      ts => nest(1, show_trees(ts)).tl("[").tr("]")
    }
  }
  and show_trees = fn(ts : ArrayView[Tree]) -> DOC {
    match ts {
      [t] => show_tree(t)
      [t, .. ts] => show_tree(t).tr(",") + line() + show_trees(ts)
      [] => abort("unreachable")
    }
  }
  and show_tree = fn(self : Tree) -> DOC {
    let Node(s, ts) = self
    group(nest(s.length(), show_bracket(ts[:])).tl(s))
  }

  let tree = Node("aaa", [
    Node("bbbb", [Node("cc", []), Node("dd", [])]),
    Node("eee", []),
    Node("fff", [Node("gg", []), Node("hh", []), Node("ii", [])]),
  ])
  let doc = show_tree(tree)
  inspect(doc, content="aaa[bbbb[cc, dd], eee, fff[gg, hh, ii]]")
  inspect(
    doc.pretty(20),
    content=
      #|aaa[bbbb[cc, dd],
      #|    eee,
      #|    fff[gg, hh, ii]]
    ,
  )
  inspect(
    doc.pretty(10),
    content=
      #|aaa[bbbb[cc,
      #|         dd],
      #|    eee,
      #|    fff[gg,
      #|        hh,
      #|        ii]]
    ,
  )
}
