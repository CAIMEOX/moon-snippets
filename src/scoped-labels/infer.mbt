///| Hindley Milner Type Inference

///|
let name_counter : Ref[Int] = @ref.new(0)

///|
fn create_id() -> Int {
  name_counter.update(fn(x) { x + 1 })
  name_counter.val
}

///|
fn create_tvar(lvl : Level) -> Type {
  TVar({ val: Unbound(create_id(), lvl) })
}

///|
fn create_rvar(lvl : Level) -> Row {
  RVar({ val: Unbound(create_id(), lvl) })
}

///|
type! TypeError String

///| Checks if a type variable occurs in a type
trait Occurrence {
  occurs(Self, Int, Level) -> Unit!TypeError
}

///|
impl[V : Occurrence] Occurrence for Ref[TypeVar[V]] with occurs(self, id, lvl) {
  match self {
    { val: Link(t) } => t.occurs!(id, lvl)
    { val: Unbound(other_tv_id, other_lvl) } =>
      if id == other_tv_id {
        raise TypeError("occurs: recursive type")
      } else {
        let lvl = @math.minimum(lvl, other_lvl)
        self.val = Unbound(other_tv_id, lvl)
      }
    _ => raise TypeError("occurs: can not occur check a generic type variable")
  }
}

///|
impl Occurrence for Row with occurs(self, id, lvl) {
  match self {
    REmpty => ()
    RExtend(_, ty, row) => {
      ty.occurs!(id, lvl)
      row.occurs!(id, lvl)
    }
    RVar(tv) => tv.occurs!(id, lvl)
  }
}

///|
impl Occurrence for Type with occurs(self, id, lvl) {
  fn go(x : Type) -> Unit!TypeError {
    match x {
      TConst(_) => ()
      TApp(t1, rets) => {
        go!(t1)
        for r in rets {
          go!(r)
        }
      }
      TArr(args, ret) => {
        for a in args {
          go!(a)
        }
        go!(ret)
      }
      TVar(tv) => tv.occurs!(id, lvl)
      TRecord(record) => record.occurs!(id, lvl)
    }
  }

  go!(self)
}

///| Ability to generalize a type
trait Generalization {
  generalize(Self, Level) -> Self
}

///|
trait Unification {
  unify(Self, Self) -> Unit!TypeError
}

///|
impl Unification for Type with unify(self, other) {
  match (self, other) {
    (TConst(x), TConst(y)) =>
      if x != y {
        raise TypeError("unify: can not unify \{x} with \{y}")
      }
    (TArr(ls1, r1), TArr(ls2, r2)) =>
      if ls1.length() != ls2.length() {
        raise TypeError("unify: functions have different arity")
      } else {
        for i in 0..<ls1.length() {
          ls1[i].unify!(ls2[i])
        }
        r1.unify!(r2)
      }
    (TApp(t1, args1), TApp(t2, args2)) =>
      if args1.length() != args2.length() {
        raise TypeError("unify: type constructors have different arity")
      } else {
        t1.unify!(t2)
        for i in 0..<args1.length() {
          args1[i].unify!(args2[i])
        }
      }
    (TVar({ val: Link(t1) }), TVar({ val: Link(t2) })) => t1.unify!(t2)
    (TVar({ val: Unbound(id, level) } as v), ty)
    | (ty, TVar({ val: Unbound(id, level) } as v)) => {
      ty.occurs!(id, level)
      v.val = Link(ty)
    }
    (TRecord(t1), TRecord(t2)) => t1.unify!(t2)
    (x, y) => raise TypeError("unify: can not unify \{x} with \{y}")
  }
}

// | TRowExtend (label1, field_ty1, rest_row1), (TRowExtend _ as row2) ->
//         let rest_row1_tvar_ref_option =
//           match rest_row1 with
//           | TVar ({ contents = Unbound _ } as tvar_ref) -> Some tvar_ref
//           | _ -> None
//         in
//         let rest_row2 = rewrite_row row2 label1 field_ty1 in
//         (match rest_row1_tvar_ref_option with
//         | Some { contents = Link _ } ->
//             error "recursive row types" (* why this is row recursive *)
//         | _ -> ());
//         unify rest_row1 rest_row2

///|
impl Unification for Row with unify(self, other) {
  match (self, other) {
    (REmpty, REmpty) => ()
    (RVar({ val: Link(t1) }), RVar({ val: Link(t2) })) => t1.unify!(t2)
    (RVar({ val: Unbound(id, level) } as v), ty)
    | (ty, RVar({ val: Unbound(id, level) } as v)) => {
      ty.occurs!(id, level)
      v.val = Link(ty)
    }
    (RExtend(label1, field_ty1, rest_row1), RExtend(_) as row2) => {
      let rest_row1_tvar_ref_option = match rest_row1 {
        RVar({ val: Unbound(_) } as tvar_ref) => Some(tvar_ref)
        _ => None
      }
      let rest_row2 = rw_row!(row2, label1, field_ty1)
      match rest_row1_tvar_ref_option {
        Some({ val: Link(_) }) => raise TypeError("unify: recursive row types")
        _ => ()
      }
      rest_row1.unify!(rest_row2)
    }
    (r1, r2) =>
      raise TypeError("unify: can not unify row types \{r1} and \{r2}")
  }
}

///|
fn rw_row(self : Row, label : String, field_ty : Type) -> Row!TypeError {
  match self {
    REmpty => raise TypeError("rw_row: row does not contain label \{label}")
    RExtend(label2, field_ty2, rest_row2) =>
      if label == label2 {
        field_ty.unify!(field_ty2)
        rest_row2
      } else {
        RExtend(label2, field_ty2, rw_row!(rest_row2, label, field_ty))
      }
    RVar({ val: Link(row2) }) => rw_row!(row2, label, field_ty)
    RVar({ val: Unbound(_, lvl) } as rv) => {
      let rest_row2 = create_rvar(lvl)
      let ty2 = RExtend(label, field_ty, rest_row2)
      rv.val = Link(ty2)
      rest_row2
    }
    _ => raise TypeError("rw_row: unexpected generic type")
  }
}

///|
impl Generalization for Type with generalize(self, lvl) {
  match self {
    TVar({ val: Unbound(id, other_lvl) }) =>
      if other_lvl > lvl {
        TVar({ val: Generic(id) })
      } else {
        self
      }
    TApp(t, args) =>
      TApp(t.generalize(lvl), args.map(fn { x => x.generalize(lvl) }))
    TArr(args, ret) =>
      TArr(args.map(fn { x => x.generalize(lvl) }), ret.generalize(lvl))
    TVar({ val: Link(t) }) => t.generalize(lvl)
    TRecord(rec) => TRecord(rec.generalize(lvl))
    _ => self
  }
}

///|
impl Generalization for Row with generalize(self, lvl) {
  match self {
    REmpty => REmpty
    RExtend(label, ty, row) =>
      RExtend(label, ty.generalize(lvl), row.generalize(lvl))
    RVar({ val: Link(t) }) => t.generalize(lvl)
    _ => self
  }
}

///|
fn instantiate(self : Type, lvl : Level) -> Type {
  let tracking_typ = Map::new()
  let tracking_row = Map::new()
  fn inst_typ(ty) {
    match ty {
      TVar({ val: Generic(id) }) =>
        match tracking_typ[id] {
          Some(x) => x
          None => {
            let tvar = create_tvar(lvl)
            tracking_typ[id] = tvar
            tvar
          }
        }
      TVar({ val: Link(t) }) => inst_typ(t)
      TApp(t, args) => TApp(inst_typ(t), args.map(fn { x => inst_typ(x) }))
      TArr(args, ret) => TArr(args.map(fn { x => inst_typ(x) }), inst_typ(ret))
      TRecord(row) => TRecord(inst_row(row))
      _ => ty
    }
  }

  fn inst_row {
    REmpty => REmpty
    RExtend(label, field_typ, row_typ) =>
      RExtend(label, inst_typ(field_typ), inst_row(row_typ))
    RVar({ val: Link(t) }) => inst_row(t)
    RVar({ val: Generic(id) }) =>
      match tracking_row[id] {
        Some(x) => x
        None => {
          let tvar = create_rvar(lvl)
          tracking_row[id] = tvar
          tvar
        }
      }
    x => x
  }

  inst_typ(self)
}

///|
fn match_fun(self : Type, param_num : Int) -> (Array[Type], Type)!TypeError {
  match self {
    TVar({ val: Link(t) }) => match_fun!(t, param_num)
    TVar({ val: Unbound(_, lvl) } as tvar) => {
      let vars = Array::makei(param_num, fn(_) { create_tvar(lvl) })
      let ret = create_tvar(lvl)
      tvar.val = Link(TArr(vars, ret))
      (vars, ret)
    }
    TArr(params, ret) => {
      if params.length() != param_num {
        raise TypeError("match_fun: function has different arity")
      }
      (params, ret)
    }
    _ => raise TypeError("match_fun: not a function type")
  }
}

///|
pub fn infer(
  self : Expr,
  lvl : Level,
  env : @immut/hashmap.T[String, Type]
) -> Type!TypeError {
  match self {
    Var(name) =>
      match env[name] {
        Some(x) => {
          let t = instantiate(x, lvl)
          t
        }
        None => raise TypeError("infer: unbound variable: \{name}")
      }
    Lam(params, body) => {
      let param_arr = params.map(fn(_) { create_tvar(lvl) })
      let env_prim = params.foldi(init=env, fn(index, env_acc, param) {
        env_acc.add(param, param_arr[index])
      })
      let ret = infer!(body, lvl, env_prim)
      TArr(param_arr, ret)
    }
    Call(f, args) => {
      let f_ty = infer!(f, lvl, env)
      let (param_arr, ret) = match_fun!(f_ty, args.length())
      for i in 0..<args.length() {
        let arg_ty = infer!(args[i], lvl, env)
        param_arr[i].unify!(arg_ty)
      }
      ret
    }
    Let(name, e1, e2) => {
      let t1 = infer!(e1, lvl.enter(), env)
      let t1_gen = t1.generalize(lvl)
      let env_prim = env.add(name, t1_gen)
      infer!(e2, lvl, env_prim)
    }
    RecordEmpty => TRecord(REmpty)
    RecordSelect(exp, label) => {
      let rest_ty = create_rvar(lvl)
      let field_ty = create_tvar(lvl)
      let rec_ty = TRecord(RExtend(label, field_ty, rest_ty))
      let exp_ty = infer!(exp, lvl, env)
      exp_ty.unify!(rec_ty)
      field_ty
    }
    RecordRestrict(exp, label) => {
      let rest_ty = create_rvar(lvl)
      let field_ty = create_tvar(lvl)
      let param_ty = TRecord(RExtend(label, field_ty, rest_ty))
      let exp_ty = infer!(exp, lvl, env)
      param_ty.unify!(exp_ty)
      TRecord(rest_ty)
    }
    RecordExtend(label, exp, rest_exp) => {
      let field_ty = create_tvar(lvl)
      let rest_ty = create_rvar(lvl)
      let old_row = TRecord(rest_ty)
      let ret_ty = TRecord(RExtend(label, field_ty, rest_ty))
      old_row.unify!(infer!(rest_exp, lvl, env))
      field_ty.unify!(infer!(exp, lvl, env))
      ret_ty
    }
  }
}
