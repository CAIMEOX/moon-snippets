///| Hindley Milner Type Inference with Levels

///|
let name_counter : Ref[Int] = @ref.new(0)

///|
fn create_tvar(lvl : Level) -> Type {
  name_counter.update(fn(x) { x + 1 })
  TVar({ val: Unbound(name_counter.val, lvl) })
}

///|
suberror TypeError String

///|
fn occurs(self : Type, tv_id : Int, lvl : Level) -> Unit raise TypeError {
  fn go(x) -> Unit raise TypeError {
    match x {
      TConst(_) => ()
      TApp(t1, rets) => {
        go(t1)
        rets.each(go)
      }
      TArr(args, ret) => {
        args.each(go)
        go(ret)
      }
      TVar({ val: Link(t) }) => t.occurs(tv_id, lvl)
      TVar({ val: Generic(_) }) =>
        raise TypeError("occurs: unexpected generic type variable")
      TVar({ val: Unbound(other_tv_id, other_lvl) } as otv) => {
        guard tv_id != other_tv_id else {
          raise TypeError("occurs: recursive type")
        }
        otv.val = Unbound(other_tv_id, @math.minimum(lvl, other_lvl))
      }
    }
  }

  go(self)
}

///|
fn unify(self : Type, other : Type) -> Unit raise TypeError {
  match (self, other) {
    (TConst(x), TConst(y)) if x == y => ()
    (TArr(ls1, t1), TArr(ls2, t2)) | (TApp(t1, ls1), TApp(t2, ls2)) =>
      if ls1.length() != ls2.length() {
        raise TypeError("unify: functions have different arity")
      } else {
        ls1.zip(ls2).each(ls => ls.0.unify(ls.1))
        t1.unify(t2)
      }
    (TVar({ val: Link(t1) }), TVar({ val: Link(t2) })) => t1.unify(t2)
    (TVar({ val: Unbound(id, level) } as v), ty)
    | (ty, TVar({ val: Unbound(id, level) } as v)) => {
      ty.occurs(id, level)
      v.val = Link(ty)
    }
    (x, y) => raise TypeError("unify: can not unify \{x} with \{y}")
  }
}

///|
fn generalize(self : Type, lvl : Level) -> Type {
  match self {
    TVar({ val: Unbound(id, other_lvl) }) if other_lvl > lvl =>
      TVar({ val: Generic(id) })
    TVar({ val: Unbound(_, _) }) => self
    TApp(t, args) => TApp(t.generalize(lvl), args.map(_.generalize(lvl)))
    TArr(args, ret) => TArr(args.map(_.generalize(lvl)), ret.generalize(lvl))
    TVar({ val: Link(t) }) => t.generalize(lvl)
    _ => self
  }
}

///|
fn instantiate(self : Type, lvl : Level) -> Type {
  let tracking = Map::new()
  fn go(x) -> Type {
    match x {
      TVar({ val: Generic(id) }) if tracking.get(id) is Some(x) => x
      TVar({ val: Generic(id) }) => {
        let tvar = create_tvar(lvl)
        tracking[id] = tvar
        tvar
      }
      TApp(t, args) => TApp(go(t), args.map(go))
      TArr(args, ret) => TArr(args.map(go), go(ret))
      TVar({ val: Link(t) }) => go(t)
      _ => x
    }
  }

  go(self)
}

///|
fn match_fun(
  self : Type,
  param_num : Int
) -> (Array[Type], Type) raise TypeError {
  match self {
    TVar({ val: Link(t) }) => t.match_fun(param_num)
    TVar({ val: Unbound(_, lvl) } as tvar) => {
      let vars = Array::makei(param_num, fn(_) { create_tvar(lvl) })
      let ret = create_tvar(lvl)
      tvar.val = Link(TArr(vars, ret))
      (vars, ret)
    }
    TArr(params, _) if params.length() != param_num =>
      raise TypeError("match_fun: function has different arity")
    TArr(params, ret) => (params, ret)
    _ => raise TypeError("match_fun: not a function type")
  }
}

///|
pub fn infer(
  self : Expr,
  lvl : Level,
  env : @moonbitlang/core/immut/hashmap.T[String, Type]
) -> Type raise TypeError {
  match self {
    Var(name) =>
      match env.get(name) {
        Some(x) => x.instantiate(lvl)
        None => raise TypeError("infer: unbound variable: \{name}")
      }
    Lam(params, body) => {
      let param_arr = params.map(fn(_) { create_tvar(lvl) })
      let env_prim = params.foldi(init=env, fn(index, env_acc, param) {
        env_acc.add(param, param_arr[index])
      })
      TArr(param_arr, body.infer(lvl, env_prim))
    }
    Call(f, args) => {
      let f_ty = f.infer(lvl, env)
      let (param_arr, ret) = f_ty.match_fun(args.length())
      args.zip(param_arr).each(fn(ap) { ap.0.infer(lvl, env).unify(ap.1) })
      ret
    }
    Let(name, e1, e2) => {
      let t1 = e1.infer(lvl.enter(), env)
      let t1_gen = t1.generalize(lvl)
      let env_prim = env.add(name, t1_gen)
      e2.infer(lvl, env_prim)
    }
  }
}
