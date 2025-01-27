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
type! TypeError String

///|
fn occurs(self : Type, tv_id : Int, lvl : Level) -> Unit!TypeError {
  fn go(x) -> Unit!TypeError {
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
      TVar({ val: Link(t) }) => occurs!(t, tv_id, lvl)
      TVar({ val: Generic(_) }) =>
        raise TypeError("occurs: unexpected generic type variable")
      TVar({ val: Unbound(other_tv_id, other_lvl) } as otv) =>
        if tv_id != other_tv_id {
          let lvl = @math.minimum(lvl, other_lvl)
          otv.val = Unbound(other_tv_id, lvl)
        } else {
          raise TypeError("occurs: recursive type")
        }
    }
  }

  go!(self)
}

///|
fn unify(self : Type, other : Type) -> Unit!TypeError {
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
          unify!(ls1[i], ls2[i])
        }
        unify!(r1, r2)
      }
    (TApp(t1, args1), TApp(t2, args2)) =>
      if args1.length() != args2.length() {
        raise TypeError("unify: type constructors have different arity")
      } else {
        unify!(t1, t2)
        for i in 0..<args1.length() {
          unify!(args1[i], args2[i])
        }
      }
    (TVar({ val: Link(t1) }), TVar({ val: Link(t2) })) => unify!(t1, t2)
    (TVar({ val: Unbound(id, level) } as v), ty)
    | (ty, TVar({ val: Unbound(id, level) } as v)) => {
      occurs!(ty, id, level)
      v.val = Link(ty)
    }
    (x, y) => raise TypeError("unify: can not unify \{x} with \{y}")
  }
}

///|
fn generalize(self : Type, lvl : Level) -> Type {
  match self {
    TVar({ val: Unbound(id, other_lvl) }) =>
      if other_lvl > lvl {
        TVar({ val: Generic(id) })
      } else {
        self
      }
    TApp(t, args) =>
      TApp(generalize(t, lvl), args.map(fn { x => generalize(x, lvl) }))
    TArr(args, ret) =>
      TArr(args.map(fn { x => generalize(x, lvl) }), generalize(ret, lvl))
    TVar({ val: Link(t) }) => generalize(t, lvl)
    _ => self
  }
}

///|
fn instantiate(self : Type, lvl : Level) -> Type {
  let tracking = Map::new()
  fn go(x) -> Type {
    match x {
      TVar({ val: Generic(id) }) =>
        match tracking[id] {
          Some(x) => x
          None => {
            let tvar = create_tvar(lvl)
            tracking[id] = tvar
            tvar
          }
        }
      TApp(t, args) => TApp(go(t), args.map(fn { x => go(x) }))
      TArr(args, ret) => TArr(args.map(fn { x => go(x) }), go(ret))
      TVar({ val: Link(t) }) => go(t)
      _ => x
    }
  }

  go(self)
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
  env : @moonbitlang/core/immut/hashmap.T[String, Type]
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
        unify!(param_arr[i], arg_ty)
      }
      ret
    }
    Let(name, e1, e2) => {
      let t1 = infer!(e1, lvl.enter(), env)
      let t1_gen = generalize(t1, lvl)
      let env_prim = env.add(name, t1_gen)
      infer!(e2, lvl, env_prim)
    }
  }
}
