/// Hindley Milner Type Inference with Levels
/// 
/// This implements the Hindley-Milner type inference algorithm with an important
/// optimization called "levels".
/// 
/// The level-based approach ensures that we only generalize type variables that
/// are truly polymorphic, avoiding the inefficiencies of other approaches.

/// Global counter for generating unique type variable IDs.
/// Each type variable gets a fresh ID to distinguish it from others.
let name_counter : Ref[Int] = @ref.new(0)

/// Create a fresh unbound type variable at the given level.
/// 
/// This is how we introduce new "unknowns" in the type system.
/// Each variable has:
/// - A unique ID (from the global counter)
/// - A level (the nesting depth where it was created)
/// 
/// Example: When we see "λx. x", we create a fresh type variable for x's type.
fn create_tvar(lvl : Level) -> Type {
  name_counter.update(fn(x) { x + 1 })
  TVar({ val: Unbound(name_counter.val, lvl) })
}

/// Exception type for type errors during inference.
/// This allows us to report meaningful error messages when type checking fails.
suberror TypeError String

/// The "occurs check" prevents infinite recursive types.
/// 
/// This checks if a type variable occurs within a type it's being unified with.
/// Without this check, we could create impossible types like "X = X -> Int"
/// which would represent a function that takes itself as an argument.
/// 
/// The function also performs level adjustment as an optimization:
/// when we find a type variable at a deeper level, we "promote" it to the
/// shallower level to enable more generalization opportunities.
/// 
/// Example: Unifying "X" with "X -> Int" should fail (infinite type)
/// Example: Unifying "X" with "Int -> Y" should succeed
fn occurs(self : Type, tv_id : Int, lvl : Level) -> Unit raise TypeError {
  fn go(x) -> Unit raise TypeError {
    match x {
      // Base types can't contain the type variable we're looking for
      TConst(_) => ()
      // Recursively check type applications and their arguments
      TApp(t1, rets) => {
        go(t1)
        rets.each(go)
      }
      // Recursively check function arguments and return type
      TArr(args, ret) => {
        args.each(go)
        go(ret)
      }
      // Follow the link and check the target type
      TVar({ val: Link(t) }) => t.occurs(tv_id, lvl)
      // Generic variables shouldn't appear during occurs check
      TVar({ val: Generic(_) }) =>
        raise TypeError("occurs: unexpected generic type variable")
      // Check if this is the same variable (occurs check failure)
      // Otherwise, adjust the level for better generalization
      TVar({ val: Unbound(other_tv_id, other_lvl) } as otv) => {
        guard tv_id != other_tv_id else {
          raise TypeError("occurs: recursive type")
        }
        // Level adjustment: promote the variable to the minimum level
        // This allows more variables to be generalized later
        otv.val = Unbound(other_tv_id, @cmp.minimum(lvl, other_lvl))
      }
    }
  }

  go(self)
}

/// Unification is the heart of type inference.
/// 
/// It finds the most general type that satisfies the constraint that two types
/// must be the same. This works by:
/// 1. If both types are the same constant, we're done
/// 2. If they're both functions/applications, unify their parts recursively
/// 3. If one is a type variable, bind it to the other type (after occurs check)
/// 4. Otherwise, the types are incompatible
/// 
/// Example: Unifying "X -> Y" with "Int -> Bool" 
/// results in X = Int, Y = Bool
fn unify(self : Type, other : Type) -> Unit raise TypeError {
  match (self, other) {
    // Same constants unify trivially
    (TConst(x), TConst(y)) if x == y => ()
    // Functions and type applications: check arity then unify components
    (TArr(ls1, t1), TArr(ls2, t2)) | (TApp(t1, ls1), TApp(t2, ls2)) =>
      if ls1.length() != ls2.length() {
        raise TypeError("unify: type constructor have different arity")
      } else {
        // Unify corresponding arguments/parameters
        ls1.zip(ls2).each(ls => ls.0.unify(ls.1))
        // Unify the result/base types
        t1.unify(t2)
      }
    // Both are linked variables: unify their targets
    (TVar({ val: Link(t1) }), TVar({ val: Link(t2) })) => t1.unify(t2)
    // One is unbound variable: bind it to the other type (occurs check first)
    (TVar({ val: Unbound(id, level) } as v), ty)
    | (ty, TVar({ val: Unbound(id, level) } as v)) => {
      ty.occurs(id, level)
      v.val = Link(ty)
    }
    // Types are fundamentally incompatible
    (x, y) => raise TypeError("unify: can not unify \{x} with \{y}")
  }
}

/// Generalization converts unbound type variables to generic ones.
/// 
/// This is the key to polymorphism! When we finish inferring the type of a
/// let-bound expression, we generalize any type variables that were created
/// at a deeper level than the current one. This makes them "forall" variables.
/// 
/// The level check is crucial: we only generalize variables that are "local"
/// to the current let-expression. Variables from outer scopes should **not**
/// be generalized because they might still be constrained by outer contexts.
/// 
/// Example: In "let id = λx.x in ...", the type variable for x becomes
/// generalized to "forall a. a -> a"
fn generalize(self : Type, lvl : Level) -> Type {
  match self {
    // Unbound variable at a deeper level: generalize it
    TVar({ val: Unbound(id, other_lvl) }) if other_lvl > lvl =>
      TVar({ val: Generic(id) })
    // Unbound variable at current/shallower level: keep as is
    TVar({ val: Unbound(_, _) }) => self
    // Recursively generalize type applications and functions
    TApp(t, args) => TApp(t.generalize(lvl), args.map(_.generalize(lvl)))
    TArr(args, ret) => TArr(args.map(_.generalize(lvl)), ret.generalize(lvl))
    // Follow links and generalize the target
    TVar({ val: Link(t) }) => t.generalize(lvl)
    // Constants and already-generic variables stay unchanged
    _ => self
  }
}

/// Instantiation creates fresh copies of polymorphic types.
/// 
/// When we use a polymorphic value (like a function with type "forall a. a -> a"),
/// we need to create fresh type variables for each use. This prevents different
/// uses from interfering with each other.
/// 
/// Example: If we have "let id = λx.x in (id 5, id true)", we need to instantiate
/// the type of "id" twice: once as "Int -> Int" and once as "Bool -> Bool".
/// 
/// The tracking map ensures that the same generic variable gets the same
/// fresh variable within a single instantiation.
fn instantiate(self : Type, lvl : Level) -> Type {
  // Map from generic variable IDs to their fresh instantiations
  let tracking = Map::new()
  fn go(x) -> Type {
    match x {
      // Already seen this generic variable: reuse the same fresh variable
      TVar({ val: Generic(id) }) if tracking.get(id) is Some(x) => x
      // New generic variable: create a fresh unbound variable
      TVar({ val: Generic(id) }) => {
        let tvar = create_tvar(lvl)
        tracking[id] = tvar
        tvar
      }
      // Recursively instantiate type applications and functions
      TApp(t, args) => TApp(go(t), args.map(go))
      TArr(args, ret) => TArr(args.map(go), go(ret))
      // Follow links and instantiate the target
      TVar({ val: Link(t) }) => go(t)
      // Everything else remains unchanged
      _ => x
    }
  }

  go(self)
}

/// Extract function parameter and return types from a type.
/// 
/// This handles the case where we're calling something that might not
/// obviously be a function. If it's a type variable, we assume it's a
/// function and create fresh type variables for its parameters and return type.
/// 
/// This is how we can infer that "f x" means f must be a function type,
/// even if we don't know what f is yet.
/// 
/// Example: Calling an unknown "f" with 2 arguments creates the constraint
/// that f must have type "X -> Y -> Z" for some X, Y, Z.
fn match_fun(
  self : Type,
  param_num : Int
) -> (Array[Type], Type) raise TypeError {
  match self {
    // Follow links to the actual type
    TVar({ val: Link(t) }) => t.match_fun(param_num)
    // Unknown type variable: assume it's a function and create constraints
    TVar({ val: Unbound(_, lvl) } as tvar) => {
      let vars = Array::makei(param_num, fn(_) { create_tvar(lvl) })
      let ret = create_tvar(lvl)
      // Bind the type variable to be a function type
      tvar.val = Link(TArr(vars, ret))
      (vars, ret)
    }
    // Known function with wrong arity
    TArr(params, _) if params.length() != param_num =>
      raise TypeError("match_fun: function has different arity")
    // Known function with correct arity
    TArr(params, ret) => (params, ret)
    // Not a function type at all
    _ => raise TypeError("match_fun: not a function type")
  }
}

/// The main type inference algorithm.
/// 
/// The level parameter tracks let-nesting depth for proper generalization.
/// The environment maps variable names to their (possibly polymorphic) types.
pub fn infer(
  self : Expr,
  lvl : Level,
  env : @moonbitlang/core/immut/hashmap.T[String, Type]
) -> Type raise TypeError {
  match self {
    // Variable reference: look up in environment
    Var(name) =>
      match env.get(name) {
        // Found: instantiate to get fresh copy of polymorphic type
        Some(x) => x.instantiate(lvl)
        // Not found: unbound variable error
        None => raise TypeError("infer: unbound variable: \{name}")
      }
    // Lambda abstraction: create function type
    Lam(params, body) => {
      // Create fresh type variables for each parameter
      let param_arr = params.map(fn(_) { create_tvar(lvl) })
      // Extend environment with parameter bindings
      let env_prim = params.foldi(init=env, fn(index, env_acc, param) {
        env_acc.add(param, param_arr[index])
      })
      // Infer body type in extended environment
      TArr(param_arr, body.infer(lvl, env_prim))
    }
    // Function application: infer function, match against arguments
    Call(f, args) => {
      let f_ty = f.infer(lvl, env)
      // Extract parameter types and return type from function (and match shape / arity)
      let (param_arr, ret) = f_ty.match_fun(args.length())
      // Unify each argument with its expected parameter type
      args.zip(param_arr).each(fn(ap) { ap.0.infer(lvl, env).unify(ap.1) })
      ret
    }
    // Let binding: the heart of polymorphism
    Let(name, e1, e2) => {
      // Infer type of bound expression at deeper level
      let t1 = e1.infer(lvl.enter(), env)
      // Generalize any type variables created at the deeper level
      let t1_gen = t1.generalize(lvl)
      // Add generalized type to environment
      let env_prim = env.add(name, t1_gen)
      // Infer type of continuation in extended environment
      e2.infer(lvl, env_prim)
    }
  }
}
