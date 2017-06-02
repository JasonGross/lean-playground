set_option profiler true
def some_lets : ℕ → ℕ → ℕ
| 0            v := v
| (nat.succ n) v := let k := some_lets n v + some_lets n v in some_lets n k

def some_unfolded_lets (n : ℕ) : Σ' v : ℕ , v = some_lets 5 n :=
begin
  constructor; unfold some_lets; constructor
end

universe variables u v
inductive let_inM : Sort u → Sort (u+1)
| ret : Π {A : Sort u} , A → let_inM A
| bind : Π {A : Sort u} {B : Sort u} , let_inM A → (A → let_inM B) → let_inM B
| app2 : Π {A B C : Sort u} , (A → B → C) → let_inM A → let_inM B → let_inM C

def denote_let_inM : Π {A : Sort (u+1)} , let_inM A → A
| A (@let_inM.ret ._ v) := v
| B (@let_inM.bind A ._ v f) := let v' := @denote_let_inM A v in @denote_let_inM B (f v')
| C (@let_inM.app2 A B ._ f x y) := f (denote_let_inM x) (denote_let_inM y)
attribute [simp] denote_let_inM

def under_lets : Π {A B : Sort (u+1)} , let_inM A → (A → let_inM B) → let_inM B
| A B (@let_inM.ret ._ v) f := let_inM.bind (let_inM.ret v) f
| A B (@let_inM.bind A2 ._ v g) f := under_lets v (λ v' , under_lets (g v') f)
| A B (@let_inM.app2 A2 B2 ._ g x y) f := under_lets x (λ x' , under_lets y (λ y' , f (g x' y')))
attribute [simp] under_lets

def lift_lets : Π {A : Sort (u+1)} , let_inM A → let_inM A :=
  λ A v , @under_lets A A v (@let_inM.ret _)

lemma denote_under_lets_correct {A : Sort (u+1)} {B : Sort (u+1)} (v : let_inM A)
 : ∀ (f : A → let_inM B), @denote_let_inM B (@under_lets A B v f) = @denote_let_inM B (f (@denote_let_inM A v)) :=
begin
  induction v; intro f; try { reflexivity }; simp; rewrite ih_1; rewrite ih_2
end
lemma lift_lets_correct {A : Sort (u+1)} (v : let_inM A)
 : denote_let_inM v = denote_let_inM (lift_lets v)
:= by symmetry; apply denote_under_lets_correct

meta def reify_to_let_in_pexpr_aux : expr → (pexpr → pexpr) → pexpr
| (expr.elet n ty val body) f := let val' := reify_to_let_in_pexpr_aux val (λ x, ``(@let_inM.ret _ %%x)) in
                                 let body' := reify_to_let_in_pexpr_aux body f in
                                 let body' := expr.lam n binder_info.default (pexpr.of_expr ty) body' in
                                 ``(@let_inM.bind %%ty _ %%val' %%body')
| `(%%a + %%b) f := let a' := reify_to_let_in_pexpr_aux a (λ x, ``(@let_inM.ret _ %%x)) in
                    let b' := reify_to_let_in_pexpr_aux b (λ x, ``(@let_inM.ret _ %%x)) in
                    ``(@let_inM.app2 _ _ _ (λ a' b' , a' + b') %%a' %%b')
| e f := f (pexpr.of_expr e)

meta def reify_to_let_in_pexpr (e : expr) : pexpr := reify_to_let_in_pexpr_aux e (λ x , ``(@let_inM.ret _ %%x))


meta def is_eq : expr → option (expr × expr × expr)
| `(@eq %%α %%a %%b) := some (α, a, b)
| _                  := none

open tactic
meta def unify_reify_rhs_to_let_in : tactic unit :=
  do [g] <- tactic.get_goals,
     gl_ty <- tactic.infer_type g,
     match is_eq gl_ty with
     | some (ty, ev, v)
        := let v' := reify_to_let_in_pexpr v in
           let v' := ``(denote_let_inM %%v') in
           do _ <- tactic.refine ``(@eq.trans _ _ %%v' _ _ (eq.refl _)),
              (g0 :: g :: []) <- tactic.get_goals,
              tactic.set_goals [g]
     | none := tactic.fail "not an equality"
     end

-- set_option debugger true
open tactic
def some_lifted_lets (n : ℕ) : Σ' (v : ℕ), v = psigma.fst (some_unfolded_lets n) :=
begin
  constructor; unfold some_unfolded_lets psigma.fst; symmetry; transitivity; symmetry,
  {
    unify_reify_rhs_to_let_in; symmetry; to_expr ``(lift_lets_correct) >>= apply
  },
  {
     symmetry; transitivity; symmetry,
     {
       unfold lift_lets under_lets; constructor
      },
     { unfold denote_let_inM; constructor }
  }

end




-- #print some_unfolded_lets
/-
#print reify_to_let_in_pexpr
#print expr
#print let_inM
#print binder_info-/
-- #print some_unfolded_lets
