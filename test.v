Definition Let_In {A B} (v : A) (f : A -> B) := let v' := v in f v'.
Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).
Fixpoint some_lets (n : nat) (v : nat) : nat :=
  match n with
  | 0 => v
  | S n' => dlet k := some_lets n' v + some_lets n' v in some_lets n' k
  end.

Definition some_unfolded_lets (n : nat) : { v : nat | v = some_lets 6 n }.
Proof.
  econstructor; cbv beta iota delta [some_lets]; constructor.
Defined.

Inductive let_inM : Type -> Type :=
| ret {A : Type} : A -> let_inM A
| bind {A : Type} {B : Type} : let_inM A -> (A -> let_inM B) -> let_inM B
| app2 {A B C : Type} : (A -> B -> C) -> let_inM A -> let_inM B -> let_inM C.

Fixpoint denote_let_inM {A : Type} (v : let_inM A) : A
  := match v with
     | ret v => v
     | bind v f => (dlet v' := denote_let_inM v in denote_let_inM (f v'))
     | app2 f x y => f (denote_let_inM x) (denote_let_inM y)
     end.

Fixpoint under_lets {A B : Type} (v : let_inM A) : (A -> let_inM B) -> let_inM B
  := match v with
     | ret v => fun f => bind (ret v) f
     | bind v g => fun f => under_lets v (fun v' => under_lets (g v') f)
     | app2 g x y => fun f => under_lets x (fun x' => under_lets y (fun y' => f (g x' y')))
     end.

Definition lift_lets : forall {A : Type} , let_inM A -> let_inM A :=
  fun A v => @under_lets A A v (@ret _).

Lemma denote_under_lets_correct {A : Type} {B : Type} (v : let_inM A)
  : forall (f : A -> let_inM B), @denote_let_inM B (@under_lets A B v f) = @denote_let_inM B (f (@denote_let_inM A v)).
Proof.
  induction v; intro f; try reflexivity; simpl; unfold Let_In; simpl; rewrite ?IHv, ?IHv1, ?IHv2, ?H; try reflexivity.
Qed.
Definition lift_lets_correct {A : Type} (v : let_inM A)
  : denote_let_inM v = denote_let_inM (lift_lets v).
Proof. symmetry; apply @denote_under_lets_correct. Qed.

Ltac reify_to_let_in_pexpr e :=
  lazymatch e with
  | (dlet n : ?T := ?val in ?body)
    => let val' := reify_to_let_in_pexpr val in
       let n' := fresh n in
       let n' := fresh n' in
       let n' := fresh n' in
       let n' := fresh n' in
       let body' := constr:(fun n : T => match body with
                                         | n' => ltac:(let n'' := (eval cbv delta [n'] in n') in
                                                       let ret := reify_to_let_in_pexpr n'' in
                                                       exact ret)
                                         end) in
       constr:(bind val' body')
  | (?a + ?b)%nat
    => let a' := reify_to_let_in_pexpr a in
       let b' := reify_to_let_in_pexpr b in
       constr:(app2 Nat.add a' b')
  | ?v => constr:(ret v)
  end.

Ltac unify_reify_rhs_to_let_in :=
  lazymatch goal with
  | [ |- ?ev = ?v :> ?ty ]
    => let v' := reify_to_let_in_pexpr v in
       let v' := constr:(denote_let_inM v') in
       refine (@eq_trans _ _ v' _ _ _); [ | abstract (cbv [denote_let_inM]; reflexivity) ]
  end.

Ltac vm_compute_rhs :=
  lazymatch goal with
  | [ |- ?ev = ?rhs ]
    => let rhs := match (eval pattern Nat.add in rhs) with ?rhs _ => rhs end in
       let rhs' := (eval vm_compute in rhs) in
       unify ev (rhs' Nat.add);
       abstract (exact_no_check (f_equal (fun f => f Nat.add) (eq_refl rhs' <: rhs' = rhs)))
  end.

Definition some_lifted_lets (n : nat) : { v : nat | v = proj1_sig (some_unfolded_lets n) }.
Proof.
  Time
    econstructor; unfold some_unfolded_lets, proj1_sig; symmetry; etransitivity; symmetry;
    [ unify_reify_rhs_to_let_in; symmetry; apply lift_lets_correct
    | symmetry; etransitivity; symmetry;
        [ apply f_equal; vm_compute_rhs
        | cbv [denote_let_inM]; reflexivity ] ].
Defined.
