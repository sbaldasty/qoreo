From Stdlib Require Import FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Qoreo Require Import Base.
Import Var.Map.Tactics.


Open Scope qoreo.

Inductive t :=
| Var : Var.t -> t
| LetIn : Var.t -> t -> t -> t
| Bang : t -> t
| LetBang : Var.t -> t -> t -> t
| Bit : bool -> t
| If : t -> t -> t -> t
| Pair : t -> t -> t
| LetPair : Var.t -> Var.t -> t -> t -> t
| Meas : t -> t
| QRef : Var.t -> t
| New : t -> t
| Unitary : unitary -> t -> t
| Lambda : Var.t -> t -> t
| Fix : Var.t -> Var.t -> t -> t
| App : t -> t -> t
.

Inductive Val : t -> Prop :=
| QRefVal : forall q,
  Val (QRef q)
(*| VarVal : forall x, Val x*)
| BangVal : forall e,
  Val (Bang e)
| BitVal  : forall b,
  Val (Bit b)
| PairVal : forall v1 v2,
  Val v1 -> Val v2 ->
  Val (Pair v1 v2)
| LambdaVal : forall x e,
  Val (Lambda x e)
| FixVal    : forall f x e,
  Val (Fix f x e)
.
#[global] Hint Constructors Val : var_db.

(*************************)
(* Operational Semantics *)
(*************************)

Inductive Fresh x : Expr.t -> Prop :=
| FVar : forall y, ~ Var.V.eq x y -> Fresh x (Var y)
| FLetIn : forall y e1 e2,
  Fresh x e1 ->
  ~ Var.V.eq x y ->
  Fresh x e2 ->
  Fresh x (LetIn y e1 e2)
| FBang : forall e, Fresh x e -> Fresh x (Bang e)
| FLetBang : forall y e1 e2,
  Fresh x e1 ->
  ~ Var.V.eq x y ->
  Fresh x e2 ->
  Fresh x (LetBang y e1 e2)
| FBit : forall b, Fresh x (Bit b)
| FIf : forall e e1 e2,
  Fresh x e -> Fresh x e1 -> Fresh x e2 ->
  Fresh x (If e e1 e2)
| FPair : forall e1 e2,
  Fresh x e1 -> Fresh x e2 ->
  Fresh x (Pair e1 e2)
| FLetPair : forall y1 y2 e1 e2,
  Fresh x e1 ->
  ~ Var.V.eq x y1 ->
  ~ Var.V.eq x y2 ->
  Fresh x e2 ->
  Fresh x (LetPair y1 y2 e1 e2)
| FMeas : forall e, Fresh x e -> Fresh x (Meas e)
| FQRef : forall q, Fresh x (QRef q)
| FNew : forall e, Fresh x e -> Fresh x (New e)
| FUnitary : forall u e, Fresh x e -> Fresh x (Unitary u e)
| FLambda : forall y e,
  ~ Var.V.eq x y ->
  Fresh x e ->
  Fresh x (Lambda y e)
| FFix : forall f y e,
  ~ Var.V.eq x f ->
  ~ Var.V.eq x y ->
  Fresh x e ->
  Fresh x (Fix f y e)
| FApp : forall e1 e2,
  Fresh x e1 -> Fresh x e2 ->
  Fresh x (App e1 e2)
.

(* Assume x is fresh in e, and v is closed *)
Fixpoint subst x v e :=
  match e with
  | Var y => if Var.eq_dec x y then v else Var y
  | LetIn y e1 e2 =>
    LetIn y (subst x v e1) (if Var.eq_dec x y then e2 else subst x v e2)
  | Bang e => Bang (subst x v e)
  | LetBang y e1 e2 =>
    LetBang y (subst x v e1) (if Var.eq_dec x y then e2 else subst x v e2)
  | Bit b => Bit b
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | LetPair y1 y2 e1 e2 =>
    LetPair y1 y2 (subst x v e1)
      (if Var.eq_dec x y1 then e2
       else if Var.eq_dec x y2 then e2
       else subst x v e2)
  | Meas e => Meas (subst x v e)
  | QRef q => QRef q
  | New e => New (subst x v e)
  | Unitary u e => Unitary u (subst x v e)
  | Lambda y e =>
    Lambda y (if Var.eq_dec x y then e else subst x v e)
  | Fix f y e =>
    Fix f y (if Var.eq_dec x f then e
             else if Var.eq_dec x y then e
             else subst x v e)
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  end.



Inductive step : Expr.t -> Var.Map.t nat -> Config.t -> Expr.t -> Var.Map.t nat -> Config.t -> Prop :=

(* Let *)
| LetC :
  forall x e1 e2 refs cfg e1' refs' cfg',
  
  step e1 refs cfg e1' refs' cfg' ->
  step (LetIn x e1 e2) refs cfg (LetIn x e1' e2) refs' cfg'

| LetB : forall x v1 e2 refs cfg e2',
  Val v1 ->
  e2' = subst x v1 e2 ->
  step (LetIn x v1 e2) refs cfg e2' refs cfg

(* Bang *)
(* no reduction under Bang *)

(* LetBang *)
| LetBangC :
  forall x e1 e2 refs cfg e1' refs' cfg',

  step e1 refs cfg e1' refs' cfg' ->

  step (LetBang x e1  e2) refs cfg
       (LetBang x e1' e2) refs' cfg'

| LetBangB : forall x e1 e2 refs cfg e2',
  e2' = subst x e1 e2 ->

  step (LetBang x (Bang e1) e2) refs cfg
       e2' refs cfg

(* If *)
| IfC : forall e1 e2 e3 refs cfg e1' refs' cfg',
  step e1 refs cfg e1' refs' cfg' ->

  step (If e1  e2 e3) refs cfg
       (If e1' e2 e3) refs' cfg'
  

| IfB : forall (b : bool) e2 e3 refs cfg e',

  (e' = if b then e2 else e3) ->
  
  step (If (Bit b) e2 e3) refs cfg
       e' refs cfg

(* Pair *)
| PairC1 : forall e1 e2 refs cfg e1' refs' cfg',
  step e1 refs cfg e1' refs' cfg' ->

  step (Pair e1 e2) refs cfg (Pair e1' e2) refs' cfg'

| PairC2 : forall e1 e2 refs cfg e2' refs' cfg',

  Val e1 ->
  step e2 refs cfg e2' refs' cfg' ->

  step (Pair e1 e2) refs cfg (Pair e1 e2') refs' cfg'

(* LetPair *)
| LetPairC : forall x1 x2 e1 e2 refs cfg e1' refs' cfg',

  step e1 refs cfg e1' refs' cfg' ->

  step (LetPair x1 x2 e1 e2) refs cfg
       (LetPair x1 x2 e1' e2) refs' cfg'

| LetPairB : forall x1 x2 v1 v2 e' refs cfg e'',
  Val (Pair v1 v2) ->
  e'' = subst x2 v2 (subst x1 v1 e') ->

  step (LetPair x1 x2 (Pair v1 v2) e') refs cfg 
        e'' refs cfg

| AppC1 : forall e1 e2 refs cfg e1' refs' cfg',

  step e1 refs cfg e1' refs' cfg' ->

  step (App e1 e2) refs cfg
        (App e1' e2) refs' cfg'

| AppC2 : forall e1 e2 refs cfg e2' refs' cfg',

  Val e1 ->
  step e2 refs cfg e2' refs' cfg' ->

  step (App e1 e2) refs cfg
        (App e1 e2') refs' cfg'

| AppB : forall x e v refs cfg e',

  Val v ->
  e' = subst x v e ->

  step (App (Lambda x e) v) refs cfg
        e' refs cfg

| AppFixB : forall f x e e0 refs cfg e',

  e' = subst x e0 (subst f (Fix f x e) e) ->

  step (App (Fix f x e) (Bang e0)) refs cfg e' refs cfg

(* New *)
| NewC : forall e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (New e) refs cfg (New e') refs' cfg'

| New0 : forall b refs cfg x refs' cfg',

  (x, refs', cfg') = Config.new b refs cfg ->

  step (New (Bit b)) refs cfg
        (QRef x) refs' cfg'

(* Meas *)
| MeasC : forall e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (Meas e)  refs  cfg
       (Meas e') refs' cfg'

| MeasB : forall i b x refs cfg refs' cfg',
  Var.Map.Singleton x i refs ->
  (refs', cfg') = Config.measure b x refs cfg ->

  step (Meas (QRef x)) refs cfg (Bit b) refs' cfg'


(* Unitary *)
| UnitaryC : forall u e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (Unitary u e) refs cfg
       (Unitary u e') refs' cfg'

| UnitaryB1 : forall i g q refs cfg cfg',
  Var.Map.Singleton q i refs ->
  cfg' = Config.apply_gate g [q] refs cfg ->

  step (Unitary g (QRef q)) refs cfg
       (QRef q) refs cfg'

| UnitaryB2 : forall i1 i2 g q1 q2 refs cfg cfg',
  Var.Map.Equal refs (Var.Map.add q1 i1 (Var.Map.add q2 i2 (Var.Map.empty _))) ->
  cfg' = Config.apply_gate g [q1;q2] refs cfg ->

  step (Unitary g (Pair (QRef q1) (QRef q2))) refs cfg
       (Pair (QRef q1) (QRef q2)) refs cfg'
.


(*
Fixpoint qrefs (e : Expr.t) : Var.FSet.t :=
  match e with
  | Var _ => Var.FSet.empty
  | LetIn _ e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  | Bang e => qrefs e
  | LetBang _ e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  | Bit _ => Var.FSet.empty
  | If e e1 e2 => Var.FSet.union (Var.FSet.union (qrefs e) (qrefs e1)) (qrefs e2)
  | Pair e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  | LetPair _ _ e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  | Meas e => qrefs e
  | QRef x => Var.FSet.singleton x
  | New e => qrefs e
  | Unitary _ e => qrefs e
  | Lambda _ e => qrefs e
  | Fix _ _ e => qrefs e
  | App e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  end.
*)



(*********)
(* Types *)
(*********)

Inductive typ :=
| BIT | QUBIT
| Tensor : typ -> typ -> typ
| Lolli : typ -> typ -> typ
| BANG : typ -> typ.

Definition type_of_unitary (U : unitary) : typ :=
match U with
| CNOT => Tensor QUBIT QUBIT
| _ => QUBIT
end.


(* Typing judgment: Γ; Δ; Θ ⊢ t : τ 
 *  Γ : a finite map of non-linear variables to types
 *  Δ : a finite map of linear variables to types
 *  Θ : a finite map of qref variables to natural number indices
 *)
Inductive WellTyped : Var.Map.t typ -> Var.Map.t typ -> Var.Map.t nat -> Expr.t -> typ -> Prop :=

| WTQVar : forall Γ Δ Θ x τ,
  ~ Var.Map.In x Γ ->
  Var.Map.Singleton x τ Δ ->
  Var.Map.Empty Θ ->
  WellTyped Γ Δ Θ (Var x) τ

| WTCVar : forall Γ Δ Θ x τ,
  Var.Map.Empty Δ ->
  Var.Map.Empty Θ ->
  Var.Map.MapsTo x τ Γ ->
  WellTyped Γ Δ Θ (Var x) τ

| WTLetIn : forall Δ1 Δ2 Θ1 Θ2 τ Γ Δ Θ x e1 e2 τ',
  WellTyped Γ Δ1 Θ1 e1 τ ->

  WellTyped (Var.Map.remove x Γ) (Var.Map.add x τ Δ2) Θ2 e2 τ' ->
  
  Var.Map.Partition Δ Δ1 Δ2 ->
  ~ Var.Map.In x Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (LetIn x e1 e2) τ'

| WTBang : forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->

  Var.Map.Empty Δ ->
  Var.Map.Empty Θ ->

  WellTyped Γ Δ Θ (Bang e) (BANG τ)

| WTLetBang : forall τ Δ1 Δ2 Θ1 Θ2 Γ Δ Θ x e1 e2 τ',
  WellTyped Γ Δ1 Θ1 e1 (BANG τ) ->
  WellTyped (Var.Map.add x τ Γ) Δ2 Θ2 e2 τ' ->

  Var.Map.Partition Δ Δ1 Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->
  ~ Var.Map.In x Δ2 ->

  WellTyped Γ Δ Θ (LetBang x e1 e2) τ'

| WTBit : forall Γ Δ Θ b,
  Var.Map.Empty Δ ->
  Var.Map.Empty Θ ->
  WellTyped Γ Δ Θ (Bit b) BIT

| WTIf : forall Δ1 Δ2 Θ1 Θ2 Γ Δ Θ e eT eF τ,

  WellTyped Γ Δ1 Θ1 e BIT ->
  WellTyped Γ Δ2 Θ2 eT τ ->
  WellTyped Γ Δ2 Θ2 eF τ ->

  Var.Map.Partition Δ Δ1 Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (If e eT eF) τ

| WTPair : forall Δ1 Δ2 Θ1 Θ2 Γ Δ Θ e1 e2 τ1 τ2,
  WellTyped Γ Δ1 Θ1 e1 τ1 ->
  WellTyped Γ Δ2 Θ2 e2 τ2 ->

  Var.Map.Partition Δ Δ1 Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (Pair e1 e2) (Tensor τ1 τ2)

| WTLetPair : forall Δ1 Δ2 Θ1 Θ2 τ1 τ2 Γ Δ Θ x1 x2 e e' τ',

  WellTyped Γ Δ1 Θ1 e (Tensor τ1 τ2) ->
  WellTyped (Var.Map.remove x1 (Var.Map.remove x2 Γ))
            (Var.Map.add x1 τ1 (Var.Map.add x2 τ2 Δ2))
            Θ2 e' τ' ->
  
  Var.Map.Partition Δ Δ1 Δ2 ->
  ~ Var.Map.In x1 Δ2 ->
  ~ Var.Map.In x2 Δ2 ->
  x1 <> x2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (LetPair x1 x2 e e') τ'

| WTMeas : forall Γ Δ Θ e,
  WellTyped Γ Δ Θ e QUBIT ->
  WellTyped Γ Δ Θ (Meas e) BIT

| WTQRef : forall Γ Δ Θ q idx,

  Var.Map.Empty Δ ->
  Var.Map.Singleton q idx Θ ->

  WellTyped Γ Δ Θ (QRef q) QUBIT

| WTNew : forall Γ Δ Θ e,
  WellTyped Γ Δ Θ e BIT ->
  WellTyped Γ Δ Θ (New e) QUBIT

| WTUnitary : forall Γ Δ Θ U e τ,
  type_of_unitary U = τ ->
  WellTyped Γ Δ Θ e τ ->
  WellTyped Γ Δ Θ (Unitary U e) τ

| WTLambda : forall Γ Δ Θ x e τ1 τ2,
  ~ Var.Map.In x Δ ->
  WellTyped (Var.Map.remove x Γ) (Var.Map.add x τ1 Δ) Θ e τ2 ->
  WellTyped Γ Δ Θ (Lambda x e) (Lolli τ1 τ2)

| WTFix : forall Γ Δ Θ f x e τ1 τ2,

  WellTyped (Var.Map.add f (Lolli (BANG τ1) τ2) (Var.Map.add x τ1 Γ)) Δ Θ e τ2 ->

  Var.Map.Empty Δ ->
  Var.Map.Empty Θ  ->
  f <> x ->

  WellTyped Γ Δ Θ (Fix f x e) (Lolli (BANG τ1) τ2)

| WTApp : forall Δ1 Δ2 Θ1 Θ2 τ Γ Δ Θ e1 e2 τ',
  WellTyped Γ Δ1 Θ1 e1 (Lolli τ τ') ->
  WellTyped Γ Δ2 Θ2 e2 τ ->

  Var.Map.Partition Δ Δ1 Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (App e1 e2) τ'
.

Hint Constructors WellTyped : qoreo_db.

Definition WellTypedConfig (refs : Var.Map.t nat) e tau : Prop :=
  WellTyped (Var.Map.empty _) (Var.Map.empty _) refs e tau.


(* TODO: The stronger statement would be 
to define alpha equivalence for Expr.tessions
and then to prove this with respect to
    Var.Map.Equiv alpha_equiv
*)

Lemma WellTyped_context_equal :
  forall Γ Δ Θ e τ,
    WellTyped Γ Δ Θ e τ ->
  forall Γ' Δ' Θ',
    Var.Map.Equal Γ Γ' ->
    Var.Map.Equal Δ Δ' ->
    Var.Map.Equal Θ Θ' ->
    WellTyped Γ' Δ' Θ' e τ.
Proof.
  intros Γ Δ Θ e τ He.
  induction He; intros Γ0 Δ0 Θ0 HΓ HΔ HΘ;
    try (
      econstructor;
      try apply IHHe;
      try apply IHHe1;
      try apply IHHe2;
      try apply IHHe3;
      try rewrite <- HΔ;
      try rewrite <- HΓ;
      try rewrite <- HΘ;
      try reflexivity;
      eauto;
      fail).
Qed.


Global Instance WellTypedProper : Proper (Var.Map.Equal ==> Var.Map.Equal ==> Var.Map.Equal ==> eq ==> eq ==> iff) WellTyped.
Proof.
  intros Γ1 Γ2 HΓ
    Δ1 Δ2 HΔ
    Θ1 Θ2 HΘ
    e1 e2 He
    τ1 τ2 Hτ; subst.
  split; intros; eapply WellTyped_context_equal; eauto;
    try (symmetry; auto).
Qed.

Fixpoint vars (e : t) : Var.FSet.t :=
  match e with
  | Var x | QRef x => Var.FSet.singleton x 

  | LetIn x e1 e2 | LetBang x e1 e2 =>
    Var.FSet.add x (Var.FSet.union (vars e1) (vars e2))

  | Bit _ => Var.FSet.empty
  | Bang e | Meas e | New e | Unitary _ e =>
    vars e
  | Pair e1 e2 | App e1 e2 =>
    Var.FSet.union (vars e1) (vars e2)
  | If e0 e1 e2 =>
    Var.FSet.union (vars e0) (Var.FSet.union (vars e1) (vars e2))
  
  | LetPair x1 x2 e1 e2 =>
    Var.FSet.add x1 (Var.FSet.add x2 (Var.FSet.union (vars e1) (vars e2)))
  
  | Lambda x e' => Var.FSet.add x (vars e')
  | Fix f x e' => Var.FSet.add f (Var.FSet.add x (vars e'))
  
  end.

(***************)
(* Type safety *)
(***************)
Hint Rewrite Var.Map.Properties.F.empty_in_iff : var_db.


Lemma wt_disjoint' : forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->
  forall z, Var.Map.In z Γ -> Var.Map.In z Δ -> False.
Proof.
  intros ? ? ? ? ? HWT.
  induction HWT;
    intros z HΓ HΔ;
    vsimpl;
    autorewrite with var_db in *;
    auto;

    try (apply (IHHWT z); auto; fail);

    reflect_partition; autorewrite with var_db in *.

  * unfold Var.Map.Singleton in *.
    vsimpl.
    autorewrite with var_db in *.
    compare x z; auto. intuition.
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    compare x z.
    apply (IHHWT2 z); autorewrite with var_db;
      intuition.
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    compare x z.
    apply (IHHWT2 z); autorewrite with var_db;
      intuition.
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    { apply (IHHWT2 z); auto. }
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    { apply (IHHWT2 z); auto. }
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    compare x1 z.
    compare x2 z.
    apply (IHHWT2 z); autorewrite with var_db;
      intuition.
  * compare x z.
    apply (IHHWT z); autorewrite with var_db; intuition.
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    { apply (IHHWT2 z); auto. }
Qed.

Lemma wt_disjoint : forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->
  Var.Map.Properties.Disjoint Γ Δ.
Proof.
  intros ? ? ? ? ? HWT z [HΓ HΔ].
  eapply wt_disjoint'; eauto.
Qed.

Lemma weakening1 : forall e Γ Δ Θ τ,
  WellTyped Γ Δ Θ e τ ->
  forall x0 τ0,
  ~ Var.Map.In x0 Γ ->
  ~ Var.Map.In x0 Δ ->
  WellTyped (Var.Map.add x0 τ0 Γ) Δ Θ e τ.
Proof.
  intros ? ? ? ? ? HWT;
    induction HWT;
    intros z α HΓ HΔ (*HΘ*);
    vsimpl; autorewrite with var_db in *;

    reflect_partition;
    autorewrite with var_db in *;
    repeat match goal with
    | [H : ~ (_ \/ _) |- _ ] =>
      apply Decidable.not_or in H;
      destruct H
    end;

    try (econstructor; eauto with var_db; 
          try Var.Map.Tactics.partition_concat;
          fail).
  * econstructor; eauto with var_db.
    unfold Var.Map.Singleton in *.
    vsimpl.
    autorewrite with var_db in *.
    intuition.
  * eapply WTCVar; eauto with var_db.
    assert (x <> z).
    {
      inversion 1; subst.
      apply HΓ.
      exists τ; auto.
    }
    autorewrite with var_db.
    auto.
  * (* LetIn *)
    econstructor; eauto;
      try Var.Map.Tactics.partition_concat.
    autorewrite with var_db.
    compare x z; auto.
    (* x <> y *)
    eapply IHHWT2; auto;
      autorewrite with var_db;
      intuition.

  * econstructor; eauto with var_db.
    apply IHHWT; auto;
      autorewrite with var_db;
      intuition.

  * (* LetBang *)
    econstructor; eauto with var_db;
      try Var.Map.Tactics.partition_concat.

    compare x z.
    { autorewrite with var_db; auto. }
    {
      rewrite Var.Map.Proofs.add_neq_sym; auto.
      eapply IHHWT2; auto;
        Var.simplify.
    }

  * (* LetPair *)
    econstructor; eauto with var_db;
      try Var.Map.Tactics.partition_concat.
    autorewrite with var_db.
    compare x2 z; auto.
    autorewrite with var_db.
    compare x1 z; auto.
    eapply IHHWT2; auto;
      Var.simplify.
    
  * (* Lambda *)
    econstructor; auto.
    autorewrite with var_db.
    compare x z; auto.
    apply IHHWT; auto;
      Var.simplify.

  * (* Fix *)
    econstructor; auto with var_db.
    compare f z.
    {
      rewrite (Var.Map.Proofs.add_neq_sym _ f x); auto.
      autorewrite with var_db; auto.
      rewrite (Var.Map.Proofs.add_neq_sym _ x f); auto.
    }
    compare x z.
    { autorewrite with var_db; auto. }
    rewrite (Var.Map.Proofs.add_neq_sym _ x z); auto.
    rewrite (Var.Map.Proofs.add_neq_sym _ f z); auto.
    eapply IHHWT;
      Var.simplify.
Qed.
  

Lemma weakening_gen : forall Γ0,
  forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->
  forall Γ',
  Var.Map.Partition Γ' Γ Γ0 ->
  Var.Map.Properties.Disjoint Γ0 Δ ->
  WellTyped Γ' Δ Θ e τ.
Proof.
  intros Γ0.
  induction Γ0 using Var.Map.Properties.map_induction;
  intros ? ? ? ? ? HWT Γ' Hsub Hdisj.
  
  * vsimpl.
    reflect_partition.
    setoid_replace (Var.Map.concat Γ (Var.Map.M.empty _))
      with Γ; auto.
    {
      intros z. autorewrite with var_db.
      destruct (Var.Map.M.find z Γ); auto.
    }

  * reflect_partition. 
    assert (Var.Map.Equal Γ0_2
            (Var.Map.add x e Γ0_1))
      by auto.
    Var.Map.Tactics.subst_map.
    clear H1 Γ0_2 H0.
    autorewrite with var_db in *.
    destruct Hdisj as [Hdisj Hx].
    destruct Hdisj0 as [Hdisj0 Hx0].
    setoid_replace (Var.Map.concat Γ (Var.Map.add x e Γ0_1))
      with (Var.Map.add x e (Var.Map.concat Γ Γ0_1)).
    2:{
      intros z. autorewrite with var_db.
      compare x z.
      { (* if x=z then z does not occur in Γ *)
        apply Var.Map.Properties.F.not_find_in_iff in Hx0.
        rewrite Hx0; auto.
      }
      destruct (Var.Map.M.find z Γ) eqn:Hfind; auto.
    }
    
    apply weakening1; auto.
    2:{
      autorewrite with var_db. intuition.
    }
    eapply IHΓ0_1; eauto.
    {
      reflect_partition; auto; try reflexivity.
    }
Qed.

Lemma weakening : forall Γ Δ Θ e τ,
  WellTyped (Var.Map.empty _) Δ Θ e τ ->
  Var.Map.Properties.Disjoint Γ Δ ->
  WellTyped Γ Δ Θ e τ.
Proof.
  intros Γ Δ Θ e τ HWT.
  eapply weakening_gen; eauto with var_db.
Qed.

Lemma partition_not_in_inversion : forall A (m m1 m2 : Var.Map.t A) x,
  Var.Map.Partition m m1 m2 ->
  ~ Var.Map.In x m <->
  ~ Var.Map.In x m1 /\ ~ Var.Map.In x m2.
Admitted.

Ltac partition_not_in_inversion :=
    match goal with
    | [ Hpart : Var.Map.Partition ?m ?m1 ?m2,
        Hin : ~ Var.Map.In ?x ?m |- _ ] =>
      let Hin' := fresh "Hin" in
      assert (Hin' : ~ Var.Map.In x m1 /\ ~ Var.Map.In x m2)
      by (eapply partition_not_in_inversion; eauto);
      destruct Hin'
    end.


Lemma subst_not_in : forall e x v Γ Δ Θ τ,
  WellTyped Γ Δ Θ e τ ->
  ~ Var.Map.In x Γ ->
  ~ Var.Map.In x Δ ->
  subst x v e = e.
Proof.
  intros e; induction e; intros y v ? ? ? ? Hwt HΓ HΔ;
    simpl; try rename t0 into x;
    inversion Hwt; subst; clear Hwt;
    try partition_not_in_inversion;
    auto;
    try (
      try (erewrite IHe; eauto);
      try (erewrite IHe1; eauto);
      try (erewrite IHe2; eauto);
      try (erewrite IHe3; eauto);
      fail).
  * compare y x; auto.
    exfalso.
    apply HΔ.
    unfold Var.Map.Singleton in *. vsimpl.
    autorewrite with var_db. auto.
  * compare y x; auto.
    exfalso.
    apply HΓ. exists τ; auto.
  *
    erewrite IHe1; eauto.
    repeat reduce_eq_dec; auto.
    erewrite IHe2; eauto;
      autorewrite with var_db;
      intuition.
  * erewrite IHe1; eauto.
    repeat reduce_eq_dec; auto.
    compare y x; auto.
    erewrite IHe2; eauto;
      autorewrite with var_db;
      intuition.
  * rename t1 into z.
    erewrite IHe1; eauto.
    compare y x; auto.
    compare y z; auto.
    erewrite IHe2; eauto;
      autorewrite with var_db;
      intuition.
  * compare y x; auto.
    erewrite IHe; eauto;
      autorewrite with var_db;
      intuition.
  * rename x into f, t1 into x.
    compare y f; auto.
    compare y x; auto.
    erewrite IHe; eauto;
      autorewrite with var_db;
      intuition.
Qed.
Hint Resolve subst_not_in : var_db.

#[global] Hint Resolve weakening : var_db.

Lemma wt_subst_bang : forall e τ Γ Δ Θ x v τ',
  (*Val v ->*)
  WellTyped (Var.Map.empty _) (Var.Map.empty _) (Var.Map.empty _) v τ ->
  WellTyped (Var.Map.add x τ Γ) Δ Θ e τ' ->
  WellTyped Γ Δ Θ (subst x v e) τ'.
Proof.
  intros ? ? ? ? ? ? ? ? (*Hval*) Hv He.
  assert (Hdisj : Var.Map.Properties.Disjoint (Var.Map.add x τ Γ) Δ).
  { eapply wt_disjoint; eauto. }
  autorewrite with var_db in Hdisj.
  destruct Hdisj as [Hdisj Hin].
  dependent induction e;
    simpl;
    try rename t0 into y;
    inversion He; subst; clear He;
    vsimpl;

    reflect_partition;
    autorewrite with var_db in *;
    repeat match goal with
    | [H : ~ (_ \/ _) |- _ ] =>
      apply Decidable.not_or in H
    | [ H : _ /\ _ |- _ ] => destruct H
    end;

    try (econstructor; eauto with var_db; 
          try Var.Map.Tactics.partition_concat;
          fail).
  *  (* linear variable *)
      compare x y.
      apply WTQVar; auto with var_db.
  * (* non-linear variable *)
      compare x y.
      { (* x=y *)
        assert (τ = τ') by intuition.
        subst.
        apply weakening; auto.
      }
      { (* x <> y *)
        apply WTCVar; auto with var_db.
        intuition.
      }

  * (* LetIn *)
    eapply (WTLetIn Δ1 Δ2 Θ1 Θ2); eauto;
      try Var.Map.Tactics.partition_concat.
    compare x y.
    { (* x = y *)  compare x x; auto. }
    compare y x.
    eapply IHe2; eauto;
      [ | Var.simplify ].
    {
      autorewrite with var_db. intuition.
      apply Var.Map.Proofs.disjoint_remove_1; auto.
    }

  * (* Bang *)
    econstructor; auto with var_db.
    eapply IHe; eauto with var_db.
    Var.simplify.

  * (* LetBang *)
    eapply (WTLetBang _ Δ1 Δ2 Θ1 Θ2); eauto;
      try Var.Map.Tactics.partition_concat.
    compare x y.
    { (* x = y *) autorewrite with var_db in *; auto. }
    {
      eapply IHe2; eauto;
        [ | Var.simplify ].
      rewrite Var.Map.MProofs.Proofs.add_neq_sym; auto.
    }

  * (* LetPair *) rename y into y1, t1 into y2.
    eapply (WTLetPair Δ1 Δ2 Θ1 Θ2); eauto;
      try Var.Map.Tactics.partition_concat.
    compare x y1; compare x y2; auto.
    {
      reduce_eq_dec.
      autorewrite with var_db in *.
      reduce_eq_dec.
      auto.
    }
    {
      reduce_eq_dec; auto.
    }
    (* x <> y1 /\ x <> y2 *)
    repeat reduce_eq_dec.
    autorewrite with var_db in *.
    repeat reduce_eq_dec.
    
    eapply IHe2; [ eauto | eauto | | Var.simplify].
    {
      autorewrite with var_db.
      intuition.
      repeat apply Var.Map.Proofs.disjoint_remove_1; auto.
    }
    
  * (* Lambda *)
    econstructor; eauto with var_db.
    compare x y; reduce_eq_dec; auto.
    eapply IHe; [ eauto | eauto | | Var.simplify].
    {
      autorewrite with var_db.
      intuition.
      apply Var.Map.Proofs.disjoint_remove_1; auto.
    }

  * (* Fix *)
    rename y into f, t1 into y.
    econstructor; eauto with var_db.
    compare f x; reduce_eq_dec.
    {
      rewrite (Var.Map.MProofs.Proofs.add_neq_sym _ f y) in *;
        auto.
      autorewrite with var_db in *.
      rewrite <- (Var.Map.MProofs.Proofs.add_neq_sym _ f y) in *;
        auto.
    }
    compare y x; reduce_eq_dec.
    { autorewrite with var_db in *; auto. }
    eapply IHe;
      [ eauto |
      | Var.simplify | Var.simplify ].
    rewrite (Var.Map.MProofs.Proofs.add_neq_sym _ x f); auto.
    rewrite (Var.Map.MProofs.Proofs.add_neq_sym _ x y); auto.
Qed.



Lemma wt_subst : forall e Θ1 Θ2 τ Γ Δ Θ x v τ',
  (*Val v ->*)
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ1 v τ ->
  WellTyped Γ (Var.Map.add x τ Δ) Θ2 e τ' ->
  Var.Map.Partition Θ Θ1 Θ2 ->
  ~ Var.Map.In x Γ ->
  ~ Var.Map.In x Δ ->

  WellTyped Γ Δ Θ (subst x v e) τ'.
Proof.
  intros e; induction e;
    intros ? ? ? ? ? ? ? ? ? (*Hval*) Hv He Hpart HΓ Hin;
    simpl.
  * (* Var *)
    inversion He; subst; clear He;
      Var.simplify.
    rewrite Var.Map.Proofs.remove_not_in in H2; auto.
    vsimpl.    
    reduce_eq_dec.
    auto with var_db.    

  * (* LetIn *)
    inversion He; subst; clear He;
      Var.simplify.
    + (* x occcurs in Δ1 *)

      setoid_replace (if Var.FSet.MF.eq_dec x t0 then e2 else subst x v e2)
        with e2.
      2:{
        compare x t0; auto.
        eapply (subst_not_in x v e2);
          eauto;
          Var.simplify.
      }

      (* Γ; Δ1-{x}; Θ1+Θ0 |- subst x v e1 : τ *)
      eapply (WTLetIn
                (Var.Map.remove x Δ1) Δ2
                (Var.Map.concat Θ1 Θ0) Θ3);
        eauto with extra_var_db.
      eapply IHe1; eauto with var_db extra_var_db.
      Var.simplify.
      setoid_replace (Var.Map.add x τ Δ1) with Δ1;
        auto with extra_var_db.
      
    + (* x occurs in Δ2 *)
      rename t0 into y.
      simpl.
      erewrite (subst_not_in x v e1); eauto.
      assert (x <> y).
      { inversion 1; subst.
        absurd (Var.Map.In y Δ2); auto.
        exists τ; auto.
      }
      reduce_eq_dec.

      eapply (WTLetIn 
                Δ1 (Var.Map.remove x Δ2)
                Θ0 (Var.Map.concat Θ1 Θ3));
        eauto. (* if you use eauto with var_db here, it will hang *)
      2:{ Var.simplify. }
      2:{ auto with extra_var_db. }
      
      eapply IHe2;
        [ eauto | | auto with extra_var_db
        | Var.simplify | Var.simplify ].
      setoid_replace
        (Var.Map.add x τ (Var.Map.add y τ0 (Var.Map.remove x Δ2)))
        with (Var.Map.add y τ0 Δ2)
        by decide_equal;
      auto.

  * (* Bang e *) 
    inversion He; subst; clear He.
    Var.simplify.
      
  * (* LetBang *)
    inversion He; subst; clear He;
      Var.simplify.

    + (* x occcurs in Δ1 *)

      setoid_replace (if Var.FSet.MF.eq_dec x t0 then e2 else subst x v e2)
        with e2.
      2:{
        compare x t0; auto.
        eapply (subst_not_in x v e2); eauto.
        Var.simplify.
      }

      (* Γ; Δ1-{x}; Θ1+Θ0 |- subst x v e1 : τ *)
      eapply (WTLetBang _
                (Var.Map.remove x Δ1) Δ2
                (Var.Map.concat Θ1 Θ0) Θ3);
        eauto with extra_var_db.
      eapply IHe1; eauto with var_db extra_var_db.
      autorewrite with var_db.
      setoid_replace (Var.Map.add x τ Δ1) with Δ1;
        auto with extra_var_db.

    + (* x occurs in Δ2 *)
      rename t0 into y.
      erewrite (subst_not_in x v e1); eauto.


      assert (x <> y).
      { (* Lemma: since  Γ,y:τ0; Δ2; Θ3 |- e2 : τ' 
                  it must be the case that Disjoint(\Gamma,y:τ0, Δ2)
                  and thus y ∉ Δ2.
                  But y ∈ Δ2.
        *)
        inversion 1; subst.
        absurd (Var.Map.In y Δ2).
        2:{ exists τ; auto. }
        assert (Hdisj : Var.Map.Properties.Disjoint (Var.Map.add y τ0 Γ) Δ2).
        { eapply wt_disjoint; eauto. }
        specialize (Hdisj y).
        autorewrite with var_db in Hdisj.
        intuition.
      }
      reduce_eq_dec.

      eapply (WTLetBang _ 
                Δ1 (Var.Map.remove x Δ2)
                Θ0 (Var.Map.concat Θ1 Θ3));
        [ eauto |
        | auto with extra_var_db
        | auto with extra_var_db
        | Var.simplify ].
      eapply IHe2; auto;
      try match goal with
      | [ |- WellTyped _ _ _ v _ ] => eauto
      | [ |- Var.Map.Partition _ _ _ ] => eauto with var_db extra_var_db
      | [ |- ~ Var.Map.In _ _ ] => Var.simplify
      end.
      setoid_replace
        (Var.Map.add x τ (Var.Map.remove x Δ2))
        with Δ2
        by decide_equal;
      auto.


  * (* Bit b *)
    inversion He; subst; Var.simplify.

  * (* If *)
    inversion He; subst; clear He; Var.simplify.

    + (* x in e1 *)
      erewrite (subst_not_in x v e2); eauto.
      erewrite (subst_not_in x v e3); eauto.
      eapply (WTIf (Var.Map.remove x Δ1) Δ2 (Var.Map.concat Θ1 Θ0) Θ3);
        eauto with extra_var_db.
      eapply IHe1; eauto with var_db extra_var_db.
      setoid_replace (Var.Map.add x τ (Var.Map.remove x Δ1))
        with Δ1
        by decide_equal; auto.

    + (* x in e2/e3 *)

      erewrite (subst_not_in x v e1); eauto.
      eapply (WTIf Δ1 (Var.Map.remove x Δ2) Θ0 (Var.Map.concat Θ3 Θ1));
        eauto with extra_var_db.
      - eapply IHe2; eauto with var_db extra_var_db.
        setoid_replace (Var.Map.add x τ (Var.Map.remove x Δ2))
        with Δ2 by decide_equal; auto.
      - eapply IHe3; eauto with var_db extra_var_db.
        setoid_replace (Var.Map.add x τ (Var.Map.remove x Δ2))
          with Δ2 by decide_equal;
        auto.

  * (* Pair *)
    inversion He; subst; clear He;
      Var.simplify.
    
    + (* x in e1 *)
      erewrite (subst_not_in x v e2); eauto.
      eapply (WTPair (Var.Map.remove x Δ1) Δ2 (Var.Map.concat Θ1 Θ0) Θ3);
        eauto with var_db extra_var_db.
      eapply IHe1; eauto with var_db extra_var_db.

      setoid_replace (Var.Map.add x τ (Var.Map.remove x Δ1))
        with Δ1
        by decide_equal;
      auto.

    + (* x in e2 *)
      erewrite (subst_not_in x v e1); eauto.
      eapply (WTPair Δ1 (Var.Map.remove x Δ2) Θ0 (Var.Map.concat Θ3 Θ1));
        eauto with var_db extra_var_db.
      eapply IHe2; eauto with var_db extra_var_db.
      setoid_replace (Var.Map.add x τ (Var.Map.remove x Δ2))
        with Δ2
        by decide_equal; auto.

  * (* LetPair *) 
    rename t0 into y1, t1 into y2.
  
    inversion He; subst; clear He; Var.simplify.

    + (* x occcurs in Δ1 *)

      setoid_replace (if Var.FSet.MF.eq_dec x y1 then e2 else if Var.FSet.MF.eq_dec x y2 then e2 else subst x v e2)
        with e2.
      2:{
        repeat reduce_eq_dec; auto.
        eapply (subst_not_in x v e2); [eauto | | ];
          Var.simplify.
      }

      (* Γ; Δ1-{x}; Θ1+Θ0 |- subst x v e1 : τ *)
      eapply (WTLetPair
                (Var.Map.remove x Δ1) Δ2
                (Var.Map.concat Θ1 Θ0) Θ3);
        eauto with extra_var_db.
      eapply IHe1;
        [ eauto | 
        | eauto with extra_var_db
        | auto
        | Var.simplify ].
      autorewrite with var_db.
      setoid_replace (Var.Map.add x τ Δ1) with Δ1;
        auto with extra_var_db.

    + (* x occurs in Δ2 *)
      erewrite (subst_not_in x v e1); eauto.
      assert (x <> y1).
      { inversion 1; subst.
        absurd (Var.Map.In y1 Δ2); auto.
        exists τ; auto.
      }
      assert (x <> y2).
      { inversion 1; subst.
        absurd (Var.Map.In y2 Δ2); auto.
        exists τ; auto.
      }
      repeat reduce_eq_dec.

      eapply (WTLetPair
                Δ1 (Var.Map.remove x Δ2)
                Θ0 (Var.Map.concat Θ1 Θ3));
        auto;
        try match goal with
        | [ |- Var.Map.Partition _ _ _ ] =>
          auto with var_db extra_var_db
        | [ |- ~ Var.Map.In _ _ ] => Var.simplify
        | [ |- WellTyped _ _ _ e1 _ ] => eauto
        end.
      
      eapply IHe2; auto;
        try match goal with
        | [ |- WellTyped _ _ _ v _ ] => eauto
        | [ |- Var.Map.Partition _ _ _ ] =>
          auto with var_db extra_var_db
        | [ |- ~ Var.Map.In _ _ ] => Var.simplify
        end.
      
      setoid_replace
        (Var.Map.add x τ (Var.Map.add y1 τ1 (Var.Map.add y2 τ2 (Var.Map.remove x Δ2))))
        with (Var.Map.add y1 τ1 (Var.Map.add y2 τ2 Δ2))
        by decide_equal;
      auto.

  * (* Meas *)
    inversion He; subst; clear He.
    constructor.
    eapply IHe; eauto.

  * (* QRef *)
    inversion He; subst; Var.simplify.

  * (* New *) 
    inversion He; subst; clear He.
    constructor.
    eapply IHe; eauto.

  * (* Unitary *)
    inversion He; subst; clear He.
    constructor; auto.
    eapply IHe; eauto.

  * (* Lambda *)
    rename t0 into y.
    inversion He; subst; clear He.
    autorewrite with var_db in *.
    assert (x <> y) by intuition.
    compare x y.
    constructor; auto.
    eapply IHe;
      [ eauto | 
      | eauto | Var.simplify | Var.simplify ].
    setoid_replace (Var.Map.add x τ (Var.Map.add y τ1 Δ))
      with         (Var.Map.add y τ1 (Var.Map.add x τ Δ))
      by decide_equal;
      auto.
    
  * (* Fix *)
    inversion He; subst; Var.simplify.

  * (* App *)
    inversion He; subst; clear He; Var.simplify.

    + (* x in e1 *)
      erewrite (subst_not_in x v e2); eauto.
      eapply (WTApp (Var.Map.remove x Δ1) Δ2 (Var.Map.concat Θ1 Θ0) Θ3);
        eauto with extra_var_db.
      eapply IHe1; eauto with var_db extra_var_db.

      setoid_replace (Var.Map.add x τ (Var.Map.remove x Δ1))
        with Δ1
        by decide_equal;
      auto.

    + (* x in e2 *)
      erewrite (subst_not_in x v e1); eauto.
      eapply (WTApp Δ1 (Var.Map.remove x Δ2) Θ0 (Var.Map.concat Θ3 Θ1));
        eauto with extra_var_db.
      eapply IHe2; eauto with var_db extra_var_db.
      setoid_replace (Var.Map.add x τ (Var.Map.remove x Δ2))
        with Δ2
        by decide_equal; auto.
    
Qed.

Lemma wt_subst2 : forall Θ1 Θ2 Θ0 Θ τ1 τ2 Γ Δ Θ' x1 v1 x2 v2 e τ',
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ1 v1 τ1 ->
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ2 v2 τ2 ->
  WellTyped Γ (Var.Map.add x1 τ1 (Var.Map.add x2 τ2 Δ)) Θ0 e τ' ->

  Var.Map.Partition Θ Θ1 Θ2 ->
  Var.Map.Partition Θ' Θ Θ0 ->
  ~ Var.Map.In x1 Δ ->
  ~ Var.Map.In x2 Δ ->
  x1 <> x2 ->
  WellTyped Γ Δ Θ' (subst x2 v2 (subst x1 v1 e)) τ'.
Proof.
  intros.
  assert (Hin : ~ Var.Map.In x1 Γ /\ ~ Var.Map.In x2 Γ).
  {
    apply wt_disjoint in H1.
    split.
    specialize (H1 x1); autorewrite with var_db in *; intuition.
    specialize (H1 x2); autorewrite with var_db in *; intuition.
  }
  destruct Hin.
  eapply wt_subst; eauto.
  eapply wt_subst; eauto.
  2:{ autorewrite with var_db. intuition. }
  { reflect_partition; try reflexivity.
    Var.simplify; auto.
  }
  { auto with extra_var_db. }
Qed.


Lemma step_inversion : forall e refs ρ e' refs' ρ',
  
  step e refs ρ e' refs' ρ' ->

  forall refs1 refs2 τ,
  WellTyped (Var.Map.empty _) (Var.Map.empty _) refs1 e τ ->
  Var.Map.Partition refs refs1 refs2 ->
  exists refs1', 
    step e refs1 ρ e' refs1' ρ'
    /\
    Var.Map.Partition refs' refs1' refs2.
Proof.
Admitted.


Lemma step_weakening_1 : forall Θ1 Θ1' Θ2 e Θ cfg e' Θ' cfg',
  step e Θ1 cfg e' Θ1' cfg' ->
  Var.Map.Partition Θ Θ1 Θ2 ->
  Config.WellScoped Θ2 cfg ->
  Var.Map.Partition Θ' Θ1' Θ2 ->
  step e Θ cfg e' Θ' cfg'.
Admitted.
Lemma step_weakening_2 : forall Θ1 Θ2 Θ2' e Θ cfg e' Θ' cfg',
  step e Θ2 cfg e' Θ2' cfg' ->
  Var.Map.Partition Θ Θ1 Θ2 ->
  Config.WellScoped Θ1 cfg ->
  Var.Map.Partition Θ' Θ1 Θ2' ->
  step e Θ cfg e' Θ' cfg'.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hstep Hpart Hws Hpart'.
  eapply step_weakening_1; [eauto | | eauto | ].
  apply Var.Map.Properties.Partition_sym; auto.
  apply Var.Map.Properties.Partition_sym; auto.
Qed.

Ltac step_weakening_tac :=
  match goal with
  | [ Hstep : step ?e ?refs ?ρ ?e' ?refs' ?ρ',
      HTyped : WellTyped ?Γ ?Δ ?Θ ?e ?τ
      |- _ ] =>
      let refs1 := fresh "refs1" in
      let Hstep1 := fresh "Hstep1" in
      let Hpart1 := fresh "Hpart1" in
      edestruct (step_inversion _ _ _ _ _ _ Hstep) as [refs1 [Hstep1 Hpart1]]; eauto
  end.




Lemma preservation : forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->

  forall ρ e' Θ' ρ',
  Var.Map.Empty Γ ->
  Var.Map.Empty Δ ->
  
  step e Θ ρ e' Θ' ρ' ->
  
  WellTyped Γ Δ Θ' e' τ.
Proof.
  intros ? ? ? ? ? HWT.
  induction HWT; intros ? ? ? ? HΓ HΔ Hstep;
    unfold Var.Map.Singleton in *;
    try (rewrite HΔ in *; clear Δ HΔ);
    try (rewrite HΔ' in *; clear Δ' HΔ');
    try (inversion Hstep; auto; fail).
  * Var.simplify.
    autorewrite with var_db in *.
    assert (~ Var.Map.In x (Var.Map.empty typ))
      by (autorewrite with var_db; auto).
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *)  

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac; eauto.
      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT1) in Hstep1; eauto with var_db;
        try reflexivity.
      econstructor; eauto with var_db.

    + eapply wt_subst; eauto.

  * (* Let!*)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *)

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply IHHWT1 in Hstep1; eauto with var_db;
        try Var.simplify;
        try reflexivity.
      econstructor; eauto with var_db.

    + (* beta *)

      inversion HWT1; subst.
      Var.simplify.

      eapply wt_subst_bang; eauto with var_db.
    

  * (* If *) 
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e -> e1' *)
      step_weakening_tac.
      eapply (IHHWT1) in Hstep1; eauto with var_db;
        Var.simplify;
        try reflexivity.
      econstructor; eauto with var_db.

    + inversion HWT1; subst.
      Var.simplify.
      destruct b; auto.
  * (* Pair *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + step_weakening_tac.
      eapply (IHHWT1) in Hstep1; eauto with var_db;
        Var.simplify;
        try reflexivity.
      econstructor; eauto with var_db.

    + step_weakening_tac; eauto with var_db.
      {
        apply Var.Map.Properties.Partition_sym.
        eauto with var_db.
      }
      eapply (IHHWT2) in Hstep1; eauto with var_db;
        Var.simplify;
        try reflexivity.
      econstructor; eauto with var_db.
      {
        apply Var.Map.Properties.Partition_sym; auto.
      }

  * (* LetPair *) 
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT1) in Hstep1; eauto with var_db;
        try reflexivity.

      econstructor; eauto with var_db.

    + inversion HWT1; subst; clear HWT1.
      match goal with
      | [ H : Val (Pair _ _) |- _ ] =>
          inversion H; subst; clear H
      end.
      Var.simplify.
      autorewrite with var_db in HWT2.
      eapply wt_subst2; eauto.

  * (* Meas *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac; eauto with var_db.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT) in Hstep1; eauto with var_db;
        try reflexivity.
      econstructor; eauto with var_db.

    + econstructor; eauto with var_db.

      match goal with
      | [ H : _ = Config.measure _ _ _ _ |- _ ] =>
        inversion H; subst; clear H
      end.
      eauto with var_db.

  * (* New *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac; eauto with var_db.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT) in Hstep1; eauto with var_db;
        try reflexivity.
      econstructor; eauto with var_db.

    + match goal with
      | [ H : _ = Config.new _ _ _ |- _ ] =>
        inversion H; subst; clear H
      end.
      inversion HWT; subst; clear HWT.
      Var.simplify.
      remember (Var.fresh Θ) as idx eqn:Hidx;
        clear Hidx.
      subst_map.
      econstructor; eauto with var_db.
      unfold Var.Map.Singleton. reflexivity.

  * (* Unitary *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac; eauto with var_db.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT) in Hstep1; eauto with var_db;
        try reflexivity.
      econstructor; eauto;
        eauto with var_db.

    + inversion HWT; subst.
      econstructor; eauto.

    + inversion HWT; subst; auto.
      econstructor; eauto.

  * (* App *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac; eauto with var_db.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT1) in Hstep1;
        eauto with var_db;
        try reflexivity.
      econstructor; eauto; eauto with var_db.

    + (* e2 -> e2' *)
      step_weakening_tac.
      { apply Var.Map.Properties.Partition_sym; eauto. }
      eapply IHHWT2 in Hstep1; eauto with var_db.
      econstructor; eauto with var_db.
      { apply Var.Map.Properties.Partition_sym; eauto. }


    + (* Lambda beta reduction *)
      inversion HWT1; subst; clear HWT1.
      rename H9 into HWT1.
      autorewrite with var_db in HWT1.
      eapply wt_subst; eauto with var_db.
      { apply Var.Map.Properties.Partition_sym; eauto. }

    + (* Fix beta reduction *)
      (*
        f:!τ -o τ', x:τ; ∅; Θ1 ⊢ e : τ'     ∅;∅;∅ ⊢ v2 : τ
        ------------------------------    --------------------
        ∅;∅;Θ1 ⊢ fix f.x.e : !τ -o τ'    ∅;∅;∅ ⊢ !v2 : !τ
        -----------------------------------------------------
        ∅;∅;Θ1 ⊢ (fix f.x.e) !v2 : τ'

      WTS
      ∅;∅;Θ1,Θ2 ⊢ e{fix f.x.e / f, e2/x} : τ'
      *)
      inversion HWT1; subst. vsimpl.
      inversion HWT2; subst. vsimpl.

      eapply wt_subst_bang; eauto with var_db.
      eapply wt_subst_bang; eauto with var_db.
Qed.


Lemma step_WellScoped_disjoint : forall Θ2 e Θ1 cfg e' Θ1' cfg',
  step e Θ1 cfg e' Θ1' cfg' ->
  Var.Map.Properties.Disjoint Θ1 Θ2 ->
  Config.WellScoped Θ2 cfg ->
  Var.Map.Properties.Disjoint Θ1' Θ2.
Admitted.


Ltac simplify_val :=
  repeat match goal with
  | [ Hval : Val ?e, Hwt : WellTyped _ _ _ ?e ?τ |- _ ] =>
    match τ with
    | BIT => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    | QUBIT  => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    | Tensor _ _ => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    | Lolli _ _ => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    | BANG _ => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    end
  end.

Ltac ws_partition_tac :=
  match goal with
  | [Hpart : Var.Map.Partition ?Θ ?Θ1 ?Θ2,
     H : Config.WellScoped ?θ ?cfg |- _ ] =>
     let H' := fresh "H" in
     assert (H' : Config.WellScoped Θ1 cfg /\ Config.WellScoped Θ2 cfg)
     by (apply Config.WellScoped_concat; reflect_partition; auto);
     destruct H'
  end.
Ltac ws_step_tac :=
  match goal with
  | [ Hstep : step ?e ?Θ1 ?cfg ?e' ?Θ1' ?cfg' |- Var.Map.Partition _ ?Θ1' ?Θ2 ] =>
      reflect_partition; [ | reflexivity];
      eapply step_WellScoped_disjoint; eauto
  | [ Hpart : Var.Map.Partition ?Θ ?Θ1 ?Θ2,
      Hstep : step ?e ?Θ1 ?cfg ?e' ?Θ1' ?cfg' |- _ ] =>
      let H' := fresh "H" in
      assert (H' : Var.Map.Partition (Var.Map.concat Θ1' Θ2) Θ1' Θ2)
      by (reflect_partition; [ | reflexivity];
          eapply step_WellScoped_disjoint; eauto)
  end.


Theorem progress : forall e τ Γ Δ Θ,
  WellTyped Γ Δ Θ e τ ->
  forall cfg,
  Config.WellScoped Θ cfg ->
  Var.Map.Empty Γ ->
  Var.Map.Empty Δ ->
  Val e \/ exists e' Θ' cfg', step e Θ cfg e' Θ' cfg'.
Proof.
  intros e τ Γ Δ Θ Hwt.
  induction Hwt; intros cfg Hscoped HΓ HΔ;
    vsimpl;
    autorewrite with var_db in *;
    try contradiction;
    try (left; auto with var_db; fail).

  * (* Let *)
    ws_partition_tac.
    
    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    + (* e1 is a value *)
      right. eexists. eexists. eexists.
      eapply LetB; auto.

    + (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply LetC; eauto.
      eapply step_weakening_1; eauto;
        ws_step_tac.

  * (* Let! *)
    ws_partition_tac.

    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    + (* e1 is a value *)
      (* e1 must be of the form (Bang e1') *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply LetBangB; auto.

    + (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply LetBangC; eauto.
      eapply step_weakening_1; eauto;
        ws_step_tac.

  * (* If *)
    ws_partition_tac.

    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    + (* e1 is a value *)
      (* e1 must be of the form Bit b *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply IfB; auto.

    + (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply IfC; eauto.
      eapply step_weakening_1; eauto;
        ws_step_tac.

  * (* Pair *)
    ws_partition_tac.
    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    2:{ (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply PairC1; eauto.
      eapply step_weakening_1; eauto;
        ws_step_tac.
    }
    edestruct IHHwt2 as [Hv2 | [e2' [Θ2' [cfg' Hstep2]]]];
      eauto with var_db.
    { (* e2 can take a step *)
      right. eexists. eexists. eexists.
      apply PairC2; eauto.
      eapply step_weakening_2; [eauto | eauto with var_db | | ];
        auto.
      {
        reflect_partition; try reflexivity.
        apply Var.Map.Proofs.disjoint_sym.
        eapply step_WellScoped_disjoint; eauto.
        apply Var.Map.Proofs.disjoint_sym; auto.
      }
    }

  * (* LetPair *)
    ws_partition_tac.
    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    + (* e1 is a value *)
      (* e1 must be of the form Bit b *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply LetPairB; auto with var_db.

    + (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply LetPairC; eauto.
      eapply step_weakening_1; eauto;
        ws_step_tac.
  
  * (* Meas *)
    edestruct IHHwt as [Hv | [e' [Θ' [cfg' Hstep]]]];
      eauto with var_db.
    + (* e' is a value -- must be a qref *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply MeasB; eauto.
      reflexivity.

    + (* e' can take a step *)
      right. eexists. eexists. eexists.
      apply MeasC; eauto.

  * (* New *)
    edestruct IHHwt as [Hv | [e' [Θ' [cfg' Hstep]]]];
      eauto with var_db.
    + (* e' is a value -- must be a bit *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply New0; eauto.
      reflexivity.

    + (* e' can take a step *)
      right. eexists. eexists. eexists.
      apply NewC; eauto.

  * (* Unitary *)
    edestruct IHHwt as [Hv | [e' [Θ' [cfg' Hstep]]]];
      eauto with var_db.
    
    + (* e' is a value *)

      (* τ = Qubit or Qubit ** Qubit *)
      assert (Hτ : τ = QUBIT \/ τ = Tensor QUBIT QUBIT).
      { destruct U; inversion H; subst; auto. }
      destruct Hτ as [Hτ | Hτ]; rewrite Hτ in *.
      - (* τ = QUBIT *)
        simplify_val.
        right. eexists. eexists. eexists.
        eapply UnitaryB1; eauto.

      - (* τ = Tensor QUBIT QUBIT *)
        simplify_val.
        right. eexists. eexists. eexists.
        eapply UnitaryB2; eauto.
        {
          vsimpl. unfold Var.Map.Singleton in *.
          vsimpl.
          reflect_partition.
          decide_equal.
        }

    + (* e can take a step *)
      right. eexists. eexists. eexists.
      apply UnitaryC; eauto.

  * (* App *)
    ws_partition_tac.
    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    2:{ (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply AppC1; eauto.
      eapply step_weakening_1; eauto;
        ws_step_tac.
    }
    edestruct IHHwt2 as [Hv2 | [e2' [Θ2' [cfg' Hstep2]]]];
      eauto with var_db.
    2:{ (* e2 can take a step *)
      right. eexists. eexists. eexists.
      apply AppC2; eauto.
      eapply step_weakening_2; eauto.
      {
        reflect_partition; try reflexivity.
        apply Var.Map.Proofs.disjoint_sym.
        eapply step_WellScoped_disjoint; eauto.
        apply Var.Map.Proofs.disjoint_sym; auto.
      }
    }
    (* both e1 and e2 are values *)
    simplify_val.
    - (* v1 is a lambda *)
      right. eexists. eexists. eexists.
      eapply AppB; eauto.

    - (* v1 is a fix *)
      right. eexists. eexists. eexists.
      eapply AppFixB; eauto.

Unshelve. exact true.
Qed.