From Qoreo Require Import Base.
From Qoreo Require Expr Choreography.

Module Label := Choreography.Label.
Module Choreography := Choreography.Choreography.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.
Import Actor.Map.Tactics.

Module Insn.
    Inductive t :=
    | Let : Var.t -> Expr.t -> t
    | LetBang : Var.t -> Expr.t -> t
    | LetPair : Var.t -> Var.t -> Expr.t -> t
    | Send : Expr.t -> Actor.t -> t
    | Receive : Var.t -> Actor.t ->  t
    | EPR : Var.t -> Actor.t -> t
    .

    Definition subst (x : Var.t) (v : Expr.t) (I : t) : t :=
        match I with
        | Let y e => Let y (Expr.subst x v e)
        | LetBang y e => LetBang y (Expr.subst x v e)
        | LetPair y1 y2 e => LetPair y1 y2 (Expr.subst x v e)
        | Send e A => Send (Expr.subst x v e) A
        | Receive y A => Receive y A
        | EPR y A => EPR y A
        end.

    Definition binders (I : t) : Var.FSet.t :=
        match I with
        | Let y _ | LetBang y _ | Receive y _ | EPR y _ => Var.FSet.singleton y
        | LetPair y1 y2 _ => Var.FSet.add y1 (Var.FSet.singleton y2)
        | Send _ _ => Var.FSet.empty
        end.
End Insn.

Module Process.
    Definition t := list Insn.t.

    Fixpoint subst (x : Var.t) (v : Expr.t) (P : t) : t :=
    match P with
    | [] => []
    | (I0 :: P') =>
      let P'' := if Var.FSet.mem x (Insn.binders I0)
                 then P'
                 else subst x v P'
      in
      (Insn.subst x v I0) :: P''
    end.


    (* Semantics *)

    Inductive step : Process.t -> Var.Map.t nat -> Config.t -> Process.t -> Var.Map.t nat -> Config.t -> Prop :=
    | LetC : forall x e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.Let x e :: P) refs ρ (Insn.Let x e' :: P) refs' ρ'
    | LetB : forall x v P refs ρ P',
        Expr.Val v ->
        P' = Process.subst x v P ->
        step (Insn.Let x v :: P) refs ρ P' refs ρ

    | LetBangC : forall x e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.LetBang x e :: P) refs ρ (Insn.LetBang x e' :: P) refs' ρ'
    | LetBangB : forall x e P refs ρ P',
        P' = Process.subst x e P ->
        step (Insn.LetBang x (Expr.Bang e) :: P) refs ρ P' refs ρ

    | LetPairC : forall x1 x2 e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.LetPair x1 x2 e :: P) refs ρ (Insn.LetPair x1 x2 e' :: P) refs' ρ'
    | LetPairP : forall x1 x2 v1 v2 P ρ refs P',
        Expr.Val v1 -> Expr.Val v2 ->
        P' = Process.subst x2 v2 (Process.subst x1 v1 P) ->
        step (Insn.LetPair x1 x2 (Expr.Pair v1 v2) :: P) refs ρ P' refs ρ

    | SendC : forall e B P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.Send e B :: P) refs ρ (Insn.Send e' B :: P) refs' ρ'
    .

End Process.

Module Network.
    Definition t := Actor.Map.t (Process.t).

    Inductive step :    Network.t -> ChorEnv.t nat -> Config.t ->
                        Label.t ->
                        Network.t -> ChorEnv.t nat -> Config.t -> Prop :=

    | Loc : forall P P' refsA' N' N refs cfg A refs' cfg',
      Actor.Map.MapsTo A P N ->
      Process.step  P (ChorEnv.find A refs) cfg
                    P' refsA' cfg' ->
      N' = Actor.Map.add A P' N ->
      ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->
      step  N refs cfg
            (Label.Loc A)
            N' refs' cfg'

    | Send : forall PA PB y N refs cfg A v B N',
      A <> B ->
      Actor.Map.MapsTo A (Insn.Send v B :: PA) N ->
      Actor.Map.MapsTo B (Insn.Receive y A :: PB) N ->
      Expr.Val v ->
      N' = Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N) ->
      
      step N refs cfg (Label.Send A v B) N' refs cfg

    | EPR : forall x y PA PB qA qB N refs cfg A B N' refs' cfg',
      A <> B ->
      Actor.Map.MapsTo A (Insn.EPR x B :: PA) N ->
      Actor.Map.MapsTo B (Insn.EPR y A :: PB) N ->
      ChorEnv.epr A B refs cfg = (qA, qB, refs', cfg') ->
      N' = Actor.Map.add A (Process.subst x (Expr.Var qA) PA) (
            Actor.Map.add B (Process.subst y (Expr.Var qB) PB) N) ->

      step N refs cfg (Label.EPR A B) N' refs' cfg'
    .

    Record WF (Actors : Actor.FSet.t) (N : Network.t) :=
        {
            wf_domain : forall A, Actor.FSet.In A Actors <-> Actor.Map.In A N;
        }.
    
End Network.

Definition conso {A : Type} (x : A) (xso : option (list A)) : option (list A) :=
  match xso with
  | None => None
  | Some xs => Some (x :: xs)
  end.

Fixpoint epp (p : Actor.t) (c : Choreography.t): option Process.t :=
  match c with
  | [] => Some []
  | Choreography.Insn.Send A1 e A2 x :: C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
      | (left _, left _)  => None
      | (left _, right _) => conso (Insn.Send e A2) (epp p C)
      | (right _, left _) => conso (Insn.Receive x A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Insn.EPR A1 x1 A2 x2 :: C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
      | (left _, left _)  => None
      | (left _, right _) => conso (Insn.EPR x1 A2) (epp p C)
      | (right _, left _) => conso (Insn.EPR x2 A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Insn.Let A1 x e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.Let x e) (epp p C)
      else epp p C
  | Choreography.Insn.LetBang A1 x e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.LetBang x e) (epp p C)
      else epp p C
  | Choreography.Insn.LetPair A1 x1 x2 e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.LetPair x1 x2 e) (epp p C)
      else epp p C
  (* | _ => None *)
end.

(*
Inductive EPP : list Actor.t -> Choreography.t -> Network.t -> Prop :=
| epp_empty : forall C, EPP [] C (Actor.Map.empty _)
| epp_cons : forall A Actors C P N,
    epp A C = Some P ->
    EPP Actors C N ->
    EPP (A::Actors) C (Actor.Map.add A P N).
*)
Inductive EPP : Actor.t -> Choreography.t -> Process.t -> Prop :=
| EPP_nil : forall A, EPP A [] []

| EPP_send : forall D A C P B e y,
    D = A ->
    D <> B ->
    EPP D C P ->
    EPP D (Choreography.Insn.Send A e B y :: C) (Insn.Send e B :: P)
| EPP_receive : forall D B C P A e y,
    D = B ->
    D <> A ->
    EPP D C P ->
    EPP D (Choreography.Insn.Send A e B y :: C) (Insn.Receive y A :: P)

| EPP_EPR_1 : forall D A B x y C P,
    D = A ->
    D <> B ->
    EPP D C P ->
    EPP D (Choreography.Insn.EPR A x B y :: C) (Insn.EPR x B :: P)
| EPP_EPR_2 : forall D A B x y C P,
    D <> A ->
    D = B ->
    EPP D C P ->
    EPP D (Choreography.Insn.EPR A x B y :: C) (Insn.EPR y A :: P)

| EPP_Let : forall D A x e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.Let A x e :: C) (Insn.Let x e :: P)

| EPP_LetBang : forall D A x e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.LetBang A x e :: C) (Insn.LetBang x e :: P)

| EPP_LetPair : forall D A x1 x2 e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.LetPair A x1 x2 e :: C) (Insn.LetPair x1 x2 e :: P)

| EPP_disjoint : forall A I C P,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C P ->
  EPP A (I :: C) P
.

Lemma EPP_correct : forall A C P,
    EPP A C P <-> epp A C = Some P.
Proof.
    intros.
    split.
    * intros HEPP. 
      induction HEPP; simpl; auto;
        subst;
        try rewrite IHHEPP;
        Actor.simplify.
      destruct I; simpl in *;
        Actor.simplify.
    * revert A P.
      induction C as [ | I C]; intros A P Hepp.
      { 
        simpl in *.
        inversion Hepp; subst; clear Hepp.
        constructor.
      }
      simpl in Hepp.
      destruct (epp A C) eqn:IH.
      2:{
        destruct I; Actor.simplify; try rewrite IH in Hepp.
      }
      destruct I
        as [B1 e B2 x | B1 x1 B2 x2 | B x e | B x e | B x1 x2 e];
        Actor.simplify;
        inversion Hepp; subst; clear Hepp;
          constructor; auto;
        simpl; Actor.simplify.
Qed.

Definition EPP_N (C : Choreography.t) (N : Network.t) : Prop :=
    forall A PA,
        Actor.Map.MapsTo A PA N
        <->
        (*Actor.FSet.In A (Choreography.actors C)*)
        EPP A C PA.

(* Correctness of EPP *)

Theorem soundness : forall C C' refs cfg refs' cfg' l N,

    Choreography.step C refs cfg l C' refs' cfg' ->
    EPP_N C N ->
    exists N', EPP_N C'  N' /\
               Network.step N refs cfg l N' refs' cfg'.
Admitted.

Require Import Stdlib.Program.Equality.

Lemma actors_subst : forall I B x v,
  Actor.FSet.Equal
    (Choreography.Insn.actors (Choreography.Insn.subst B x v I))
    (Choreography.Insn.actors I).
Proof.
  destruct I; intros; Actor.simplify.
Qed.


Lemma EPP_disjoint_inversion : forall A I C P,
  EPP A (I :: C) P ->
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C P.
Proof.
Admitted.
About Actor.Map.FSetProperties.add_iff.
Hint Rewrite Actor.Map.FSetProperties.add_iff : actor_db.


Lemma EPP_subst_neq : forall C A P B x v,
    A <> B ->
    EPP A C P ->
    EPP A (Choreography.subst B x v C) P.
Proof.
  induction C as [ | I C];
    intros ? ? ? ? ? Hneq H.
  { inversion H; subst; constructor. }
  inversion H; subst; clear H; simpl;
    try (repeat reduce_eq_dec;
    repeat Var.Map.Tactics.reduce_eq_dec;
    simpl;
    constructor; auto; fail).

  apply EPP_disjoint.
  { rewrite actors_subst; auto. }
  destruct (Choreography.Insn.rebound_in B x I) eqn:HI; auto.
Qed.

Lemma EPP_subst_neq_bwd : forall C A P B x v,
    A <> B ->
    EPP A (Choreography.subst B x v C) P ->
    EPP A C P.
Proof.
  intros C A P B x v Hneq.
  revert P.
  induction C as [ | I C]; 
    intros P Hepp; simpl; auto.
  assert (Hdec : Actor.FSet.In A (Choreography.Insn.actors I) 
        \/ ~ Actor.FSet.In A (Choreography.Insn.actors I)).
  {
    destruct I; simpl; Var.simplify.
  }
  destruct Hdec as [Hin | Hin].
  2:{
    apply EPP_disjoint; auto.
    simpl in *.
    apply EPP_disjoint_inversion in Hepp.
    destruct (Choreography.Insn.rebound_in B x I) eqn:HB; auto.
    rewrite actors_subst; auto.
  }

  destruct I as 
    [A0 v0 B0 | A0 x0 B0 y0 | A0 x0 v0 | A0 x0 v0 | A0 x0 y0 v0];
    simpl in *.
  * simpl in Hin. autorewrite with actor_db in Hin.
    destruct Hin; subst.
    + (* A = A0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify.
    + (* A = B0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * simpl in Hin. autorewrite with actor_db in Hin.
    destruct Hin; subst.
    + (* A = A0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify.
    + (* A = B0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify.
  * simpl in Hin. autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * simpl in Hin. autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * simpl in Hin. autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
Qed. 



Lemma add_mem_iff : forall x y s,
  Var.Map.S.mem x (Var.Map.S.add y s)
  =
  if Var.eq_dec x y then true else Var.Map.S.mem x s.
Proof.
  intros.
  rewrite Var.Map.MProofs.FSetProperties.add_b.
  unfold Var.Map.MProofs.FSetProperties.eqb.
  Var.simplify.
Qed.
#[global] Hint Rewrite add_mem_iff : var_db.


Lemma subst_not_in_I : forall I A x v,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  Choreography.Insn.subst A x v I = I.
Proof.
  destruct I; intros; simpl in *; Actor.simplify.
Qed.
Lemma rebound_not_in_I : forall I A x,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  Choreography.Insn.rebound_in A x I = false.
Proof.
  destruct I; intros; simpl in *; Actor.simplify.
Qed.

Lemma singleton_mem_iff : forall x y,
  Var.Map.S.mem y (Var.Map.S.singleton x)
  =
  if Var.eq_dec x y then true else false.
Proof.
  intros.
  rewrite Var.Map.FSetProperties.singleton_b.
  auto.
Qed.
#[global] Hint Rewrite singleton_mem_iff : var_db.



Lemma EPP_subst_eq : forall A C P x v,
    EPP A C P ->
    EPP A (Choreography.subst A x v C) (Process.subst x v P).
Proof.
  intros ? ? ? ? ? H.
  induction H; subst; simpl;
    Actor.simplify;
    Var.simplify;
    simpl;
    try (constructor; auto; fail).

  rewrite subst_not_in_I; auto.
  rewrite rebound_not_in_I; auto.
  apply EPP_disjoint; auto.
Qed.


Lemma EPP_subst_eq_bwd : forall A x v C P',
  EPP A (Choreography.subst A x v C) P' ->
  exists P, EPP A C P /\ P' = Process.subst x v P.
Proof.
  intros A x v C.
  induction C as [ | I C];
    intros P' H;
    simpl in *.
  {
    inversion H; subst.
    exists []. split; auto.
  }
    assert (Hdec : Actor.FSet.In A (Choreography.Insn.actors I) 
        \/ ~ Actor.FSet.In A (Choreography.Insn.actors I)).
  {
    destruct I; simpl; Var.simplify.
  }
  destruct Hdec as [Hin | Hin].
  2:{
    apply EPP_disjoint_inversion in H; auto.
    2:{ rewrite actors_subst; auto. }
    rewrite rebound_not_in_I in H; auto.
    apply IHC in H.
    destruct H as [P [H ?]]; subst.
    exists P; split; auto.
    apply EPP_disjoint; auto.
  }

  destruct I as 
    [A0 v0 B0 y0 | A0 x0 B0 y0 | A0 x0 v0 | A0 x0 v0 | A0 x0 y0 v0];
    simpl in *.
  * autorewrite with actor_db in Hin.
    inversion H; subst; clear H.

    + (* A = A0 *)
      Actor.simplify.
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.Send v0 B0 :: P0).
      split; auto.
      constructor; auto.

    + (* A = B0 *)
      Actor.simplify.
      Var.Map.Tactics.compare x y0.
      - (* x = y0 *)
        exists (Insn.Receive x A0 :: P).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.
      
      - (* x <> y0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.Receive y0 A0 :: P0).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A <> A0 /\ B <> B0 *)
      (* contradicts Hin *)
      simpl in *. Actor.simplify.
      destruct Hin; subst; contradiction.

  * (* EPR *) 
    autorewrite with actor_db in Hin.
    inversion H; subst; clear H.

    + (* A = A0 *)
      Actor.simplify.
      Var.Map.Tactics.compare x x0.
      - (* x = y0 *)
        exists (Insn.EPR x B0 :: P).
        simpl in *. Var.simplify.
        split; auto.
        constructor; auto.

      - (* x <> x0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.EPR x0 B0 :: P0).
        simpl in *. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A = B0 *)
      Actor.simplify. simpl in *.
      Var.Map.Tactics.compare x y0.
      - (* x = y0 *)
        exists (Insn.EPR x A0 :: P).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.
      
      - (* x <> y0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.EPR y0 A0 :: P0).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A <> A0 /\ B <> B0 *)
      (* contradicts Hin *)
      simpl in *. Actor.simplify.
      destruct Hin; subst; contradiction.

  * (* Let *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0.
    + (* x = x0 *)
      exists (Insn.Let x v0 :: P).
      simpl. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.Let x0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.


  * (* LetBang *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0.
    + (* x = x0 *)
      exists (Insn.LetBang x v0 :: P).
      simpl. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.LetBang x0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.

  
  * (* LetPair *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0;
      [ | Var.Map.Tactics.compare x y0 ].
    + (* x = x0 *)
      exists (Insn.LetPair x y0 v0 :: P).
      simpl in *. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x = y0 *)
      exists (Insn.LetPair x0 x v0 :: P).
      simpl in *. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 /\ x <> y0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.LetPair x0 y0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.
Qed.


Lemma EPP_subst_iff : forall C D PD A x v,
    EPP D (Choreography.subst A x v C) PD <->
    (D = A /\ exists PD0,
                EPP D C PD0 
                /\ PD = Process.subst x v PD0)
    \/
    (D <> A /\ EPP D C PD).
Proof.
  intros.
  split; intros H.
  * compare A D.
    + left. split; auto.
      apply EPP_subst_eq_bwd; auto.
    + right. split; auto.
      eapply EPP_subst_neq_bwd; eauto.
  * destruct H as [[? [PD0 [HPD0 ?]]] | [? HPD]]; subst.
    + apply EPP_subst_eq; auto.
    + apply EPP_subst_neq; auto. 
Qed.




Definition insn_matches_label (I : Choreography.Insn.t) (l : Label.t) : bool :=
  match I, l with
  | Choreography.Insn.Send A _ B _, Label.Send A' _ B'
  | Choreography.Insn.EPR A _ B _, Label.EPR A' B' =>
    if Actor.eq_dec A A'
    then if Actor.eq_dec B B' then true else false
    else false
  | Choreography.Insn.Let A _ _, Label.Loc A'
  | Choreography.Insn.LetBang A _ _, Label.Loc A'
  | Choreography.Insn.LetPair A _ _ _, Label.Loc A' =>
    if Actor.eq_dec A A' then true else false

  | _, _ => false
  end.

(** Return the choreography C' such that C, refs -l-> C', refs'
  * if such a choreography exists.
  *)
Inductive step_label : Choreography.t -> ChorEnv.t nat ->
                       Label.t ->
                       Choreography.t  -> Prop :=

| StepSend : forall A v B x C refs A' v' B' C',
  A = A' ->
  B = B' ->
  v = v' ->
  C' = Choreography.subst B x v C ->
  step_label  (Choreography.Insn.Send A v B x :: C)
              refs
              (Label.Send A' v' B')
              C'

| StepEPR : forall q1 q2 A x B y C refs A' B' C',
  A = A' ->
  B = B' ->
  q1 = Var.fresh (ChorEnv.find A refs) ->
  q2 = Var.fresh (Var.Map.add x q1 (ChorEnv.find A refs)) ->

  C' = Choreography.subst A x (Expr.Var q1)
        (Choreography.subst B y (Expr.Var q2)
        C) ->

  step_label  (Choreography.Insn.EPR A x B y :: C)
              refs
              (Label.EPR A' B')
              C'

| StepLet :forall A x v C refs A' C',
  A = A' ->
  C' = Choreography.subst A x v C ->
  step_label (Choreography.Insn.Let A x v :: C)
             refs
             (Label.Loc A')
             C'

| StepLetBang : forall A x v' C refs A' C',
  A = A' ->
  C' = Choreography.subst A x v' C ->
  step_label (Choreography.Insn.LetBang A x (Expr.Bang v') :: C)
             refs
             (Label.Loc A')
             C'

| StepLetPair : forall A x1 x2 v1 v2 C refs A' C',
  A = A' ->
  C' = Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C) ->
  step_label (Choreography.Insn.LetPair A x1 x2 (Expr.Pair v1 v2) :: C)
             refs
             (Label.Loc A')
             C'

| StepCons : forall I C refs l C',
  Actor.FSet.Empty
    (Actor.FSet.inter (Choreography.Label.actors l)
                      (Choreography.Insn.actors I)) ->
  step_label C refs l C' ->
  step_label (I :: C) refs l (I :: C')
.

(*
Fixpoint step_label l (refs : Var.Map.t nat) C :=
  match C with
  | [] => []
  | I0 :: C' =>

    match I0 with

    | Choreography.Insn.Send A v B y =>
      if insn_matches_label I0 l
      then Choreography.subst B y v C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.EPR A x B y =>
      let q1 := Var.fresh refs in
      let refs' := Var.Map.add x q1 refs in
      let q2 := Var.fresh refs' in
      let refs'' := Var.Map.add y q2 refs' in

      if insn_matches_label I0 l
      then  Choreography.subst A x (Expr.Var q1)
            (Choreography.subst B y (Expr.Var q2)
            C')
      else I0 :: step_label l refs'' C'

    | Choreography.Insn.Let A x v =>
      if insn_matches_label I0 l
      then Choreography.subst A x v C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.LetBang A x (Expr.Bang v') =>
      if insn_matches_label I0 l
      then Choreography.subst A x v' C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.LetPair A x1 x2 (Expr.Pair v1 v2) =>
      if insn_matches_label I0 l
      then Choreography.subst A x1 v1
          (Choreography.subst A x2 v2 C')
      else I0 :: step_label l refs C'

    | _ => I0 :: step_label l refs C'

    end
  end.
  *)

(*
(** Return the choreography C' such that C -(Send A v B y)-> C' *)
Fixpoint step_send A B (C : Choreography.t) : Choreography.t :=
    match C with
    | [] => []
    | Choreography.Insn.Send A0 v0 B0 y0 :: C' =>
        match Actor.eq_dec A A0, Actor.eq_dec B B0 with
        | left _, left _ => Choreography.subst B0 y0 v0 C'
        | _, _ => Choreography.Insn.Send A0 v0 B0 y0 :: (step_send A B C')
        end
    | I' :: C' => I' :: step_send A B C'
    end.
  *)

  
Lemma step_send_complete : forall C A v y B PA PB refs cfg C',
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    step_label C refs (Label.Send A v B) C' ->
    Choreography.step C refs cfg (Label.Send A v B)
                      C' refs cfg.
Proof.
    induction C as [ | I C];
        intros A v y B PA PB refs cfg C' HEPPA HEPPB Hval Hstep.
    { contradict HEPPA. simpl; inversion 1. }
    inversion Hstep; subst; clear Hstep.

    inversion HEPPA; subst; clear HEPPA;
    inversion HEPPB; subst; clear HEPPB;
      simpl in *;
      Actor.simplify.
    * (* send *)
      apply Choreography.SendB; auto.
        
    * apply Choreography.Delay; auto.
        match goal with
        | [ H : Actor.FSet.Empty _ |- _ ] =>
          rename H into Hempty
        end.
    (*
      assert (Hin : ~ (Actor.FSet.In A (Choreography.Insn.actors I)) /\ ~ ).
      {
        intros Hin.
        match goal with
        | [ H : Actor.FSet.Empty _ |- _ ] =>
          specialize (H A);
          simpl in H;
          Actor.simplify
        end.
      }
        *)
      apply EPP_disjoint_inversion in HEPPA; auto.
      2:{
        specialize (Hempty A);
        simpl in *;
        Actor.simplify.
      }
      apply EPP_disjoint_inversion in HEPPB; auto.
      2:{
        specialize (Hempty B);
        simpl in *;
        Actor.simplify.
      }
      eapply IHC; eauto.
Qed.


Lemma EPP_deterministic : forall C A P1 P2,
  EPP A C P1 ->
  EPP A C P2 ->
  P1 = P2.
Proof.
  induction C as [ | I C]; intros A P1 P2 H1 H2.
  * inversion H1; inversion H2; subst; clear H1 H2.
    auto.
  * inversion H1; inversion H2; subst; clear H1 H2; auto;
    try discriminate;
    repeat match goal with
    | [ H : ?A <> ?A |- _ ] => contradiction
    | [ H : ?C _ = ?C _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ = ?C _ _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ _ = ?C _ _ _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ _ _ = ?C _ _ _ _ |- _ ] => inversion H; subst; clear H
    end;
    f_equal; eauto;
    simpl in *; Actor.simplify. 
Qed.

Lemma EPP_disjoint_iff : forall A I C P,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A (I :: C) P <-> EPP A C P.
Proof.
  intros. split; intros Hepp.
  { apply EPP_disjoint_inversion in Hepp; auto. }
  { apply EPP_disjoint; auto. }
Qed.

Lemma EPP_cons_iff : forall A I C1 C2,
  (forall P, EPP A C1 P <-> EPP A C2 P) ->
  (forall P, EPP A (I :: C1) P <-> EPP A (I :: C2) P).
Proof.
  intros A I C1 C2 H P.
  
Admitted.

Lemma step_label_neq : forall refs l D C C' PD,
      step_label C refs l C' ->
      ~ Actor.FSet.In D (Label.actors l) ->
      EPP D C' PD <-> EPP D C PD.
Proof.
  intros ? ? ? ? ? ? Hstep.
  revert D PD.
  induction Hstep; intros D PD;
    subst; simpl; intros Hin; Actor.simplify.
  * rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    rewrite EPP_subst_iff.
    intuition.

  * remember (Var.fresh (ChorEnv.find A' refs)) as q1.
    remember (Var.fresh (Var.Map.add x q1 (ChorEnv.find A' refs))) as q2.
  
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.
    
  * 
    apply EPP_cons_iff.
    intros P. apply IHHstep; auto.
Qed.

Lemma step_send_EPP : forall C A B PA PB v y refs D PD,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    A <> B ->
    forall C',
    step_label C refs (Label.Send A v B) C' ->

    EPP D C' PD
    <->
    (D = A /\ PD = PA)
    \/
    (D = B /\ PD = Process.subst y v PB)
    \/
    (D <> A /\ D <> B /\ EPP D C PD).
Proof.
  intros C A B PA PB v y refs D PD HA HB Hneq.
  induction C as [ | I C];
    intros C' Hstep;
    simpl in *;
    inversion Hstep; subst; clear Hstep.

  * (* substitution happens here *)
    rewrite EPP_subst_iff; auto.
    inversion HA; subst; clear HA; auto.
    2:{ (* contradiction *)
      simpl in *; Actor.simplify.
    }
    inversion HB; subst; clear HB; auto.
    2:{ (* contradiction *)
      simpl in *; Actor.simplify.
    }
    clear H3 H4 H11 H7.
    split; intros H.
    + compare D A; [ | compare D B].
      - left. split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        eapply EPP_deterministic; eauto.
      - right. left.
        split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        f_equal.
        eapply EPP_deterministic; eauto.
      - right. right.
        split; auto. split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        constructor; auto.
        simpl; Actor.simplify.

    + destruct H as [[? ?] | [ [? ?] | [? [? ?]] ]]; subst.
      - right. split; auto.
      - left. split; auto. exists PB. split; auto.
      - right. split; auto.
        apply EPP_disjoint_inversion in H1; auto.
        simpl; Actor.simplify.

  * (* substitution happens later *)
    assert (~ Actor.FSet.In A (Choreography.Insn.actors I)).
    {
      intros Hin;
      match goal with
      | [ H0 : Actor.FSet.Empty _ |- _ ] => 
        apply (H0 A)
      end.
      simpl; Actor.simplify.
    }
    assert (~ Actor.FSet.In B (Choreography.Insn.actors I)).
    {
      intros Hin;
      match goal with
      | [ H0 : Actor.FSet.Empty _ |- _ ] => 
        apply (H0 B)
      end.
      simpl; Actor.simplify.
    }
    clear H1.
    apply EPP_disjoint_inversion in HA; auto.
    apply EPP_disjoint_inversion in HB; auto.

    match goal with
    | [ Hstep0 : step_label C _ _ _ |- _ ] =>
      set (IH := IHC HA HB _ Hstep0); eauto;
      rename Hstep0 into Hstep
    end.

    compare D A; [ | compare D B].
    - (* D = A *)
      transitivity (EPP D C'0 PD).
      { apply EPP_disjoint_iff; auto. }
      rewrite IH.
      intuition.

    - (* D = B *)
      transitivity (EPP D C'0 PD).
      { apply EPP_disjoint_iff; auto. }
      rewrite IH.
      intuition.

    - (* D <> A /\ D <> B *)
      transitivity (EPP D (I :: C) PD).
      2:{ intuition. }

      eapply (step_label_neq refs (Label.Send A v B)).
      2:{ simpl; Actor.simplify. }
      apply StepCons; auto.
      { intros Z. simpl. Actor.simplify.
        intros [[? | ?] Hin']; subst; try contradiction.
      }
Qed.



Lemma subst_neq_inversion : forall A x v D C P,
  D <> A ->
  EPP D (Choreography.subst A x v C) P ->
  EPP D C P.
Proof.
  intros ? ? ? ? C.
  induction C as [ | I C]; intros P Hneq H;
    simpl in H;
    auto.
  inversion H; subst; clear H;
    try match goal with
    | [ Hsubst : _ = Choreography.Insn.subst _ _ _ I |- _ ] =>
    destruct I; simpl in *;
    inversion Hsubst; subst; clear Hsubst
    end.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
    Actor.simplify; auto.
    Var.simplify; auto.
  * constructor; auto.
    Actor.simplify; auto.
  * constructor; auto;
    Actor.simplify; auto;
    Var.simplify; auto.
  * constructor; auto.
    Actor.simplify; auto;
    Var.simplify; auto.
  * Actor.Map.Tactics.compare A t.
    apply EPP_Let; auto.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
  * rewrite actors_subst in *.
    apply EPP_disjoint; auto.
    destruct (Choreography.Insn.rebound_in A x I) eqn:Hbound;
      auto.
Qed.


Lemma step_send_EPP_N : forall C A B PA PB y v N refs C',
    EPP_N C N ->
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    step_label C refs (Label.Send A v B) C' ->
    EPP_N C' (Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N)).
Proof.
  intros C. induction C as [ | I C];
    intros ? ? ? ? ? ? ? ? ? HN HA HB Hv Hstep.
  { inversion Hstep. }
  inversion Hstep; subst; clear Hstep.
  * (* Case 1: substitution happens here *)
    inversion HA; subst; clear HA.
    2:{ simpl in *; Actor.simplify. }
    inversion HB; subst; clear HB.
    2:{ simpl in *; Actor.simplify. }

    intros D PD.
    split; intros H.
    + Actor.simplify. admit.
    + Actor.simplify. admit.
    

  * (* Case 2: substitution happens later *)
    simpl in *.
    rename H1 into Hempty; simpl in Hempty.
    assert (HinA : ~ Actor.FSet.In A (Choreography.Insn.actors I)).
    { intros H; apply (Hempty A); Actor.simplify. }
    assert (HinB : ~ Actor.FSet.In B (Choreography.Insn.actors I)).
    { intros H; apply (Hempty B); Actor.simplify. }


  intros D PD. split.
  * intros Hmaps.
    Actor.simplify.
    destruct Hmaps as [[? ?] | Hmaps];
      subst.
    + (* D = A *)
      eapply step_send_complete in Hstep; eauto.
      inversion Hstep; subst; clear Hstep.
    inversion HA; subst; clear HA.
      2:{

      }
      inversion HB; subst; clear HB.
Qed.

Lemma step_send_EPP_B : forall C A B PA PB v y,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    EPP B (step_send A B C) (Process.subst y v PB).
Proof.
  intros C. induction C as [ | I C];
    intros ? ? ? ? ? ? HA HB;
    simpl.
  { inversion HB. }

  inversion HA; subst; clear HA;
  inversion HB; subst; clear HB;
    simpl in *; Actor.simplify.
  { apply EPP_subst_eq; auto. }

  destruct I;
    try (
      apply EPP_disjoint; auto;
      simpl in *; Var.simplify;
      eapply IHC; eauto;
        fail
    ).
    
  simpl in *.
  Actor.simplify.
  apply EPP_disjoint; simpl; Actor.simplify.
  eapply IHC; eauto.
Qed.


Lemma step_send_EPP_other : forall C D A B PD,
        D <> A ->
        D <> B ->
        EPP D (step_send A B C) PD <-> EPP D C PD.
Proof.
    intros C D A B.
    induction C as [ | I C];
        intros PD HDA HDB.
    { simpl. reflexivity. }
    simpl. split; intros H.
    * destruct (Actor.FSet.mem D (Choreography.Insn.actors I))
      eqn:Hin;
        [ apply Actor.Map.FSetProperties.mem_iff in Hin
        | apply Actor.Map.FSetProperties.not_mem_iff in Hin ].

      + destruct I;
            simpl in Hin; Actor.simplify;
            try (
              try destruct Hin; subst; Actor.simplify;
              inversion H; subst; clear H; Actor.simplify;
              try constructor; auto; apply IHC; auto;
              fail
            ).

      + assert (EPP D (step_send A B C) PD).
        {
          destruct I;
            simpl in Hin; Actor.simplify;
            try (
              inversion H; subst; clear H; Actor.simplify;
              fail
            ).
          apply subst_neq_inversion in H; auto.
          apply IHC; auto.
        }
        apply EPP_disjoint; auto.
        eapply IHC; auto.

    * inversion H; subst; clear H;
      try (
        Actor.simplify;
        constructor; auto;
        rewrite IHC; auto;
        fail
      ).
      rewrite <- IHC in *; auto.
      destruct I;
        simpl in *; Actor.simplify;
        try (
          apply EPP_disjoint; simpl; [ Actor.simplify | eauto];
          fail
        ).
      apply EPP_subst_neq; auto.
      rewrite <- IHC; eauto.
Qed.


Lemma step_send_EPP_N : forall A B C PA PB y v N,
    EPP_N C N ->
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    EPP_N (step_send A B C) (Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N)).
Proof.
    intros A B C PA PB y v N EPPN EPPA EPPB.
    intros D PD.
    specialize (EPPN D PD) as EPPN_D.
    assert (EPP A (step_send A B C) PA).
    { eapply step_send_EPP_A; eauto. }
    assert (EPP B (step_send A B C) (Process.subst y v PB)).
    { eapply step_send_EPP_B; eauto. }
    split; intros HIn.
    * Actor.simplify.
      destruct HIn as [[? ?] | [? [[? HIn] | [? HIn]]]];
        subst; auto.
      (* case 3: A <> D /\ B <> D *)
      eapply step_send_EPP_other; auto.
      apply EPPN_D; auto.

    * Actor.simplify.
      compare A D.
      {
        Actor.simplify.
        left. split; auto.
        eapply EPP_deterministic; eauto.
      }
      right. split; auto.
      compare B D.
      {
        left. split; auto.
        eapply EPP_deterministic; eauto.
      }
      right. split; auto.
      {
        apply EPPN_D.
        apply step_send_EPP_other in HIn; auto.
      }
Qed.
      

(*
Lemma send_complete : forall C A v y B PA PB,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    exists C', 
        (forall cfg,
            Choreography.step (C, cfg) (Label.Send A v B) (C', cfg))
        /\ EPP A C' PA
        /\ EPP B C' (Process.subst y v PB)
        /\ forall D PD, D <> A -> D <> B -> EPP D C' PD <-> EPP D C PD.
Proof.
    induction C as [ | I C'];
        intros A v y B PA PB HEPPA HEPPB Hval.
    { contradict HEPPA. simpl; inversion 1. }
    destruct I as   [ (*Send*) A0 v0 B0 y0
                    | (*EPR*)  A0 x0 B0 y0
                    | (*Let*)  A0 x0 e0
                    | (*Let!*) A0 x0 e0
                    | (*LetPair *) A0 x0 y0 e0
    ].
    * inversion HEPPA; inversion HEPPB; subst;
        try contradiction.
      + exists (Choreography.subst B y v C').
        split; [ | split; [ | split]].
        2:{ apply EPP_subst_neq; auto. }
        2:{ apply EPP_subst_eq; auto. }
        { constructor; auto. }
        {
            intros D PD HDA0 HDB0.
        }

      +  destruct (IHC' A v y B PA PB) as [C0' [IHEPPA [IHEPPB IHC0']]]; auto.
         exists (Choreography.Insn.Send A0 v0 B0 y0 :: C0'); intros.
         repeat split; intros.
         { apply EPP_send_other; auto. }
         { apply EPP_send_other; auto. }
         {
            apply Choreography.Delay; auto.
            intros D.
            rewrite Actor.FSetFacts.inter_iff.
            simpl.
            repeat rewrite Actor.FSetFacts.add_iff.
            repeat rewrite Actor.FSetFacts.singleton_iff.
            intros [[? | ?] [? | ?]]; subst; contradiction.
         }
    * (* TODO *)

Admitted.
*)

(** Return the choreography C' such that 
    C -(Local A)-> C'
*)
Fixpoint step_local A (C : Choreography.t) : Choreography.t :=
  match C with
  | [] => []
  | Choreography.Insn.Let B x v :: C' =>
    if Actor.eq_dec A B then Choreography.subst A x v C'
    else (Choreography.Insn.Let B x v) :: step_local A C'
  | Choreography.Insn.LetBang B x v :: C' =>
    if Actor.eq_dec A B
    then match v with
         | Expr.Bang v => Choreography.subst A x v C'
         | _ => []
         end
    else (Choreography.Insn.LetBang B x v) :: step_local A C'
  | Choreography.Insn.LetPair B x1 x2 v :: C' =>
    if Actor.eq_dec A B
    then match v with
         | Expr.Pair v1 v2 => Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C)
         | _ => []
         end
    else (Choreography.Insn.LetPair B x1 x2 v) :: step_local A C'
  | I0 :: C' => I0 :: step_local A C'
  end.

Lemma step_let_complete : forall C A x v P,
    EPP A C (Insn.Let x v :: P) ->
    Expr.Val v ->
    forall refs cfg,
        Choreography.step C refs cfg (Label.Loc A) (step_local A C) refs cfg.
Proof.
  induction C as [ | I C]; intros A x v P HEPP Hv refs cfg.
  { exfalso. inversion HEPP. }
  inversion HEPP; subst; clear HEPP.
  * simpl. Actor.simplify.
    apply Choreography.LetB; auto.
  * 
  
Lemma step_local_not_in :
  step_local A (I :: C)


(** Return the choreography C' such that C, refs, cfg' -(EPR A x B y)-> C' in the configuration cfg *)
Fixpoint step_epr A B refs cfg (C : Choreography.t) : Choreography.t :=
    match C with
    | [] => []
    | Choreography.Insn.EPR A0 x0 B0 y0 :: C' =>
        match Actor.eq_dec A A0, Actor.eq_dec B B0 with
        | left _, left _ => 
            match ChorEnv.epr A B refs cfg with
            | (q1,q2,refs',cfg') =>
                Choreography.subst A x0 (Expr.Var q1)
                (Choreography.subst B y0 (Expr.Var q2)
                C')
            end
        | _, _ =>
            Choreography.Insn.EPR A0 x0 B0 y0 :: (step_epr A B refs cfg C')
        end
    | I' :: C' => I' :: step_epr A B refs cfg C'
    end.

Lemma step_epr_complete : forall C A x y B PA PB,
    EPP A C (Insn.EPR x B :: PA) ->
    EPP B C (Insn.EPR y A :: PB) ->
    forall refs cfg q1 q2 refs' cfg',
        ChorEnv.epr A B refs cfg = (q1,q2,refs', cfg') ->
        Choreography.step   C refs cfg
                            (Label.EPR A B)
                            (step_epr A B refs cfg C) refs' cfg'.
Admitted.

Lemma step_epr_EPP_N : forall A B C PA PB x y N refs cfg q1 q2 refs' cfg',
    EPP_N C N ->
    EPP A C (Insn.EPR x B :: PA) ->
    EPP B C (Insn.EPR y A :: PB) ->
    ChorEnv.epr A B refs cfg = (q1, q2, refs', cfg') ->
    EPP_N (step_epr A B refs cfg C)
        (Actor.Map.add A (Process.subst x (Expr.Var q1) PA)
            (Actor.Map.add B (Process.subst y (Expr.Var q2) PB) N)).
Admitted.

Theorem completeness : forall N refs cfg l N' refs' cfg',

    Network.step N refs cfg l N' refs' cfg' ->

    forall C,
    EPP_N C N ->
    exists C', EPP_N C' N' /\
                Choreography.step C refs cfg l C' refs' cfg'.
Proof.
    intros N refs cfg l N' refs' cfg' Hstep.
    induction Hstep; intros C HEPP; subst.
  
    * (* local step *)


    * (* send *)
      apply HEPP in H0; destruct H0 as [_ HEPPA].
      apply HEPP in H1; destruct H1 as [_ HEPPB].
      exists (step_send A B C).
      split.
      { apply step_send_EPP_N; auto. }
      { eapply step_send_complete; eauto. }

    * (* EPR *) 
      apply HEPP in H0; destruct H0 as [_ HEPPA].
      apply HEPP in H1; destruct H1 as [_ HEPPB].
      exists (step_epr A B refs cfg C).
      split.
      { eapply step_epr_EPP_N; eauto. }
      { eapply step_epr_complete; eauto. }

Admitted.
