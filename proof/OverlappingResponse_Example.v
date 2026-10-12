(* A checked instance of the verified MTL-to-TBA theorem. The general
   theorem keeps its propositional-backend contract explicit; this example
   proves that contract for one Spot-generated automaton transcription. *)

From Stdlib Require Import List Reals Lra Lia ClassicalDescription.
Import ListNotations.
Require Import MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Require Import EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.

Open Scope R_scope.

Definition ALARM : Action := 1%nat.
Definition HANDLED : Action := 2%nat.

(* G (alarm -> F_[0,3] handled).  MUle is the derived non-strict
   bounded-until operator; its hatted primitive owns the formula-keyed clock. *)
Definition alarm_response : mtl :=
  MR MFalse
    (MOr (MNotAtom ALARM)
         (MUle 3 MTrue (MAtom HANDLED))).

Lemma alarm_response_well_formed : well_formed alarm_response.
Proof.
  unfold alarm_response, MUle.
  simpl.
  repeat split; try exact I; lra.
Qed.

Lemma alarm_response_has_one_primitive_clock :
  timed_subformulas alarm_response =
    [MUhatLe 3 MTrue (MAtom HANDLED)].
Proof.
  vm_compute.
  reflexivity.
Qed.

(* The clock used by the one bounded response clause. *)
Definition alarm_clock : Clock alarm_response.
Proof.
  refine (exist _ (MUhatLe 3 MTrue (MAtom HANDLED)) _).
  rewrite alarm_response_has_one_primitive_clock.
  simpl. auto.
Defined.

Lemma alarm_clock_of :
  clock_of alarm_response (MUhatLe 3 MTrue (MAtom HANDLED)) =
    Some alarm_clock.
Proof.
  unfold alarm_clock.
  apply clock_of_mem.
Qed.

(* Explicit expansion of T alarm_response. The names in the Spot input file
   are abbreviations for these four Rocq propositions. *)
Definition alarm_response_spot_ltl : ltl alarm_response :=
  LRelease LFalse
    (LOr (LAtom (LNAct ALARM))
      (LOr (LAtom (LAct HANDLED))
        (LAnd LTrue
          (LNext
            (LUntil
              (LAnd (LAtom (LCLe alarm_clock 3))
                (LAnd (LAtom (LUnch alarm_clock)) LTrue))
              (LAnd (LAtom (LCLe alarm_clock 3))
                (LAtom (LAct HANDLED)))))))).

Lemma alarm_response_T_eq : T alarm_response = alarm_response_spot_ltl.
Proof.
  change
    (T_at (root:=alarm_response) []
      (MR MFalse
        (MOr (MNotAtom ALARM)
          (MUle 3 MTrue (MAtom HANDLED)))) =
     alarm_response_spot_ltl).
  unfold alarm_response_spot_ltl.
  cbn [T_at MUle].
  rewrite alarm_clock_of.
  reflexivity.
Qed.

(* Spot 2.16, with --buchi -S, produces this three-state state-based Büchi
   automaton from examples/spot/alarm_response_backend.ltl. The DOT graph is
   manually transcribed here; its disjunctive edge is split into two cubes. *)
Definition alarm_response_spot_backend : PBuchi alarm_response :=
  {| pb_nstates := 3;
     pb_init := 0;
     pb_trans :=
       [{| pt_src := 0; pt_label := [(LAct HANDLED, true)]; pt_tgt := 0 |};
        {| pt_src := 0; pt_label := [(LNAct ALARM, true)]; pt_tgt := 0 |};
        {| pt_src := 0;
           pt_label := [(LAct HANDLED, false); (LNAct ALARM, false)];
           pt_tgt := 1 |};
        {| pt_src := 1;
           pt_label := [(LCLe alarm_clock 3, true); (LAct HANDLED, true)];
           pt_tgt := 0 |};
        {| pt_src := 1;
           pt_label := [(LCLe alarm_clock 3, true); (LAct HANDLED, false);
                        (LUnch alarm_clock, true)];
           pt_tgt := 2 |};
        {| pt_src := 2;
           pt_label := [(LCLe alarm_clock 3, true); (LAct HANDLED, true)];
           pt_tgt := 0 |};
        {| pt_src := 2;
           pt_label := [(LCLe alarm_clock 3, true); (LAct HANDLED, false);
                        (LUnch alarm_clock, true)];
           pt_tgt := 2 |}];
     pb_accepting := [0%nat; 1%nat] |}.

Definition alarm_spot_not_alarm (s : pword alarm_response) (i : nat) : Prop :=
  s i (LNAct ALARM).
Definition alarm_spot_handled (s : pword alarm_response) (i : nat) : Prop :=
  s i (LAct HANDLED).
Definition alarm_spot_clock_le (s : pword alarm_response) (i : nat) : Prop :=
  s i (LCLe alarm_clock 3).
Definition alarm_spot_unchanged (s : pword alarm_response) (i : nat) : Prop :=
  s i (LUnch alarm_clock).

Definition alarm_spot_p (s : pword alarm_response) (i : nat) : Prop :=
  alarm_spot_clock_le s i /\ alarm_spot_unchanged s i.
Definition alarm_spot_q (s : pword alarm_response) (i : nat) : Prop :=
  alarm_spot_clock_le s i /\ alarm_spot_handled s i.

Definition alarm_response_backend_spec (s : pword alarm_response) : Prop :=
  forall i,
    alarm_spot_not_alarm s i \/ alarm_spot_handled s i \/
    exists j,
      (S i <= j)%nat /\ alarm_spot_q s j /\
      forall k, (S i <= k < j)%nat -> alarm_spot_p s k.

Definition alarm_spot_step
    (s : pword alarm_response) (i src tgt : nat) : Prop :=
  match src, tgt with
  | 0, 0 => alarm_spot_not_alarm s i \/ alarm_spot_handled s i
  | 0, 1 => ~ alarm_spot_not_alarm s i /\ ~ alarm_spot_handled s i
  | 1, 0 | 2, 0 => alarm_spot_q s i
  | 1, 2 | 2, 2 => alarm_spot_p s i /\ ~ alarm_spot_handled s i
  | _, _ => False
  end.

Definition alarm_spot_trigger
    (s : pword alarm_response) (i : nat) : Prop :=
  ~ alarm_spot_not_alarm s i /\ ~ alarm_spot_handled s i.

Definition alarm_spot_next_state
    (s : pword alarm_response) (q i : nat) : nat :=
  match q with
  | 0 => if excluded_middle_informative (alarm_spot_trigger s i)
         then 1%nat else 0%nat
  | 1 | 2 => if excluded_middle_informative (alarm_spot_q s i)
            then 0%nat else 2%nat
  | _ => 0%nat
  end.

Fixpoint alarm_spot_run (s : pword alarm_response) (i : nat) : nat :=
  match i with
  | O => 0%nat
  | S n => alarm_spot_next_state s (alarm_spot_run s n) n
  end.

Definition alarm_spot_edge
    (s : pword alarm_response) (i src tgt : nat) : Prop :=
  exists t,
    In t (pb_trans alarm_response_spot_backend) /\
    pt_src t = src /\ pt_tgt t = tgt /\
    Forall (plit_holds s i) (pt_label t).

Lemma alarm_spot_run_lt3 :
  forall (s : pword alarm_response) i,
    (alarm_spot_run s i < 3)%nat.
Proof.
  intros s i. induction i as [|i IH].
  - simpl. lia.
  - change (alarm_spot_next_state s (alarm_spot_run s i) i < 3)%nat.
    destruct (alarm_spot_run s i) as [|[|[|q]]] eqn:Hrun.
    + unfold alarm_spot_next_state.
      destruct (excluded_middle_informative (alarm_spot_trigger s i)); simpl; lia.
    + unfold alarm_spot_next_state.
      destruct (excluded_middle_informative (alarm_spot_q s i)); simpl; lia.
    + unfold alarm_spot_next_state.
      destruct (excluded_middle_informative (alarm_spot_q s i)); simpl; lia.
    + unfold alarm_spot_next_state. simpl. lia.
Qed.

Lemma alarm_spot_run_pending_has_trigger :
  forall (s : pword alarm_response) n,
    alarm_spot_run s n = 1%nat \/ alarm_spot_run s n = 2%nat ->
    exists r,
      (r < n)%nat /\ alarm_spot_trigger s r /\
      forall k, (S r <= k < n)%nat -> ~ alarm_spot_q s k.
Proof.
  intros s n. induction n as [|n IH]; intros Hpending.
  - simpl in Hpending. lia.
  - cbn [alarm_spot_run] in Hpending.
    unfold alarm_spot_next_state in Hpending.
    destruct (alarm_spot_run s n) as [|[|[|q]]] eqn:Hprev.
    + destruct (excluded_middle_informative (alarm_spot_trigger s n))
        as [Htrigger|Hnottrigger]; simpl in Hpending.
      * unfold alarm_spot_trigger in Htrigger.
        destruct Htrigger as [Hnot Hhandled].
        exists n. split; [lia|]. split; [split; assumption|].
        intros k Hk. lia.
      * simpl in Hpending. lia.
    + destruct (excluded_middle_informative (alarm_spot_q s n))
        as [Hq|Hnotq]; simpl in Hpending.
      * lia.
      * destruct (IH (or_introl eq_refl)) as [r [Hrn [Htrigger Hnoq]]].
        exists r. split; [lia|]. split; [exact Htrigger|].
        intros k Hk.
        destruct (Nat.eq_dec k n) as [->|Hneq].
        -- exact Hnotq.
        -- apply Hnoq. lia.
    + destruct (excluded_middle_informative (alarm_spot_q s n))
        as [Hq|Hnotq]; simpl in Hpending.
      * lia.
      * destruct (IH (or_intror eq_refl)) as [r [Hrn [Htrigger Hnoq]]].
        exists r. split; [lia|]. split; [exact Htrigger|].
        intros k Hk.
        destruct (Nat.eq_dec k n) as [->|Hneq].
        -- exact Hnotq.
        -- apply Hnoq. lia.
    + simpl in Hpending. lia.
Qed.

Lemma alarm_response_spot_ltl_language :
  forall s : pword alarm_response,
    psat s 0 alarm_response_spot_ltl <-> alarm_response_backend_spec s.
Proof.
  intros s.
  unfold alarm_response_spot_ltl, alarm_response_backend_spec.
  unfold alarm_spot_not_alarm, alarm_spot_handled,
    alarm_spot_clock_le, alarm_spot_unchanged,
    alarm_spot_p, alarm_spot_q.
  cbn [psat].
  split.
  - intros H i.
    specialize (H i (Nat.le_0_l i)).
    destruct H as [Hbody | [k [_ Hfalse]]]; [|contradiction].
    destruct Hbody as [Hnot | [Hhandled | [Htrue Huntil]]].
    + left. exact Hnot.
    + right. left. exact Hhandled.
    + right. right.
      destruct Huntil as [j [Hj [Hq Hp]]].
      exists j. split; [exact Hj|].
      split; [exact Hq|].
      intros k Hk. specialize (Hp k Hk).
      destruct Hp as [Hc [Hu _]]. exact (conj Hc Hu).
  - intros H j Hj.
    destruct (H j) as [Hnot | [Hhandled | [j0 [Hj0 [Hq Hp]]]]].
    + left. left. exact Hnot.
    + left. right. left. exact Hhandled.
    + left. right. right. split; [exact I|].
      exists j0. split; [exact Hj0|].
      split; [exact Hq|].
      intros k Hk. specialize (Hp k Hk).
      destruct Hp as [Hc Hu]. exact (conj Hc (conj Hu I)).
Qed.

Lemma alarm_spot_edge_00 :
  forall (s : pword alarm_response) i,
    alarm_spot_edge s i 0 0 <->
    alarm_spot_not_alarm s i \/ alarm_spot_handled s i.
Proof.
  intros s i.
  unfold alarm_spot_edge, alarm_response_spot_backend,
    alarm_spot_not_alarm, alarm_spot_handled.
  split.
  - intros [t [Hin [Hsrc [Htgt Hlabels]]]].
    simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hnil]]]]]]];
      try contradiction; subst t; simpl in Hsrc, Htgt; try congruence;
      unfold plit_holds in Hlabels; simpl in Hlabels;
      inversion Hlabels; subst; tauto.
  - intros [Hnot|Hhandled].
    + exists {| pt_src := 0; pt_label := [(LNAct ALARM, true)]; pt_tgt := 0 |}.
      split; [simpl; right; left; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      simpl. constructor; [unfold plit_holds; simpl; exact Hnot|constructor].
    + exists {| pt_src := 0; pt_label := [(LAct HANDLED, true)]; pt_tgt := 0 |}.
      split; [simpl; left; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      simpl. constructor; [unfold plit_holds; simpl; exact Hhandled|constructor].
Qed.

Lemma alarm_spot_edge_01 :
  forall (s : pword alarm_response) i,
    alarm_spot_edge s i 0 1 <->
    ~ alarm_spot_not_alarm s i /\ ~ alarm_spot_handled s i.
Proof.
  intros s i.
  unfold alarm_spot_edge, alarm_response_spot_backend,
    alarm_spot_not_alarm, alarm_spot_handled.
  split.
  - intros [t [Hin [Hsrc [Htgt Hlabels]]]].
    simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hnil]]]]]]];
      try contradiction; subst t; simpl in Hsrc, Htgt; try congruence;
      unfold plit_holds in Hlabels;
      repeat match goal with H : Forall _ _ |- _ => inversion H; subst end;
      simpl in *; tauto.
  - intros [Hnot Hhandled].
    exists {| pt_src := 0; pt_label := [(LAct HANDLED, false);
                                          (LNAct ALARM, false)]; pt_tgt := 1 |}.
    split; [simpl; right; right; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    simpl. constructor.
    + unfold plit_holds. simpl. exact Hhandled.
    + constructor; [unfold plit_holds; simpl; exact Hnot|constructor].
Qed.

Lemma alarm_spot_edge_10 :
  forall (s : pword alarm_response) i,
    alarm_spot_edge s i 1 0 <-> alarm_spot_q s i.
Proof.
  intros s i.
  unfold alarm_spot_edge, alarm_response_spot_backend, alarm_spot_q,
    alarm_spot_clock_le, alarm_spot_handled.
  split.
  - intros [t [Hin [Hsrc [Htgt Hlabels]]]].
    simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hnil]]]]]]];
      try contradiction; subst t; simpl in Hsrc, Htgt; try congruence;
      unfold plit_holds in Hlabels;
      repeat match goal with H : Forall _ _ |- _ => inversion H; subst end;
      simpl in *; tauto.
  - intros [Hclock Hhandled].
    exists {| pt_src := 1; pt_label := [(LCLe alarm_clock 3, true);
                                          (LAct HANDLED, true)]; pt_tgt := 0 |}.
    split; [simpl; right; right; right; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    simpl. constructor.
    + unfold plit_holds. simpl. exact Hclock.
    + constructor; [unfold plit_holds; simpl; exact Hhandled|constructor].
Qed.

Lemma alarm_spot_edge_12 :
  forall (s : pword alarm_response) i,
    alarm_spot_edge s i 1 2 <->
    alarm_spot_p s i /\ ~ alarm_spot_handled s i.
Proof.
  intros s i.
  unfold alarm_spot_edge, alarm_response_spot_backend,
    alarm_spot_p, alarm_spot_clock_le, alarm_spot_unchanged,
    alarm_spot_handled.
  split.
  - intros [t [Hin [Hsrc [Htgt Hlabels]]]].
    simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hnil]]]]]]];
      try contradiction; subst t; simpl in Hsrc, Htgt; try congruence;
      unfold plit_holds in Hlabels;
      repeat match goal with H : Forall _ _ |- _ => inversion H; subst end;
      simpl in *; tauto.
  - intros [[Hclock Hunch] Hhandled].
    exists {| pt_src := 1; pt_label := [(LCLe alarm_clock 3, true);
                                          (LAct HANDLED, false);
                                          (LUnch alarm_clock, true)]; pt_tgt := 2 |}.
    split; [simpl; right; right; right; right; left; reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    simpl. constructor.
    + unfold plit_holds. simpl. exact Hclock.
    + constructor.
      * unfold plit_holds. simpl. exact Hhandled.
      * constructor; [unfold plit_holds; simpl; exact Hunch|constructor].
Qed.

Lemma alarm_spot_edge_20 :
  forall (s : pword alarm_response) i,
    alarm_spot_edge s i 2 0 <-> alarm_spot_q s i.
Proof.
  intros s i.
  unfold alarm_spot_edge, alarm_response_spot_backend, alarm_spot_q,
    alarm_spot_clock_le, alarm_spot_handled.
  split.
  - intros [t [Hin [Hsrc [Htgt Hlabels]]]].
    simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hnil]]]]]]];
      try contradiction; subst t; simpl in Hsrc, Htgt; try congruence;
      unfold plit_holds in Hlabels;
      repeat match goal with H : Forall _ _ |- _ => inversion H; subst end;
      simpl in *; tauto.
  - intros [Hclock Hhandled].
    exists {| pt_src := 2; pt_label := [(LCLe alarm_clock 3, true);
                                          (LAct HANDLED, true)]; pt_tgt := 0 |}.
    split; [simpl; right; right; right; right; right; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    simpl. constructor.
    + unfold plit_holds. simpl. exact Hclock.
    + constructor; [unfold plit_holds; simpl; exact Hhandled|constructor].
Qed.

Lemma alarm_spot_edge_22 :
  forall (s : pword alarm_response) i,
    alarm_spot_edge s i 2 2 <->
    alarm_spot_p s i /\ ~ alarm_spot_handled s i.
Proof.
  intros s i.
  unfold alarm_spot_edge, alarm_response_spot_backend,
    alarm_spot_p, alarm_spot_clock_le, alarm_spot_unchanged,
    alarm_spot_handled.
  split.
  - intros [t [Hin [Hsrc [Htgt Hlabels]]]].
    simpl in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hnil]]]]]]];
      try contradiction; subst t; simpl in Hsrc, Htgt; try congruence;
      unfold plit_holds in Hlabels;
      repeat match goal with H : Forall _ _ |- _ => inversion H; subst end;
      simpl in *; tauto.
  - intros [[Hclock Hunch] Hhandled].
    exists {| pt_src := 2; pt_label := [(LCLe alarm_clock 3, true);
                                          (LAct HANDLED, false);
                                          (LUnch alarm_clock, true)]; pt_tgt := 2 |}.
    split; [simpl; right; right; right; right; right; right; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    simpl. constructor.
    + unfold plit_holds. simpl. exact Hclock.
    + constructor.
      * unfold plit_holds. simpl. exact Hhandled.
      * constructor; [unfold plit_holds; simpl; exact Hunch|constructor].
Qed.

Lemma alarm_spot_edge_iff :
  forall (s : pword alarm_response) i src tgt,
    alarm_spot_edge s i src tgt <-> alarm_spot_step s i src tgt.
Proof.
  intros s i src tgt.
  destruct src as [|[|[|src]]]; destruct tgt as [|[|[|tgt]]];
    cbn [alarm_spot_step];
    try exact (alarm_spot_edge_00 s i);
    try exact (alarm_spot_edge_01 s i);
    try exact (alarm_spot_edge_10 s i);
    try exact (alarm_spot_edge_12 s i);
    try exact (alarm_spot_edge_20 s i);
    try exact (alarm_spot_edge_22 s i).
  all: unfold alarm_spot_edge, alarm_response_spot_backend; simpl.
  all: split;
    [intros [t [Hin [Hsrc [Htgt Hlabels]]]];
     simpl in Hin;
     destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hnil]]]]]]];
     try contradiction; subst t; simpl in Hsrc, Htgt; congruence
    | contradiction].
Qed.

Lemma alarm_spot_pending_continues :
  forall (s : pword alarm_response) i,
    alarm_response_backend_spec s ->
    (alarm_spot_run s i = 1%nat \/ alarm_spot_run s i = 2%nat) ->
    ~ alarm_spot_q s i ->
    alarm_spot_p s i /\ ~ alarm_spot_handled s i.
Proof.
  intros s i Hspec Hpending Hnotq.
  destruct (alarm_spot_run_pending_has_trigger s i Hpending)
    as [r [Hri [Htrigger Hnoq]]].
  unfold alarm_spot_trigger in Htrigger.
  destruct Htrigger as [Hnotalarm_r Hhandled_r].
  destruct (Hspec r) as [Hnotalarm | [Hhandled | [j [Hj [Hqj Hp]]]]].
  - contradiction.
  - contradiction.
  - assert (Hrij : (S r <= i)%nat) by lia.
    assert (Hij : (i < j)%nat).
    { assert (i < j \/ j <= i)%nat by lia.
      destruct H as [Hlt|Hge]; [exact Hlt|].
      assert (j < i \/ j = i)%nat by lia.
      destruct H as [Hji|Heq].
      - specialize (Hnoq j (conj Hj Hji)). contradiction.
      - subst j. contradiction. }
    pose proof (Hp i (conj Hrij Hij)) as Hpi.
    split; [exact Hpi|].
    intro Hhandled_i.
    apply Hnotq. unfold alarm_spot_q.
    destruct Hpi as [Hclock _]. split; assumption.
Qed.

Lemma alarm_spot_step_next :
  forall (s : pword alarm_response) i src tgt,
    (src < 3)%nat -> alarm_spot_step s i src tgt ->
    alarm_spot_next_state s src i = tgt.
Proof.
  intros s i src tgt Hsrc Hstep.
  destruct src as [|[|[|src]]]; try lia.
  - destruct tgt as [|[|[|tgt]]].
    + cbn [alarm_spot_step] in Hstep. unfold alarm_spot_next_state. simpl.
      destruct (excluded_middle_informative (alarm_spot_trigger s i)) as [Ht|Ht].
      * unfold alarm_spot_trigger in Ht. tauto.
      * reflexivity.
    + cbn [alarm_spot_step] in Hstep. unfold alarm_spot_next_state. simpl.
      destruct (excluded_middle_informative (alarm_spot_trigger s i)) as [Ht|Ht].
      * reflexivity.
      * unfold alarm_spot_trigger in Ht. tauto.
    + cbn [alarm_spot_step] in Hstep. contradiction.
    + cbn [alarm_spot_step] in Hstep. contradiction.
  - destruct tgt as [|[|[|tgt]]].
    + cbn [alarm_spot_step] in Hstep. unfold alarm_spot_next_state. simpl.
      destruct (excluded_middle_informative (alarm_spot_q s i)) as [Hq|Hq].
      * reflexivity.
      * contradiction.
    + cbn [alarm_spot_step] in Hstep. contradiction.
    + cbn [alarm_spot_step] in Hstep. unfold alarm_spot_next_state. simpl.
      destruct (excluded_middle_informative (alarm_spot_q s i)) as [Hq|Hq].
      * unfold alarm_spot_q in Hq.
        destruct Hstep as [[Hclock _] Hnothandled]. tauto.
      * reflexivity.
    + cbn [alarm_spot_step] in Hstep. contradiction.
  - destruct tgt as [|[|[|tgt]]].
    + cbn [alarm_spot_step] in Hstep. unfold alarm_spot_next_state. simpl.
      destruct (excluded_middle_informative (alarm_spot_q s i)) as [Hq|Hq].
      * reflexivity.
      * contradiction.
    + cbn [alarm_spot_step] in Hstep. contradiction.
    + cbn [alarm_spot_step] in Hstep. unfold alarm_spot_next_state. simpl.
      destruct (excluded_middle_informative (alarm_spot_q s i)) as [Hq|Hq].
      * unfold alarm_spot_q in Hq.
        destruct Hstep as [[Hclock _] Hnothandled]. tauto.
      * reflexivity.
    + cbn [alarm_spot_step] in Hstep. contradiction.
Qed.

Lemma alarm_spot_run_step_of_spec :
  forall (s : pword alarm_response),
    alarm_response_backend_spec s ->
    forall i, alarm_spot_step s i (alarm_spot_run s i)
      (alarm_spot_run s (S i)).
Proof.
  intros s Hspec i.
  change (alarm_spot_step s i (alarm_spot_run s i)
    (alarm_spot_next_state s (alarm_spot_run s i) i)).
  pose proof (alarm_spot_run_lt3 s i) as Hlt.
  destruct (alarm_spot_run s i) as [|[|[|q]]] eqn:Hrun; try lia.
  - unfold alarm_spot_step, alarm_spot_next_state. simpl.
    destruct (excluded_middle_informative (alarm_spot_trigger s i))
      as [Htrigger|Htrigger].
    + exact Htrigger.
    + unfold alarm_spot_trigger in Htrigger. tauto.
  - unfold alarm_spot_step, alarm_spot_next_state. simpl.
    destruct (excluded_middle_informative (alarm_spot_q s i))
      as [Hq|Hq].
    + exact Hq.
    + destruct (alarm_spot_pending_continues s i Hspec
        (or_introl Hrun) Hq) as [Hp Hnothandled].
      exact (conj Hp Hnothandled).
  - unfold alarm_spot_step, alarm_spot_next_state. simpl.
    destruct (excluded_middle_informative (alarm_spot_q s i))
      as [Hq|Hq].
    + exact Hq.
    + destruct (alarm_spot_pending_continues s i Hspec
        (or_intror Hrun) Hq) as [Hp Hnothandled].
      exact (conj Hp Hnothandled).
Qed.

Lemma alarm_spot_run_succ :
  forall (s : pword alarm_response) n,
    alarm_spot_run s (S n) = alarm_spot_next_state s (alarm_spot_run s n) n.
Proof. reflexivity. Qed.

Lemma alarm_spot_run_pending_q_reaches_zero :
  forall (s : pword alarm_response),
    (forall i, alarm_spot_step s i (alarm_spot_run s i)
      (alarm_spot_run s (S i))) ->
    forall n d,
      (alarm_spot_run s n = 1%nat \/ alarm_spot_run s n = 2%nat) ->
      alarm_spot_q s (n + d)%nat ->
      exists z, (n < z)%nat /\ (z <= S (n + d))%nat /\
        alarm_spot_run s z = 0%nat.
Proof.
  intros s Hsteps n d. revert n.
  induction d as [|d IH]; intros n Hpending Hqfuture.
  - replace (n + 0)%nat with n in Hqfuture by lia.
    exists (S n). split; [lia|]. split; [lia|].
    rewrite alarm_spot_run_succ. unfold alarm_spot_next_state.
    destruct Hpending as [Hone|Htwo].
    + rewrite Hone. destruct (excluded_middle_informative (alarm_spot_q s n)) as [Hq|Hq];
        [reflexivity|contradiction].
    + rewrite Htwo. destruct (excluded_middle_informative (alarm_spot_q s n)) as [Hq|Hq];
        [reflexivity|contradiction].
  - destruct (classic (alarm_spot_q s n)) as [Hqn|Hqn].
    + exists (S n). split; [lia|]. split; [simpl; lia|].
      rewrite alarm_spot_run_succ. unfold alarm_spot_next_state.
      destruct Hpending as [Hone|Htwo].
      * rewrite Hone. destruct (excluded_middle_informative (alarm_spot_q s n)); [reflexivity|contradiction].
      * rewrite Htwo. destruct (excluded_middle_informative (alarm_spot_q s n)); [reflexivity|contradiction].
    + assert (Hactive : alarm_spot_run s n = 1%nat \/
                       alarm_spot_run s n = 2%nat) by exact Hpending.
      pose proof (Hsteps n) as Hstep.
      assert (Hnext : alarm_spot_run s (S n) = 2%nat).
      { rewrite alarm_spot_run_succ. unfold alarm_spot_next_state.
        destruct Hactive as [Hone|Htwo].
        - rewrite Hone.
          destruct (excluded_middle_informative (alarm_spot_q s n)); [contradiction|reflexivity].
        - rewrite Htwo.
          destruct (excluded_middle_informative (alarm_spot_q s n)); [contradiction|reflexivity]. }
      assert (Hpn : alarm_spot_p s n).
      { rewrite Hnext in Hstep.
        destruct Hactive as [Hone|Htwo]; rewrite Hone in Hstep || rewrite Htwo in Hstep;
          cbn [alarm_spot_step] in Hstep; tauto. }
      assert (Hfuture' : alarm_spot_q s (S n + d)%nat).
      { replace (S n + d)%nat with (n + S d)%nat by lia. exact Hqfuture. }
      destruct (IH (S n) (or_intror Hnext) Hfuture') as [z [Hnz [Hz Hzero]]].
      exists z. split; [lia|]. split; [replace (S (n + S d)) with (S (S n + d)) by lia; exact Hz|].
      exact Hzero.
Qed.

Lemma alarm_spot_run_accepting_of_spec :
  forall (s : pword alarm_response),
    alarm_response_backend_spec s ->
    forall n, exists j, (n <= j)%nat /\
      In (alarm_spot_run s j) [0%nat; 1%nat].
Proof.
  intros s Hspec n.
  pose proof (alarm_spot_run_step_of_spec s Hspec) as Hsteps.
  pose proof (alarm_spot_run_lt3 s n) as Hlt.
  destruct (alarm_spot_run s n) as [|[|[|q]]] eqn:Hrun; try lia.
  - exists n. split; [lia|]. simpl. left. symmetry. exact Hrun.
  - destruct (alarm_spot_run_pending_has_trigger s n (or_introl Hrun))
      as [r [Hrn [Htrigger Hnoq]]].
    unfold alarm_spot_trigger in Htrigger. destruct Htrigger as [Hnot Hhandled].
    destruct (Hspec r) as [Hnot_r|[Hhandled_r|[j [Hj [Hqj Hp]]]]].
    + contradiction.
    + contradiction.
    + assert (Hnj : (n <= j)%nat).
      { assert (n <= j \/ j < n)%nat by lia.
        destruct H as [H|H]; [exact H|].
        exfalso. apply (Hnoq j (conj Hj H)). exact Hqj. }
      assert (Hqdist : alarm_spot_q s (n + (j - n))%nat).
      { replace (n + (j - n))%nat with j by lia. exact Hqj. }
      destruct (alarm_spot_run_pending_q_reaches_zero s Hsteps n (j - n)
        (or_introl Hrun) Hqdist) as [z [Hnz [_ Hz0]]].
      exists z. split; [lia|]. simpl. left. symmetry. exact Hz0.
  - destruct (alarm_spot_run_pending_has_trigger s n (or_intror Hrun))
      as [r [Hrn [Htrigger Hnoq]]].
    unfold alarm_spot_trigger in Htrigger. destruct Htrigger as [Hnot Hhandled].
    destruct (Hspec r) as [Hnot_r|[Hhandled_r|[j [Hj [Hqj Hp]]]]].
    + contradiction.
    + contradiction.
    + assert (Hnj : (n <= j)%nat).
      { assert (n <= j \/ j < n)%nat by lia.
        destruct H as [H|H]; [exact H|].
        exfalso. apply (Hnoq j (conj Hj H)). exact Hqj. }
      assert (Hqdist : alarm_spot_q s (n + (j - n))%nat).
      { replace (n + (j - n))%nat with j by lia. exact Hqj. }
      destruct (alarm_spot_run_pending_q_reaches_zero s Hsteps n (j - n)
        (or_intror Hrun) Hqdist) as [z [Hnz [_ Hz0]]].
      exists z. split; [lia|]. simpl. left. symmetry. exact Hz0.
Qed.

Lemma alarm_spot_pending_endpoint_until :
  forall (s : pword alarm_response),
    (forall i, alarm_spot_step s i (alarm_spot_run s i)
      (alarm_spot_run s (S i))) ->
    forall n d,
      (alarm_spot_run s n = 1%nat \/ alarm_spot_run s n = 2%nat) ->
      (alarm_spot_run s (S n + d)%nat = 0%nat \/
       alarm_spot_run s (S n + d)%nat = 1%nat) ->
      exists j,
        (n <= j)%nat /\ alarm_spot_q s j /\
        (forall k, (n <= k < j)%nat -> alarm_spot_p s k).
Proof.
  intros s Hsteps n d. revert n.
  induction d as [|d IH]; intros n Hpending Haccept.
  - replace (S n + 0)%nat with (S n)%nat in Haccept by lia.
    destruct Hpending as [Hone|Htwo].
    + rewrite alarm_spot_run_succ in Haccept.
      unfold alarm_spot_next_state in Haccept. rewrite Hone in Haccept.
      destruct (excluded_middle_informative (alarm_spot_q s n)) as [Hq|Hq].
      * exists n. split; [lia|]. split; [exact Hq|]. intros k Hk. lia.
      * simpl in Haccept. destruct Haccept as [H0|H1]; discriminate.
    + rewrite alarm_spot_run_succ in Haccept.
      unfold alarm_spot_next_state in Haccept. rewrite Htwo in Haccept.
      destruct (excluded_middle_informative (alarm_spot_q s n)) as [Hq|Hq].
      * exists n. split; [lia|]. split; [exact Hq|]. intros k Hk. lia.
      * simpl in Haccept. destruct Haccept as [H0|H1]; discriminate.
  - destruct Hpending as [Hone|Htwo].
    + destruct (classic (alarm_spot_q s n)) as [Hq|Hq].
      * exists n. split; [lia|]. split; [exact Hq|]. intros k Hk. lia.
      * assert (Hnext : alarm_spot_run s (S n) = 2%nat).
        { rewrite alarm_spot_run_succ. unfold alarm_spot_next_state.
          rewrite Hone. destruct (excluded_middle_informative (alarm_spot_q s n));
            [contradiction|reflexivity]. }
        pose proof (Hsteps n) as Hstep.
        rewrite Hone, Hnext in Hstep. cbn [alarm_spot_step] in Hstep.
        destruct Hstep as [Hpn _].
        assert (Haccept' : alarm_spot_run s (S (S n + d)) = 0%nat \/
                           alarm_spot_run s (S (S n + d)) = 1%nat).
         { replace (S (S n + d))%nat with (S n + S d)%nat by lia. exact Haccept. }
        destruct (IH (S n) (or_intror Hnext) Haccept')
          as [j [Hnj [Hqj Hpj]]].
        exists j. split; [lia|]. split; [exact Hqj|].
        intros k Hk. destruct (Nat.eq_dec k n) as [->|Hneq].
        -- exact Hpn.
        -- apply Hpj. lia.
    + destruct (classic (alarm_spot_q s n)) as [Hq|Hq].
      * exists n. split; [lia|]. split; [exact Hq|]. intros k Hk. lia.
      * assert (Hnext : alarm_spot_run s (S n) = 2%nat).
        { rewrite alarm_spot_run_succ. unfold alarm_spot_next_state.
          rewrite Htwo. destruct (excluded_middle_informative (alarm_spot_q s n));
            [contradiction|reflexivity]. }
        pose proof (Hsteps n) as Hstep.
        rewrite Htwo, Hnext in Hstep. cbn [alarm_spot_step] in Hstep.
        destruct Hstep as [Hpn _].
        assert (Haccept' : alarm_spot_run s (S (S n + d)) = 0%nat \/
                           alarm_spot_run s (S (S n + d)) = 1%nat).
         { replace (S (S n + d))%nat with (S n + S d)%nat by lia. exact Haccept. }
        destruct (IH (S n) (or_intror Hnext) Haccept')
          as [j [Hnj [Hqj Hpj]]].
        exists j. split; [lia|]. split; [exact Hqj|].
        intros k Hk. destruct (Nat.eq_dec k n) as [->|Hneq].
        -- exact Hpn.
        -- apply Hpj. lia.
Qed.

Lemma alarm_spot_run_pending_acceptance_until :
  forall (s : pword alarm_response),
    (forall i, alarm_spot_step s i (alarm_spot_run s i)
      (alarm_spot_run s (S i))) ->
    (forall n, exists j, (n <= j)%nat /\
      In (alarm_spot_run s j) [0%nat; 1%nat]) ->
    forall n,
      (alarm_spot_run s n = 1%nat \/ alarm_spot_run s n = 2%nat) ->
      exists j,
        (n <= j)%nat /\ alarm_spot_q s j /\
        (forall k, (n <= k < j)%nat -> alarm_spot_p s k).
Proof.
  intros s Hsteps Hacc n Hpending.
  destruct (Hacc (S n)) as [m [Hnm Hmember]].
  assert (Haccept : alarm_spot_run s m = 0%nat \/
                    alarm_spot_run s m = 1%nat).
  { simpl in Hmember.
    destruct Hmember as [H0|[H1|[]]].
    - left. symmetry. exact H0.
    - right. symmetry. exact H1. }
  assert (Hdist : (S n + (m - S n))%nat = m) by lia.
  rewrite <- Hdist in Haccept.
  eapply alarm_spot_pending_endpoint_until; eauto.
Qed.

Lemma alarm_spot_run_acceptance_implies_spec :
  forall (s : pword alarm_response),
    (forall i, alarm_spot_step s i (alarm_spot_run s i)
      (alarm_spot_run s (S i))) ->
    (forall n, exists j, (n <= j)%nat /\
      In (alarm_spot_run s j) [0%nat; 1%nat]) ->
    alarm_response_backend_spec s.
Proof.
  intros s Hsteps Hacc i.
  destruct (classic (alarm_spot_not_alarm s i)) as [Hnot|Hnot].
  - left. exact Hnot.
  - destruct (classic (alarm_spot_handled s i)) as [Hhandled|Hhandled].
    + right. left. exact Hhandled.
    + right. right.
      assert (Htrigger : alarm_spot_trigger s i) by (unfold alarm_spot_trigger; tauto).
      pose proof (alarm_spot_run_lt3 s i) as Hlt.
      destruct (alarm_spot_run s i) as [|[|[|q]]] eqn:Hrun; try lia.
      * assert (Hnext : alarm_spot_run s (S i) = 1%nat).
        { rewrite alarm_spot_run_succ. unfold alarm_spot_next_state. rewrite Hrun.
          destruct (excluded_middle_informative (alarm_spot_trigger s i));
            [reflexivity|contradiction]. }
        destruct (alarm_spot_run_pending_acceptance_until s Hsteps Hacc
          (S i) (or_introl Hnext)) as [j [Hij [Hq HjP]]].
        exists j. split; [exact Hij|]. split; [exact Hq|].
        intros k Hk. apply HjP. exact Hk.
      * destruct (alarm_spot_run_pending_acceptance_until s Hsteps Hacc
          i (or_introl Hrun)) as [j [Hij [Hq HjP]]].
        assert (Hafter : (S i <= j)%nat).
        { destruct (Nat.eq_dec i j) as [Heq|Hneq]; [|lia].
          subst j. unfold alarm_spot_q in Hq. tauto. }
        exists j. split; [exact Hafter|]. split; [exact Hq|].
        intros k Hk. apply HjP. lia.
      * destruct (alarm_spot_run_pending_acceptance_until s Hsteps Hacc
          i (or_intror Hrun)) as [j [Hij [Hq HjP]]].
        assert (Hafter : (S i <= j)%nat).
        { destruct (Nat.eq_dec i j) as [Heq|Hneq]; [|lia].
          subst j. unfold alarm_spot_q in Hq. tauto. }
        exists j. split; [exact Hafter|]. split; [exact Hq|].
        intros k Hk. apply HjP. lia.
Qed.

Theorem alarm_response_spot_backend_contract :
  forall s : pword alarm_response,
    PBA_accepts alarm_response_spot_backend s <->
      psat s 0 (T alarm_response).
Proof.
  intro s. rewrite alarm_response_T_eq.
  split.
  - intro Haccept.
    unfold PBA_accepts, alarm_response_spot_backend in Haccept.
    destruct Haccept as [r [Hr0 [Htrans Hbuchi]]].
    assert (Hsteps_r : forall i,
      alarm_spot_step s i (r i) (r (S i))).
    { intro i.
      destruct (Htrans i) as [Hbound [t [Hin [Hsrc [Htgt Hlabels]]]]].
      apply (proj1 (alarm_spot_edge_iff s i (r i) (r (S i)))).
      exists t. repeat split; assumption. }
    assert (Hsame : forall i, r i = alarm_spot_run s i).
    { intro i. induction i as [|i IHi].
      - simpl in Hr0. exact Hr0.
      - pose proof (Htrans i) as Htrans_i.
        destruct Htrans_i as [Hbound _].
        pose proof (alarm_spot_step_next s i (r i) (r (S i))
          Hbound (Hsteps_r i)) as Hnext.
        rewrite alarm_spot_run_succ.
        rewrite IHi in Hnext. symmetry. exact Hnext. }
    assert (Hsteps : forall i,
      alarm_spot_step s i (alarm_spot_run s i)
        (alarm_spot_run s (S i))).
    { intro i. rewrite <- (Hsame i), <- (Hsame (S i)). apply Hsteps_r. }
    assert (Hbuchi' : forall n, exists j, (n <= j)%nat /\
      In (alarm_spot_run s j) [0%nat; 1%nat]).
    { intro n. destruct (Hbuchi n) as [j [Hnj Hmem]].
      exists j. split; [exact Hnj|]. rewrite <- (Hsame j). exact Hmem. }
    apply (proj2 (alarm_response_spot_ltl_language s)).
    eapply alarm_spot_run_acceptance_implies_spec; eassumption.
  - intro Hltl.
    assert (Hspec : alarm_response_backend_spec s).
    { apply (proj1 (alarm_response_spot_ltl_language s)). exact Hltl. }
    unfold PBA_accepts, alarm_response_spot_backend.
    exists (alarm_spot_run s). split; [reflexivity|].
    split.
    + intro i. split; [apply alarm_spot_run_lt3|].
      pose proof (alarm_spot_run_step_of_spec s Hspec i) as Hstep.
      apply (proj2 (alarm_spot_edge_iff s i
        (alarm_spot_run s i) (alarm_spot_run s (S i)))) in Hstep.
      destruct Hstep as [t [Hin [Hsrc [Htgt Hlabels]]]].
      exists t. repeat split; assumption.
    + apply alarm_spot_run_accepting_of_spec. exact Hspec.
Qed.

(* A concrete infinite timed word extending the overlapping-alarm prefix:
   alarms occur at times 0 and 2, handled occurs at time 4, and all later
   events are neutral. *)
Definition alarm_overlap_action (i : nat) : Action :=
  match i with
  | O => ALARM
  | S O => ALARM
  | S (S O) => HANDLED
  | _ => 0%nat
  end.

(* The two requests are at times 0 and 3/2; one response at time 3 meets
   both deadlines.  Later events are neutral and occur at unit intervals. *)
Definition alarm_overlap_trace : timed_word.
Proof.
  refine {| tw_action := alarm_overlap_action;
            tw_time := fun i => (3 / 2) * INR i |}.
  - intros i. apply Rmult_le_pos; [lra|].
    pose proof (pos_INR i). lra.
  - intros i. rewrite S_INR. nra.
  - intros i d Hd.
    destruct (archimed (d * 2 / 3)) as [Harch _].
    assert ((0 <= up (d * 2 / 3))%Z \/ (up (d * 2 / 3) <= 0)%Z) as Hcase.
    { apply Z.le_ge_cases. }
    destruct Hcase as [Hz | Hz].
    + destruct (IZN (up (d * 2 / 3)) Hz) as [n Hn].
      exists (i + n)%nat.
      split.
      * lia.
      * rewrite plus_INR.
        replace ((3 / 2) * (INR i + INR n) - (3 / 2) * INR i)
          with ((3 / 2) * INR n) by ring.
        rewrite INR_IZR_INZ, <- Hn.
        nra.
    + assert (IZR (up (d * 2 / 3)) <= 0) as Hup_nonpos.
      { apply IZR_le. exact Hz. }
      lra.
Defined.

Lemma alarm_overlap_trace_satisfies :
  msat alarm_overlap_trace 0 alarm_response.
Proof.
  unfold alarm_response, MUle.
  cbn [msat].
  intros i Hi.
  destruct i as [|[|[|i]]].
  - left. right. right. split.
    + exact I.
    + exists 2%nat. split; [lia|]. split.
      * change ((3 / 2) * INR 2 - (3 / 2) * INR 0 <= 3).
        simpl. nra.
      * split.
        -- change (alarm_overlap_action 2 = HANDLED). reflexivity.
        -- intros k Hk. exact I.
  - left. right. right. split.
    + exact I.
    + exists 2%nat. split; [lia|]. split.
      * change ((3 / 2) * INR 2 - (3 / 2) * INR 1 <= 3).
        simpl. nra.
      * split.
        -- change (alarm_overlap_action 2 = HANDLED). reflexivity.
        -- intros k Hk. exact I.
  - left. right. left. change (alarm_overlap_action 2 = HANDLED). reflexivity.
  - left. left. change (alarm_overlap_action (S (S (S i))) <> ALARM).
    unfold alarm_overlap_action, ALARM. discriminate.
Qed.

Definition alarm_trace_action (i : nat) : Action :=
  match i with
  | O => ALARM
  | S O => ALARM
  | S (S O) => HANDLED
  | _ => 0%nat
  end.

Definition alarm_response_trace : timed_word.
Proof.
  refine {| tw_action := alarm_trace_action;
            tw_time := fun i => 2 * INR i |}.
  - intros i. induction i.
    + simpl. lra.
    + rewrite S_INR. nra.
  - intros i. rewrite S_INR. nra.
  - intros i d Hd.
    destruct (archimed (d / 2)) as [Harch _].
    assert ((0 <= up (d / 2))%Z \/ (up (d / 2) <= 0)%Z) as Hcase.
    { apply Z.le_ge_cases. }
    destruct Hcase as [Hz | Hz].
    + destruct (IZN (up (d / 2)) Hz) as [n Hn].
      exists (i + n)%nat.
      split.
      * lia.
      * rewrite plus_INR.
        replace (2 * (INR i + INR n) - 2 * INR i) with (2 * INR n) by ring.
        rewrite INR_IZR_INZ, <- Hn.
        nra.
    + assert (IZR (up (d / 2)) <= 0) as Hup_nonpos.
      { apply IZR_le. exact Hz. }
      lra.
Defined.

Lemma alarm_response_trace_violates :
  ~ msat alarm_response_trace 0 alarm_response.
Proof.
  unfold alarm_response, MUle.
  simpl.
  intros H.
  specialize (H 0%nat ltac:(lia)).
  unfold alarm_trace_action, ALARM, HANDLED in H.
  simpl in H.
  destruct H as [[Hnot_alarm | [Hhandled | [_ Hfuture]]] | Hfalse].
  - apply Hnot_alarm. reflexivity.
  - discriminate.
  - destruct Hfuture as [j [Hafter [Hwithin [Hhandled _]]]].
    destruct j as [|[|[|j]]]; simpl in *; try lia; try lra; discriminate.
  - destruct Hfalse as [k [Hk _]]. lia.
Qed.

(* The proposition-level backend premise for this formula, on all
   propositional words.  MTL_to_TBA_correct_with requires it only on the
   action-consistent words; the all-words form is stronger. *)
Definition alarm_response_backend_contract
    (A : PBuchi alarm_response) : Prop :=
  forall s : pword alarm_response,
    PBA_accepts A s <-> psat s 0 (T alarm_response).

Theorem alarm_response_tba_correct_with :
  forall (A : PBuchi alarm_response) (w : timed_word),
    alarm_response_backend_contract A ->
    msat w 0 alarm_response <-> TBA_accepts (compile_with A) w.
Proof.
  intros A w HA.
    unfold alarm_response_backend_contract in HA.
  eapply MTL_to_TBA_correct_with.
  - (* the contract of the record holds on all propositional words, in
       particular on the action-consistent ones *)
    intros s _. exact (HA s).
  - apply alarm_response_well_formed.
Qed.

Definition alarm_response_spot_tba : TBA alarm_response :=
  compile_with alarm_response_spot_backend.

Theorem alarm_response_spot_tba_correct :
  forall w : timed_word,
    msat w 0 alarm_response <->
      TBA_accepts alarm_response_spot_tba w.
Proof.
  intro w. unfold alarm_response_spot_tba.
  eapply alarm_response_tba_correct_with.
  - exact alarm_response_spot_backend_contract.
Qed.

Corollary alarm_overlap_trace_accepted_by_spot_tba :
  TBA_accepts alarm_response_spot_tba alarm_overlap_trace.
Proof.
  apply (proj1 (alarm_response_spot_tba_correct alarm_overlap_trace)).
  exact alarm_overlap_trace_satisfies.
Qed.

Corollary alarm_response_trace_rejected_by_any_correct_backend :
  forall (A : PBuchi alarm_response),
    alarm_response_backend_contract A ->
    ~ TBA_accepts (compile_with A) alarm_response_trace.
Proof.
  intros A HA Haccept.
  apply alarm_response_trace_violates.
  apply (proj2 (alarm_response_tba_correct_with A alarm_response_trace HA)).
  exact Haccept.
Qed.

Corollary alarm_response_trace_rejected_by_spot_tba :
  ~ TBA_accepts alarm_response_spot_tba alarm_response_trace.
Proof.
  apply alarm_response_trace_rejected_by_any_correct_backend.
  exact alarm_response_spot_backend_contract.
Qed.
