(*
  ClockedLTL_NonMTL.v

  A non-MTL instance of the abstract theorem, and counterexamples showing
  that the polarity condition [atom_ok] cannot be dropped.

  The clock type is [unit] (one clock).  Formulas are clocked LTL formulas
  written directly: no MTL formula, no translation T.

    Instance (b = false, preservation clock):
        phi = G (c <= 5)
        accepted words = exactly the words whose consecutive timestamps are
                         at most 5 apart  (gap_bound_instance).

    Counterexamples (the abstract theorem WITHOUT its ClassC hypothesis):
      - preservation clock tested with a lower bound:  G (c >= 3)
      - restart clock tested with an upper bound:      G (c <= 5)
    In both, the back-end contract holds, the word is in L_timed, and the
    compiled automaton rejects it.
*)
Require Import Arith Lia List Bool Reals Lra ZArith.
Import ListNotations.
Open Scope R_scope.
Require MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Require ClockedLTL_Abstract.
Module C := MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Module G := ClockedLTL_Abstract.

(* ------------------------------------------------------------------ *)
(* One clock                                                          *)
(* ------------------------------------------------------------------ *)

Definition kdec : forall x y : unit, {x = y} + {x <> y}.
Proof. intros [] []. left. reflexivity. Defined.

(* [b = true]: the clock is a restart clock; [b = false]: preservation. *)
Definition kst (b : bool) : unit -> bool := fun _ => b.
Definition kall : list unit := [tt].
Lemma kall_complete : forall x : unit, In x kall.
Proof. intros []. left. reflexivity. Qed.

Definition at_le (d : R) : G.latom unit := @G.LCLe unit tt d.
Definition at_ge (d : R) : G.latom unit := @G.LCGe unit tt d.

(* G a  =  false R a *)
Definition Gf (a : G.latom unit) : G.ltl unit :=
  @G.LRelease unit (@G.LFalse unit) (@G.LAtom unit a).

(* One-state Buchi automaton for G a. *)
Definition loopA (a : G.latom unit) : G.PBuchi unit :=
  {| G.pb_nstates := 1%nat;
     G.pb_init := 0%nat;
     G.pb_trans := [ {| G.pt_src := 0%nat; G.pt_label := [(a, true)];
                        G.pt_tgt := 0%nat |} ];
     G.pb_accepting := [0%nat] |}.

Lemma loopA_correct :
  forall a (s : G.pword unit),
    G.PBA_accepts (loopA a) s <-> G.psat s 0%nat (Gf a).
Proof.
  intros a s. split.
  - intros [run [Hinit [Hsteps Hacc]]].
    simpl. intros j _. left.
    destruct (Hsteps j) as [_ [t [Ht [_ [_ Hf]]]]].
    simpl in Ht. destruct Ht as [<- | []].
    simpl in Hf. inversion Hf as [|? ? Hh _]; subst. exact Hh.
  - intro H. simpl in H.
    exists (fun _ => 0%nat). split; [reflexivity|]. split.
    + intro i. split; [simpl; lia|].
      eexists. split; [left; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      constructor; [|constructor].
      destruct (H i (Nat.le_0_l i)) as [Hh | [k [_ Hf]]]; [exact Hh | contradiction].
    + intro n. exists n. split; [lia | left; reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* A concrete timed word: event i at time i                           *)
(* ------------------------------------------------------------------ *)

Lemma nat_ge_real : forall d : R, exists n : nat, d <= INR n.
Proof.
  intro d. destruct (archimed d) as [H1 _].
  destruct (Rle_dec d 0) as [H|H].
  - exists 0%nat. simpl. lra.
  - exists (Z.to_nat (up d)).
    assert (Hz : (0 <= up d)%Z) by (apply le_IZR; simpl; lra).
    rewrite INR_IZR_INZ, Z2Nat.id by exact Hz. lra.
Qed.

Lemma unit_word_div :
  forall (i : nat) (d : R), 0 <= d ->
    exists j : nat, (i <= j)%nat /\ d <= INR j - INR i.
Proof.
  intros i d Hd. destruct (nat_ge_real d) as [n Hn].
  exists (i + n)%nat. split; [lia|]. rewrite plus_INR. lra.
Qed.

Definition unit_word : C.timed_word :=
  {| C.tw_action := fun _ => 0%nat;
     C.tw_time := INR;
     C.tw_time_nonnegative := pos_INR;
     C.tw_time_mono := fun i => le_INR _ _ (Nat.le_succ_diag_r i);
     C.tw_time_divergent := unit_word_div |}.

Lemma unit_delta : forall i, C.delta unit_word i = 1.
Proof.
  intro i. unfold C.delta. cbn [C.tw_time unit_word]. rewrite S_INR. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Timed language of G (c <= 5)                                       *)
(* ------------------------------------------------------------------ *)

Lemma Ltimed_le_iff :
  forall w, G.L_timed (Gf (at_le 5)) w <-> forall i, C.delta w i <= 5.
Proof.
  intro w. unfold G.L_timed. split.
  - intros [rho [Hb [[Hnn Hcc] Hl]]] i.
    unfold G.same_base in Hb. subst w.
    simpl in Hl. specialize (Hl (S i) (Nat.le_0_l _)).
    destruct Hl as [Hl | [k [_ Hf]]]; [|contradiction].
    unfold G.c_le in Hl. simpl in Hl.
    pose proof (Hcc i tt) as E. pose proof (Hnn i tt) as N.
    destruct (G.ew_reset rho i tt); lra.
  - intro Hd.
    exists {| G.ew_base := w;
              G.ew_val := fun i _ => match i with O => 0 | S j => C.delta w j end;
              G.ew_reset := fun _ _ => true |}.
    split; [reflexivity|]. split.
    + split.
      * intros [|j] x; simpl; [lra | apply C.delta_nonneg].
      * intros i x. simpl. reflexivity.
    + simpl. intros j _. left. unfold G.c_le. simpl.
      destruct j as [|j]; simpl; [lra | apply Hd].
Qed.

(* ------------------------------------------------------------------ *)
(* Positive instance                                                  *)
(* ------------------------------------------------------------------ *)

Theorem gap_bound_instance :
  forall w : C.timed_word,
    G.TBA_accepts
      (G.compile_abs kdec (kst false) kall_complete
         (Gf (at_le 5)) (loopA (at_le 5))) w
    <-> forall i, C.delta w i <= 5.
Proof.
  intro w. rewrite <- Ltimed_le_iff. symmetry.
  apply (@G.abstract_compile_correct unit kdec (kst false) kall kall_complete
           (Gf (at_le 5)) (loopA (at_le 5)) w).
  - intros a Ha. simpl in Ha. destruct Ha as [<- | []]. reflexivity.
  - intros s _. apply loopA_correct.
Qed.

(* ------------------------------------------------------------------ *)
(* What a run of a compiled loop automaton looks like                 *)
(* ------------------------------------------------------------------ *)

Lemma tba_facts :
  forall (b : bool) (a : G.latom unit) (cc : G.clock_constraint unit)
         (w : C.timed_word),
    G.is_ext a = true ->
    (forall x, a <> G.LRst x) ->
    (forall x, a <> G.LUnch x) ->
    G.atom_to_guard a = Some cc ->
    G.TBA_accepts
      (G.compile_abs kdec (kst b) kall_complete (Gf a) (loopA a)) w ->
    exists rho : G.ext_word unit,
      G.same_base rho w /\ G.clock_consistent rho /\
      (forall i, G.clock_constraint_holds rho i cc) /\
      (forall i, G.ew_reset rho i tt = true <-> b = false).
Proof.
  intros b a cc w Hext HnR HnU Hg [rho [Hb [Hc [run [Hinit [Hsteps Hacc]]]]]].
  exists rho. split; [exact Hb|]. split; [exact Hc|].
  set (F := G.ltl_atoms (Gf a)).
  set (L := filter (G.keep_lit kdec (kst b) kall_complete F) [(a, true)]).
  assert (HL2 : forall p, In p L -> p = (a, true)).
  { intros p Hp. unfold L in Hp. apply filter_In in Hp.
    destruct Hp as [Hp _]. destruct Hp as [<- | []]. reflexivity. }
  assert (HF : In a F) by (unfold F; simpl; left; reflexivity).
  assert (HL1 : In (a, true) L).
  { unfold L. apply filter_In. split; [left; reflexivity|].
    unfold G.keep_lit. simpl. rewrite Hext. simpl.
    apply (proj2 (G.in_atoms_iff kdec (kst b) kall_complete a F)). exact HF. }
  assert (Hstep : forall i, G.clock_constraint_holds rho i cc /\
                            (G.ew_reset rho i tt = true <-> b = false)).
  { intro i. destruct (Hsteps i) as [_ [ct [Hct [_ [_ Hen]]]]].
    unfold G.compile_abs, G.complete in Hct. cbn [G.tba_transitions] in Hct.
    apply in_map_iff in Hct. destruct Hct as [t1 [<- Ht1]].
    unfold G.relax in Ht1. cbn [G.pb_trans] in Ht1.
    apply in_map_iff in Ht1. destruct Ht1 as [t2 [<- Ht2]].
    apply filter_In in Ht2. destruct Ht2 as [Ht2 _].
    unfold loopA in Ht2. cbn [G.pb_trans] in Ht2.
    destruct Ht2 as [<- | []].
    destruct Hen as [_ [Hgd Hr]].
    unfold G.complete_trans, G.relax_trans in Hgd, Hr.
    cbn [G.bt_guard G.bt_resets G.pt_label] in Hgd, Hr.
    change (filter (G.keep_lit kdec (kst b) kall_complete F) [(a, true)])
      with L in Hgd, Hr.
    split.
    - rewrite Forall_forall in Hgd.
      assert (Hin : In (G.atom_to_guard a)
                       (map (@G.atom_to_guard unit) (G.pos_atoms L))).
      { apply in_map. unfold G.pos_atoms. apply in_map_iff.
        exists (a, true). split; [reflexivity|].
        apply filter_In. split; [exact HL1 | reflexivity]. }
      pose proof (Hgd _ Hin) as Hh. rewrite Hg in Hh. exact Hh.
    - specialize (Hr tt).
      rewrite Hr. rewrite G.in_comp_resets.
      unfold kst. destruct b.
      + split; [intro H; exfalso | intro H; discriminate H].
        pose proof (HL2 _ H) as E. inversion E. exact (HnR tt (eq_sym H1)).
      + split; [intros _; reflexivity | intros _].
        intro H. pose proof (HL2 _ H) as E. inversion E.
        exact (HnU tt (eq_sym H1)). }
  split; intro i; apply Hstep.
Qed.

(* ------------------------------------------------------------------ *)
(* Counterexample 1: preservation clock, lower-bound test             *)
(* ------------------------------------------------------------------ *)

Theorem atom_ok_necessary_preservation :
  (forall s : G.pword unit, G.action_consistent s ->
     (G.PBA_accepts (loopA (at_ge 3)) s <-> G.psat s 0%nat (Gf (at_ge 3)))) /\
  ~ G.ClassC (kst false) (Gf (at_ge 3)) /\
  G.L_timed (Gf (at_ge 3)) unit_word /\
  ~ G.TBA_accepts
      (G.compile_abs kdec (kst false) kall_complete
         (Gf (at_ge 3)) (loopA (at_ge 3))) unit_word.
Proof.
  split; [|split; [|split]].
  - intros s _. apply loopA_correct.
  - intro H. assert (Hok : G.atom_ok (kst false) (at_ge 3)).
    { apply H. simpl. left. reflexivity. }
    unfold G.atom_ok, at_ge, kst in Hok. simpl in Hok. discriminate Hok.
  - exists {| G.ew_base := unit_word; G.ew_val := fun i _ => 3 + INR i;
              G.ew_reset := fun _ _ => false |}.
    split; [reflexivity|]. split.
    + split.
      * intros i x. simpl. pose proof (pos_INR i). lra.
      * intros i x. cbn [G.ew_val G.ew_reset G.ew_base]. rewrite unit_delta, S_INR. lra.
    + simpl. intros j _. left. unfold G.c_ge. simpl. pose proof (pos_INR j). lra.
  - intro Hacc.
    destruct (@tba_facts false (at_ge 3)
                {| G.guard_clock := tt; G.guard_comparison := G.CGe;
                   G.guard_bound := 3 |} unit_word
                eq_refl) as [rho [Hb [[Hnn Hcc] [Hg Hr]]]];
      try (intros x E; discriminate E); try reflexivity; try exact Hacc.
    unfold G.same_base in Hb.
    pose proof (Hg 1%nat) as H1. unfold G.clock_constraint_holds in H1.
    simpl in H1.
    pose proof (Hcc 0%nat tt) as E.
    assert (Hr0 : G.ew_reset rho 0%nat tt = true) by (apply Hr; reflexivity).
    rewrite Hr0, Hb, unit_delta in E. simpl in E. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Counterexample 2: restart clock, upper-bound test                  *)
(* ------------------------------------------------------------------ *)

Theorem atom_ok_necessary_restart :
  (forall s : G.pword unit, G.action_consistent s ->
     (G.PBA_accepts (loopA (at_le 5)) s <-> G.psat s 0%nat (Gf (at_le 5)))) /\
  ~ G.ClassC (kst true) (Gf (at_le 5)) /\
  G.L_timed (Gf (at_le 5)) unit_word /\
  ~ G.TBA_accepts
      (G.compile_abs kdec (kst true) kall_complete
         (Gf (at_le 5)) (loopA (at_le 5))) unit_word.
Proof.
  split; [|split; [|split]].
  - intros s _. apply loopA_correct.
  - intro H. assert (Hok : G.atom_ok (kst true) (at_le 5)).
    { apply H. simpl. left. reflexivity. }
    unfold G.atom_ok, at_le, kst in Hok. simpl in Hok. discriminate Hok.
  - apply Ltimed_le_iff. intro i. rewrite unit_delta. lra.
  - intro Hacc.
    destruct (@tba_facts true (at_le 5)
                {| G.guard_clock := tt; G.guard_comparison := G.CLe;
                   G.guard_bound := 5 |} unit_word
                eq_refl) as [rho [Hb [[Hnn Hcc] [Hg Hr]]]];
      try (intros x E; discriminate E); try reflexivity; try exact Hacc.
    unfold G.same_base in Hb.
    assert (Hno : forall i, G.ew_reset rho i tt = false).
    { intro i. destruct (G.ew_reset rho i tt) eqn:E; [|reflexivity].
      exfalso. assert (true = false) by (apply (proj1 (Hr i)); exact E). discriminate. }
    assert (Hgrow : forall i, INR i <= G.ew_val rho i tt).
    { induction i as [|i IH]; [simpl; pose proof (Hnn 0%nat tt); lra|].
      rewrite (Hcc i tt), Hno, Hb, unit_delta, S_INR. lra. }
    pose proof (Hg 6%nat) as H6. unfold G.clock_constraint_holds in H6.
    simpl in H6. pose proof (Hgrow 6%nat) as G6.
    replace (INR 6) with 6 in G6 by (simpl; lra). lra.
Qed.

Print Assumptions gap_bound_instance.
Print Assumptions atom_ok_necessary_preservation.
Print Assumptions atom_ok_necessary_restart.
