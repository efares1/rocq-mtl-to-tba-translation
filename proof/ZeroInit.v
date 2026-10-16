(*
  ZeroInit.v

  Zero-initialized clocks for the translation of the article.

  The acceptance of a TBA used in the development quantifies the initial
  clock valuation existentially.  Here the initial valuation is fixed to 0.
  The file is added next to the Core and Proof files, which are unchanged:

    - complete_complete_init: reset completion keeps the initial valuation
      of the clock-consistent extended word it starts from (the proof of
      complete_complete of the Core file, with this conclusion added);
    - MTL_to_TBA_correct_with_zero_init: the conditional theorem
      MTL_to_TBA_correct_with with every clock starting at 0.

  Proof idea: the canonical extension of the completeness proof starts at 0,
  the backend step and the relaxation do not involve clocks, and reset
  completion keeps the initial valuation; the converse direction is
  MTL_to_TBA_correct_with, since zero initial clocks are a special case.
*)

Require Import Arith Lia List Bool Reals Lra.
Require Import Classical.
Import ListNotations.
Open Scope R_scope.

Set Implicit Arguments.

Require Import MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Require Import EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.

Section ZeroInit.

Variable root : mtl.

(* The proof of [complete_complete], with the conclusion that the initial
   valuation is kept. *)
Lemma complete_complete_init :
  forall A (rho : ext_word root),
    clock_consistent rho -> labels_ok A -> PBA_accepts A (word_of rho) ->
    exists rho' : ext_word root,
      ew_base rho' = ew_base rho /\ clock_consistent rho' /\
      (forall x, ew_val rho' 0%nat x = ew_val rho 0%nat x) /\
      TBA_ext_accepts (complete A) rho'.
Proof.
  intros A rho [Hnn Hcc] Hok [run [Hinit [Hsteps Hacc]]].
  set (P := fun i (t : ptransition root) =>
              pt_src t = run i /\ pt_tgt t = run (S i) /\
              Forall (plit_holds (word_of rho) i) (pt_label t)).
  assert (Hex : forall i, exists t, In t (pb_trans A) /\ P i t).
  { intro i. destruct (Hsteps i) as [_ [t [Ht H]]]. exists t. split; assumption. }
  set (lab := fun i => match first_such (P i) (pb_trans A) with
                       | Some t => pt_label t | None => [] end).
  assert (Hlab : forall i, exists t, first_such (P i) (pb_trans A) = Some t /\
                   In t (pb_trans A) /\ P i t /\ lab i = pt_label t).
  { intro i. destruct (first_such_spec (Hex i)) as [t [Hf [Ht HP]]].
    exists t. split; [exact Hf|]. split; [exact Ht|]. split; [exact HP|].
    unfold lab. rewrite Hf. reflexivity. }
  set (r := fun i x => if In_dec (@clock_eq_dec root) x (comp_resets (lab i))
                       then true else false).
  set (rho' := {| ew_base := ew_base rho;
                  ew_val := vals (ew_val rho 0) r (ew_base rho);
                  ew_reset := r |}).
  assert (Hr : forall i x, r i x = true <-> In x (comp_resets (lab i))).
  { intros i x. unfold r. destruct (In_dec _ x _); split; intro H;
      try reflexivity; try assumption; try discriminate; contradiction. }
  (* the literals of the chosen cube hold on rho *)
  assert (Hsat : forall i a b, In (a, b) (lab i) -> plit_holds (word_of rho) i (a, b)).
  { intros i a b Hin. destruct (Hlab i) as [t [_ [_ [[_ [_ Hl]] Heq]]]].
    rewrite Heq in Hin. rewrite Forall_forall in Hl. exact (Hl _ Hin). }
  assert (Hok' : forall i a b, In (a, b) (lab i) -> is_ext a = true ->
                   b = true /\ atom_ok a).
  { intros i a b Hin Hext. destruct (Hlab i) as [t [_ [Ht [_ Heq]]]].
    rewrite Heq in Hin. exact (Hok t a b Ht Hin Hext). }
  (* preservation clocks: smaller values *)
  assert (Hpres : forall x, is_restart x = false ->
                    forall i, vals (ew_val rho 0) r (ew_base rho) i x <= ew_val rho i x).
  { intros x Hx i. induction i as [|j IH]; simpl; [lra|].
    rewrite (Hcc j x). pose proof (delta_positive (ew_base rho) j).
    pose proof (Hnn j x).
    destruct (r j x) eqn:Erj.
    - destruct (ew_reset rho j x); lra.
    - destruct (ew_reset rho j x) eqn:E; [|lra].
      exfalso. assert (Hin : In x (comp_resets (lab j))).
      { apply in_comp_resets. rewrite Hx. intro HU.
        pose proof (Hsat _ _ _ HU) as HU'. unfold plit_holds, word_of in HU'.
        simpl in HU'. unfold unch_at in HU'. congruence. }
      apply Hr in Hin. congruence. }
  (* restart clocks: larger values *)
  assert (Hrest : forall x, is_restart x = true ->
                    forall i, ew_val rho i x <= vals (ew_val rho 0) r (ew_base rho) i x).
  { intros x Hx i. induction i as [|j IH]; simpl; [lra|].
    rewrite (Hcc j x). pose proof (delta_positive (ew_base rho) j).
    pose proof (@vals_nonneg root (ew_val rho 0) r (ew_base rho) (Hnn 0%nat) j x).
    destruct (r j x) eqn:Erj.
    - apply Hr in Erj. apply in_comp_resets in Erj. rewrite Hx in Erj.
      pose proof (Hsat _ _ _ Erj) as HR. unfold plit_holds, word_of in HR.
      simpl in HR. unfold rst_at in HR. rewrite HR. lra.
    - destruct (ew_reset rho j x); lra. }
  exists rho'. split; [reflexivity|]. split; [|split].
  - split.
    + intros i x. apply vals_nonneg. apply Hnn.
    + intros i x. reflexivity.
  - intro x. reflexivity.
  - exists run. split; [exact Hinit|]. split; [|exact Hacc].
    intro i. split; [exact (proj1 (Hsteps i))|].
    destruct (Hlab i) as [t [_ [Ht [[Hs [Hd Hl]] Heq]]]].
    exists (complete_trans t). split; [simpl; apply in_map; exact Ht|].
    split; [exact Hs|]. split; [exact Hd|].
    rewrite Forall_forall in Hl.
    split; [|split].
    + (* actions *)
      unfold label_holds. simpl. apply Forall_forall. intros [q c] Hq.
      apply in_flat_map in Hq. destruct Hq as [[a b] [Hab Hq]].
      pose proof (Hl _ Hab) as H. unfold plit_holds, word_of in H. simpl in H.
      unfold act_lit in Hq. simpl in Hq.
      destruct a as [q0|q0|x d|x d|x d|x d|x|x]; simpl in Hq; try contradiction.
      * destruct Hq as [Hq|[]]. injection Hq as <- <-.
        unfold alit_holds. simpl. destruct b; exact H.
      * destruct Hq as [Hq|[]]. injection Hq as <- <-.
        unfold alit_holds. simpl. destruct b; simpl in *; [exact H|].
        destruct (Nat.eq_dec (tw_action (ew_base rho) i) q0) as [E|E];
          [exact E | contradiction].
    + (* guards *)
      apply Forall_forall. intros o Ho. simpl in Ho.
      apply in_map_iff in Ho. destruct Ho as [a [<- Ha]].
      unfold pos_atoms in Ha. apply in_map_iff in Ha.
      destruct Ha as [[a' b] [Ea Ha]]. simpl in Ea. subst a'.
      apply filter_In in Ha. destruct Ha as [Ha Hb]. simpl in Hb. subst b.
      pose proof (Hl _ Ha) as H. unfold plit_holds, word_of in H. simpl in H.
      assert (Hin' : In (a, true) (lab i)) by (rewrite Heq; exact Ha).
      destruct a as [q|q|x d|x d|x d|x d|x|x]; simpl; try exact I;
        pose proof (proj2 (Hok' i _ _ Hin' eq_refl)) as Hk; simpl in Hk;
        simpl in H; unfold c_le, c_lt, c_ge, c_gt in H.
      * pose proof (Hpres x Hk i). unfold clock_constraint_holds, rho'. simpl. lra.
      * pose proof (Hpres x Hk i). unfold clock_constraint_holds, rho'. simpl. lra.
      * pose proof (Hrest x Hk i). unfold clock_constraint_holds, rho'. simpl. lra.
      * pose proof (Hrest x Hk i). unfold clock_constraint_holds, rho'. simpl. lra.
    + (* resets *)
      intro x. simpl. rewrite Hr, Heq. reflexivity.
Qed.
End ZeroInit.

(* Acceptance with every clock starting at 0. *)
Definition TBA_accepts_zero (root : mtl) (A : TBA root) (w : timed_word) : Prop :=
  exists rho : ext_word root,
    same_base rho w /\
    clock_consistent rho /\
    (forall x, ew_val rho 0%nat x = 0) /\
    TBA_ext_accepts A rho.

Theorem MTL_to_TBA_correct_with_zero_init :
  forall (f : mtl) (A : PBuchi f) (w : timed_word),
    (forall s : pword f, action_consistent s ->
       (PBA_accepts A s <-> psat s 0 (T f))) ->
    well_formed f ->
    (msat w 0 f <-> TBA_accepts_zero (compile_with A) w).
Proof.
  intros f A w HA Hwf. split.
  - intro Hm.
    set (rho := canonical_ext f w).
    assert (Hltl : lsat rho 0 (T f)).
    { unfold rho, T. specialize (node_at_nil f) as Hn.
      apply (canonical_encoding_all w Hwf Hn 0). exact Hm. }
    assert (Hclock : clock_consistent rho) by apply canonical_clock_consistent.
    assert (Hbase : same_base rho w) by apply canonical_same_base.
    apply lsat_psat in Hltl.
    apply (proj2 (HA (word_of rho) (word_of_action_consistent rho))) in Hltl.
    apply (relax_complete (ltl_atoms (T f))) in Hltl.
    destruct (complete_complete_init Hclock (@compile_labels_ok f A) Hltl)
      as [rho' [Hb' [Hc' [Hi' Ha']]]].
    exists rho'. split; [unfold same_base in *; rewrite Hb'; exact Hbase|].
    split; [exact Hc'|]. split; [|exact Ha'].
    intro x. rewrite Hi'. reflexivity.
  - intros [rho [Hbase [Hclock [_ Htba]]]].
    apply (proj2 (MTL_to_TBA_correct_with w HA Hwf)).
    exists rho. split; [exact Hbase|]. split; [exact Hclock|exact Htba].
Qed.
Print Assumptions MTL_to_TBA_correct_with_zero_init.
