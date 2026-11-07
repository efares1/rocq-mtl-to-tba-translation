(*
  ClockedLTL_Abstract.v

  Level 2 generalisation.  The relaxation / reset-completion pipeline is
  developed over an ABSTRACT clock type, with no reference to MTL.

  Parameters of the development:
    - [Clock]       : a type of clocks, with decidable equality;
    - [is_restart]  : classifies each clock as a restart clock (lower-bound
                      tests, reset markers) or a preservation clock
                      (upper-bound tests, unchanged markers);
    - [all_clocks]  : an enumeration of the clocks (finiteness).

  The syntax of clocked LTL, its semantics over extended words, the Buchi
  and timed-Buchi automata, relaxation and reset completion, and the lemmas
  relax_sound / relax_complete / complete_sound / complete_complete are
  re-derived from the Core file with every [Clock root] replaced by the
  abstract [Clock].  Timed words (nondecreasing timestamps) come from the
  Core file, qualified as C.

  The final theorem [abstract_compile_correct] has no MTL content.  Linking
  it to the MTL translation is done in a separate file.
*)
Require Import Arith Lia List Bool Reals Lra.
Require Import Classical Description.
Require MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Module C := MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Import ListNotations.
Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "All".

Section Abstract.

Variable Clock : Type.
Variable clock_eq_dec : forall x y : Clock, {x = y} + {x <> y}.
Variable is_restart : Clock -> bool.
Variable all_clocks : list Clock.
Hypothesis all_clocks_complete : forall x : Clock, In x all_clocks.

(* Boolean reflection of a proposition, by classical reasoning.  It is used
   only inside proofs, to build witness reset functions; it is never part of
   the extracted code. *)

Definition bool_of_prop (P : Prop) : {b : bool | b = true <-> P}.
Proof.
  apply constructive_definite_description.
  destruct (classic P) as [H|H].
  - exists true. split; [tauto|].
    intros b Hb. destruct b; [reflexivity|]. apply Hb in H. discriminate.
  - exists false. split; [split; [discriminate | contradiction]|].
    intros b Hb. destruct b; [|reflexivity].
    exfalso. apply H. apply Hb. reflexivity.
Defined.

Definition decide_b (P : Prop) : bool := proj1_sig (bool_of_prop P).

Lemma decide_b_spec : forall P, decide_b P = true <-> P.
Proof. intro P. exact (proj2_sig (bool_of_prop P)). Qed.

(* ====================================================================== *)

Record ext_word : Type := {
  ew_base : C.timed_word;
  ew_val : nat -> Clock -> R;
  ew_reset : nat -> Clock -> bool
}.

Definition same_base (rho : ext_word) (w : C.timed_word) : Prop :=
  ew_base rho = w.

Definition clock_consistent (rho : ext_word) : Prop :=
  (forall i x, 0 <= ew_val rho i x) /\
  (forall i x,
      ew_val rho (S i) x =
      if ew_reset rho i x
      then C.delta (ew_base rho) i
      else ew_val rho i x + C.delta (ew_base rho) i).

Definition c_le (rho : ext_word) (x : Clock) (d : R) (i : nat) : Prop :=
  ew_val rho i x <= d.

Definition c_lt (rho : ext_word) (x : Clock) (d : R) (i : nat) : Prop :=
  ew_val rho i x < d.

Definition c_ge (rho : ext_word) (x : Clock) (d : R) (i : nat) : Prop :=
  d <= ew_val rho i x.

Definition c_gt (rho : ext_word) (x : Clock) (d : R) (i : nat) : Prop :=
  d < ew_val rho i x.

Definition rst_at (rho : ext_word) (x : Clock) (i : nat) : Prop :=
  ew_reset rho i x = true.

Definition unch_at (rho : ext_word) (x : Clock) (i : nat) : Prop :=
  ew_reset rho i x = false.

(* ====================================================================== *)

Inductive latom : Type :=
| LAct  : nat -> latom
| LNAct : nat -> latom
| LCLe  : Clock -> R -> latom
| LCLt  : Clock -> R -> latom
| LCGe  : Clock -> R -> latom
| LCGt  : Clock -> R -> latom
| LRst  : Clock -> latom
| LUnch : Clock -> latom.

Inductive ltl : Type :=
| LTrue    : ltl
| LFalse   : ltl
| LAtom    : latom -> ltl
| LAnd     : ltl -> ltl -> ltl
| LOr      : ltl -> ltl -> ltl
| LNext    : ltl -> ltl
| LUntil   : ltl -> ltl -> ltl
| LRelease : ltl -> ltl -> ltl.

Definition LF (p : ltl) : ltl :=
  LUntil LTrue p.

Definition LG (p : ltl) : ltl :=
  LRelease LFalse p.

Definition LW (p q : ltl) : ltl :=
  LOr (LUntil p q) (LG p).

Definition LGF (p : ltl) : ltl :=
  LG (LF p).

Definition atom_sat (rho : ext_word) (i : nat) (a : latom) : Prop :=
  match a with
  | LAct p  => C.tw_action (ew_base rho) i = p
  | LNAct p => C.tw_action (ew_base rho) i <> p
  | LCLe x d => c_le rho x d i
  | LCLt x d => c_lt rho x d i
  | LCGe x d => c_ge rho x d i
  | LCGt x d => c_gt rho x d i
  | LRst x => rst_at rho x i
  | LUnch x => unch_at rho x i
  end.

Fixpoint lsat (rho : ext_word) (i : nat) (f : ltl) : Prop :=
  match f with
  | LTrue => True
  | LFalse => False
  | LAtom a => atom_sat rho i a
  | LAnd p q => lsat rho i p /\ lsat rho i q
  | LOr p q => lsat rho i p \/ lsat rho i q
  | LNext p => lsat rho (S i) p

  | LUntil p q =>
      exists j,
        (i <= j)%nat /\
        lsat rho j q /\
        (forall k, (i <= k < j)%nat -> lsat rho k p)

  | LRelease p q =>
      forall j,
        (i <= j)%nat ->
        lsat rho j q \/
        exists k, (i <= k < j)%nat /\ lsat rho k p
  end.

(* A Buchi letter contains only the visible, untimed action. *)
Record letter : Type := {
  letter_action : nat
}.

Definition letter_of (rho : ext_word) (i : nat) : letter :=
  {| letter_action := C.tw_action (ew_base rho) i |}.

(* nat literals: (a, true) stands for the action a, (a, false) for any
   action other than a.  Transition labels are lists of action literals. *)
Definition alit : Type := (nat * bool)%type.

Definition alit_holds (p : nat) (l : alit) : Prop :=
  if snd l then p = fst l else p <> fst l.

Definition label_holds (ls : list alit) (le : letter) : Prop :=
  Forall (alit_holds (letter_action le)) ls.

(* The LTL-to-Buchi back-end treats the atoms of the extended alphabet as
   independent propositions.  Its input is a propositional word: a truth
   value for every atom at every position. *)
Definition pword : Type := nat -> latom -> Prop.

Fixpoint psat (s : pword) (i : nat) (f : ltl) : Prop :=
  match f with
  | LTrue => True
  | LFalse => False
  | LAtom a => s i a
  | LAnd p q => psat s i p /\ psat s i q
  | LOr p q => psat s i p \/ psat s i q
  | LNext p => psat s (S i) p
  | LUntil p q =>
      exists j,
        (i <= j)%nat /\ psat s j q /\ (forall k, (i <= k < j)%nat -> psat s k p)
  | LRelease p q =>
      forall j,
        (i <= j)%nat ->
        psat s j q \/ exists k, (i <= k < j)%nat /\ psat s k p
  end.

(* The propositional word of an extended word: the truth values of its
   atoms. *)
Definition word_of (rho : ext_word) : pword := fun i a => atom_sat rho i a.

Fixpoint ltl_atoms (f : ltl) : list latom :=
  match f with
  | LTrue | LFalse => []
  | LAtom a => [a]
  | LAnd p q | LOr p q | LUntil p q | LRelease p q => ltl_atoms p ++ ltl_atoms q
  | LNext p => ltl_atoms p
  end.

(* Literals: (a, true) is the atom a, (a, false) its negation.  The
   transitions of the automaton returned by the back-end are labelled by
   cubes, i.e. lists of literals. *)
Definition plit : Type := (latom * bool)%type.

Definition plit_holds (s : pword) (i : nat) (l : plit) : Prop :=
  if snd l then s i (fst l) else ~ s i (fst l).

Record ptransition : Type := {
  pt_src : nat;
  pt_label : list plit;
  pt_tgt : nat
}.

Record PBuchi : Type := {
  pb_nstates : nat;
  pb_init : nat;
  pb_trans : list ptransition;
  pb_accepting : list nat
}.

Definition PBA_accepts (A : PBuchi) (s : pword) : Prop :=
  exists run : nat -> nat,
    run 0%nat = pb_init A /\
    (forall i,
       (run i < pb_nstates A)%nat /\
       exists t,
         In t (pb_trans A) /\
         pt_src t = run i /\
         pt_tgt t = run (S i) /\
         Forall (plit_holds s i) (pt_label t)) /\
    (forall n, exists j, (n <= j)%nat /\ In (run j) (pb_accepting A)).

(* A transition of a timed automaton is read along an extended word only if
   the reset decisions of the word are exactly its reset list. *)
Definition resets_match
    (rho : ext_word) (i : nat) (resets : list (Clock)) : Prop :=
  forall x, ew_reset rho i x = true <-> In x resets.

(* ====================================================================== *)
(* 9. Timed Buchi automata                                                *)
(* ====================================================================== *)

Inductive clock_comparison : Type :=
| CLe | CLt | CGe | CGt | CEq.

Record clock_constraint : Type := {
  guard_clock : Clock;
  guard_comparison : clock_comparison;
  guard_bound : R
}.

Definition guard := list (option clock_constraint).

Definition atom_to_guard (a : latom) : option clock_constraint :=
  match a with
  | LCLe x d =>
      Some {| guard_clock := x; guard_comparison := CLe; guard_bound := d |}
  | LCLt x d =>
      Some {| guard_clock := x; guard_comparison := CLt; guard_bound := d |}
  | LCGe x d =>
      Some {| guard_clock := x; guard_comparison := CGe; guard_bound := d |}
  | LCGt x d =>
      Some {| guard_clock := x; guard_comparison := CGt; guard_bound := d |}
  | _ => None
  end.

Definition clock_constraint_holds
    (rho : ext_word) (i : nat) (c : clock_constraint) : Prop :=
  match guard_comparison c with
  | CLe => ew_val rho i (guard_clock c) <= guard_bound c
  | CLt => ew_val rho i (guard_clock c) <  guard_bound c
  | CGe => guard_bound c <= ew_val rho i (guard_clock c)
  | CGt => guard_bound c <  ew_val rho i (guard_clock c)
  | CEq => ew_val rho i (guard_clock c) = guard_bound c
  end.

Definition guard_item_holds
    (rho : ext_word) (i : nat) (c : option clock_constraint) : Prop :=
  match c with
  | Some c' => clock_constraint_holds rho i c'
  | None => True
  end.

Record tba_transition : Type := {
  bt_source : nat;
  bt_label : list alit;
  bt_guard : guard;
  bt_resets : list (Clock);
  bt_target : nat
}.

(* The Timed Buchi Automaton produced by the construction.  Its clocks are
   the elements of [Clock]. *)
Record TBA : Type := {
  tba_nstates : nat;
  tba_init : nat;
  tba_transitions : list tba_transition;
  tba_accepting : list nat
}.

Definition tba_transition_enabled
    (rho : ext_word) (i : nat) (t : tba_transition) : Prop :=
  label_holds (bt_label t) (letter_of rho i) /\
  Forall (guard_item_holds rho i) (bt_guard t) /\
  resets_match rho i (bt_resets t).

Definition TBA_ext_accepts (A : TBA) (rho : ext_word) : Prop :=
  exists run : nat -> nat,
    run 0%nat = tba_init A /\
    (forall i,
       (run i < tba_nstates A)%nat /\
       exists t,
         In t (tba_transitions A) /\
         bt_source t = run i /\
         bt_target t = run (S i) /\
         tba_transition_enabled rho i t) /\
    (forall n,
       exists j,
         (n <= j)%nat /\ In (run j) (tba_accepting A)).

Definition TBA_accepts (A : TBA) (w : C.timed_word) : Prop :=
  exists rho : ext_word,
    same_base rho w /\
    clock_consistent rho /\
    TBA_ext_accepts A rho.

Lemma lsat_psat :
  forall (rho : ext_word) (f : ltl) i,
    lsat rho i f <-> psat (word_of rho) i f.
Proof.
  intros rho f.
  induction f as [| | a | p IHp q IHq | p IHp q IHq | p IHp | p IHp q IHq | p IHp q IHq];
    intro i; simpl.
  - tauto.
  - tauto.
  - unfold word_of. tauto.
  - rewrite IHp, IHq. tauto.
  - rewrite IHp, IHq. tauto.
  - apply IHp.
  - split; intros [j [Hij [Hq Hp]]]; exists j; split; try exact Hij;
      split; try (apply IHq; exact Hq);
      intros k Hk; apply IHp; apply Hp; exact Hk.
  - split; intros H j Hj; destruct (H j Hj) as [Hq | [k [Hk Hp]]];
      try (left; apply IHq; exact Hq);
      right; exists k; split; try exact Hk; apply IHp; exact Hp.
Qed.

(* LTL formulas have no negation: satisfaction is monotone in the atoms. *)
Lemma psat_mono :
  forall (f : ltl) (s s' : pword),
    (forall i a, In a (ltl_atoms f) -> s i a -> s' i a) ->
    forall i, psat s i f -> psat s' i f.
Proof.
  intros f s s'.
  induction f as [| | a | p IHp q IHq | p IHp q IHq | p IHp | p IHp q IHq | p IHp q IHq];
    intros Hm i H; simpl in *.
  - exact I.
  - exact H.
  - apply Hm; [left; reflexivity | exact H].
  - assert (Hp : forall i a, In a (ltl_atoms p) -> s i a -> s' i a)
      by (intros k a Ha; apply Hm; apply in_or_app; left; exact Ha).
    assert (Hq : forall i a, In a (ltl_atoms q) -> s i a -> s' i a)
      by (intros k a Ha; apply Hm; apply in_or_app; right; exact Ha).
    destruct H as [H1 H2]. split; [exact (IHp Hp i H1) | exact (IHq Hq i H2)].
  - assert (Hp : forall i a, In a (ltl_atoms p) -> s i a -> s' i a)
      by (intros k a Ha; apply Hm; apply in_or_app; left; exact Ha).
    assert (Hq : forall i a, In a (ltl_atoms q) -> s i a -> s' i a)
      by (intros k a Ha; apply Hm; apply in_or_app; right; exact Ha).
    destruct H as [H1|H2]; [left; exact (IHp Hp i H1) | right; exact (IHq Hq i H2)].
  - exact (IHp Hm (S i) H).
  - assert (Hp : forall i a, In a (ltl_atoms p) -> s i a -> s' i a)
      by (intros k a Ha; apply Hm; apply in_or_app; left; exact Ha).
    assert (Hq : forall i a, In a (ltl_atoms q) -> s i a -> s' i a)
      by (intros k a Ha; apply Hm; apply in_or_app; right; exact Ha).
    destruct H as [j [Hij [Hj Hk]]]. exists j. split; [exact Hij|].
    split; [exact (IHq Hq j Hj)|]. intros k Hk'. exact (IHp Hp k (Hk k Hk')).
  - assert (Hp : forall i a, In a (ltl_atoms p) -> s i a -> s' i a)
      by (intros k a Ha; apply Hm; apply in_or_app; left; exact Ha).
    assert (Hq : forall i a, In a (ltl_atoms q) -> s i a -> s' i a)
      by (intros k a Ha; apply Hm; apply in_or_app; right; exact Ha).
    intros j Hj. destruct (H j Hj) as [Hj' | [k [Hk Hk']]].
    + left. exact (IHq Hq j Hj').
    + right. exists k. split; [exact Hk | exact (IHp Hp k Hk')].
Qed.

(* ====================================================================== *)
(* 9b'. nat-consistent propositional words                             *)
(* ====================================================================== *)

(* The translation T uses the negated event atom [LNAct p], which holds in
   an extended word exactly when the event atom [LAct p] does not.  The
   LTL-to-Buchi back-end may receive this atom as the explicit negation of
   the event atom (the quoted atom "p" negated: !"p"), so that its contract
   is only required on the action-consistent propositional words, in which
   [LNAct p] is the complement of [LAct p] at every position.  The
   propositional word of an extended word is action-consistent, and
   relaxation preserves the property: it never changes an action atom.
   Monotonicity (psat_mono) is used only on words that differ on the
   extended (clock and marker) atoms. *)
Definition action_consistent (s : pword) : Prop :=
  forall (i : nat) (p : nat), s i (LNAct p) <-> ~ s i (LAct p).

Lemma word_of_action_consistent :
  forall rho : ext_word, action_consistent (word_of rho).
Proof.
  intros rho. unfold action_consistent. intros i p.
  unfold word_of. simpl. split; intro H; exact H.
Qed.

(* ====================================================================== *)
(* 9c. Choice of a transition along a run                                 *)
(* ====================================================================== *)

(* The first element of a list that satisfies [P] (classical decision). *)
Fixpoint first_such {A : Type} (P : A -> Prop) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: l' => if decide_b (P x) then Some x else first_such P l'
  end.

Lemma first_such_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    (exists x, In x l /\ P x) ->
    exists x, first_such P l = Some x /\ In x l /\ P x.
Proof.
  intros A P l. induction l as [|y l IH]; intros [x [Hx HP]]; [contradiction|].
  simpl. destruct (decide_b (P y)) eqn:E.
  - exists y. split; [reflexivity|]. split; [left; reflexivity|].
    apply decide_b_spec. exact E.
  - destruct Hx as [<-|Hx].
    + exfalso. apply decide_b_spec in HP. congruence.
    + destruct (IH (ex_intro _ x (conj Hx HP))) as [z [Hz [Hin HPz]]].
      exists z. split; [exact Hz|]. split; [right; exact Hin | exact HPz].
Qed.

(* ====================================================================== *)
(* 9d. Decidable equality of atoms                                        *)
(* ====================================================================== *)

Definition latom_eq_dec : forall a b : latom, {a = b} + {a <> b}.
Proof.
  decide equality;
    first [apply Nat.eq_dec | apply Req_EM_T | apply clock_eq_dec].
Defined.

Definition latom_eqb (a b : latom) : bool :=
  if latom_eq_dec a b then true else false.

Lemma latom_eqb_true : forall a b, latom_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold latom_eqb.
  destruct (latom_eq_dec a b); split; intro H; congruence.
Qed.

Definition in_atoms (a : latom) (l : list (latom)) : bool :=
  existsb (latom_eqb a) l.

Lemma in_atoms_iff : forall a l, in_atoms a l = true <-> In a l.
Proof.
  intros a l. unfold in_atoms. rewrite existsb_exists. split.
  - intros [b [Hb E]]. apply latom_eqb_true in E. subst b. exact Hb.
  - intro H. exists a. split; [exact H|]. apply latom_eqb_true. reflexivity.
Qed.

(* ====================================================================== *)
(* 9e. Relaxation                                                         *)
(* ====================================================================== *)

(* Extended atoms: clock guards and reset/unchanged markers. *)
Definition is_ext (a : latom) : bool :=
  match a with
  | LAct _ | LNAct _ => false
  | _ => true
  end.

Definition lit_conflict (p q : plit) : bool :=
  latom_eqb (fst p) (fst q) && xorb (snd p) (snd q).

(* A cube is consistent when it contains no atom together with its
   negation; an inconsistent cube is never satisfied. *)
Definition consistent (l : list (plit)) : bool :=
  forallb (fun p => negb (existsb (lit_conflict p) l)) l.

Lemma consistent_holds :
  forall (s : pword) i l, Forall (plit_holds s i) l -> consistent l = true.
Proof.
  intros s i l H. unfold consistent. apply forallb_forall. intros p Hp.
  apply negb_true_iff. destruct (existsb (lit_conflict p) l) eqn:E; [|reflexivity].
  exfalso. apply existsb_exists in E. destruct E as [q [Hq Hc]].
  rewrite Forall_forall in H. pose proof (H p Hp) as H1. pose proof (H q Hq) as H2.
  destruct p as [a b], q as [a' b']. unfold lit_conflict in Hc. simpl in *.
  apply andb_true_iff in Hc. destruct Hc as [Ha Hb].
  apply latom_eqb_true in Ha. subst a'.
  unfold plit_holds in *. simpl in *.
  destruct b, b'; simpl in Hb; try discriminate; tauto.
Qed.

Lemma consistent_no_conflict :
  forall l a, consistent l = true -> In (a, true) l -> In (a, false) l -> False.
Proof.
  intros l a Hc H1 H2. unfold consistent in Hc. rewrite forallb_forall in Hc.
  specialize (Hc _ H1). apply negb_true_iff in Hc.
  assert (E : existsb (lit_conflict (a, true)) l = true).
  { apply existsb_exists. exists (a, false). split; [exact H2|].
    unfold lit_conflict. simpl. rewrite andb_true_iff. split; [|reflexivity].
    apply latom_eqb_true. reflexivity. }
  congruence.
Qed.

(* Relaxation keeps the action literals and the positive literals over the
   extended atoms of the formula [F]; the other literals over extended atoms
   are dropped.  Inconsistent cubes are removed. *)
Definition keep_lit (F : list (latom)) (p : plit) : bool :=
  negb (is_ext (fst p)) || (snd p && in_atoms (fst p) F).

Definition relax_trans (F : list (latom)) (t : ptransition) : ptransition :=
  {| pt_src := pt_src t; pt_label := filter (keep_lit F) (pt_label t); pt_tgt := pt_tgt t |}.

Definition relax (F : list (latom)) (A : PBuchi) : PBuchi :=
  {| pb_nstates := pb_nstates A;
     pb_init := pb_init A;
     pb_trans := map (relax_trans F) (filter (fun t => consistent (pt_label t)) (pb_trans A));
     pb_accepting := pb_accepting A |}.

Lemma relax_complete :
  forall F A (s : pword), PBA_accepts A s -> PBA_accepts (relax F A) s.
Proof.
  intros F A s [run [Hinit [Hsteps Hacc]]].
  exists run. split; [exact Hinit|]. split; [|exact Hacc].
  intro i. destruct (Hsteps i) as [Hb [t [Ht [Hs [Hd Hl]]]]].
  split; [exact Hb|]. exists (relax_trans F t). split.
  - simpl. apply in_map. apply filter_In. split; [exact Ht|].
    exact (consistent_holds Hl).
  - simpl. split; [exact Hs|]. split; [exact Hd|].
    rewrite Forall_forall in *. intros p Hp. apply filter_In in Hp.
    apply Hl. exact (proj1 Hp).
Qed.

(* Relaxation preserves the language: a relaxed run on [s] is a run of the
   original automaton on a word [s'] that differs from [s] only on extended
   atoms, which it makes false (dropped negative literals) or true (dropped
   atoms outside the formula); by monotonicity, [s] satisfies the formula. *)
Lemma relax_sound :
  forall (f : ltl) A (s : pword),
    action_consistent s ->
    (forall s', action_consistent s' -> PBA_accepts A s' -> psat s' 0 f) ->
    PBA_accepts (relax (ltl_atoms f) A) s -> psat s 0 f.
Proof.
  intros f A s Hcs Hax [run [Hinit [Hsteps Hacc]]].
  set (F := ltl_atoms f).
  set (P := fun i (t : ptransition) =>
              consistent (pt_label t) = true /\ pt_src t = run i /\
              pt_tgt t = run (S i) /\
              Forall (plit_holds s i) (pt_label (relax_trans F t))).
  assert (Hex : forall i, exists t, In t (pb_trans A) /\ P i t).
  { intro i. destruct (Hsteps i) as [_ [t' [Ht' [Hs [Hd Hl]]]]].
    simpl in Ht'. apply in_map_iff in Ht'. destruct Ht' as [t [<- Ht]].
    apply filter_In in Ht. destruct Ht as [Ht Hc].
    exists t. split; [exact Ht|]. split; [exact Hc|]. split; [exact Hs|].
    split; [exact Hd | exact Hl]. }
  set (lab := fun i => match first_such (P i) (pb_trans A) with
                       | Some t => pt_label t | None => [] end).
  set (s' := fun i (a : latom) =>
               if is_ext a
               then (In (a, true) (lab i) /\ ~ In a F) \/ (s i a /\ ~ In (a, false) (lab i))
                              else s i a).
  (* the word s' differs from s on extended atoms only, so it is
     action-consistent when s is *)
  assert (Hcs' : action_consistent s').
  { intros i p. unfold s'. unfold is_ext. simpl. exact (Hcs i p). }
  assert (Hrun : PBA_accepts A s').
  { exists run. split; [exact Hinit|]. split; [|exact Hacc].
    intro i. split; [exact (proj1 (Hsteps i))|].
    destruct (first_such_spec (Hex i)) as [t [Hfs [Ht [Hc [Hs [Hd Hl]]]]]].
    exists t. split; [exact Ht|]. split; [exact Hs|]. split; [exact Hd|].
    assert (Hlab : lab i = pt_label t) by (unfold lab; rewrite Hfs; reflexivity).
    apply Forall_forall. intros [a b] Hab.
    rewrite Forall_forall in Hl. simpl in Hl.
    unfold plit_holds. simpl. unfold s'. rewrite Hlab.
    destruct (is_ext a) eqn:Hext.
    - destruct b.
      + destruct (in_atoms a F) eqn:HF.
        * right. split.
          -- assert (Hk : In (a, true) (filter (keep_lit F) (pt_label t))).
             { apply filter_In. split; [exact Hab|].
               unfold keep_lit. simpl. rewrite Hext, HF. reflexivity. }
             exact (Hl _ Hk).
          -- intro Hf. exact (consistent_no_conflict Hc Hab Hf).
        * left. split; [exact Hab|]. intro Hin.
          apply in_atoms_iff in Hin. congruence.
      + intros [[Ht' _] | [_ Hn]].
        * exact (consistent_no_conflict Hc Ht' Hab).
        * exact (Hn Hab).
    - assert (Hk : In (a, b) (filter (keep_lit F) (pt_label t))).
      { apply filter_In. split; [exact Hab|].
        unfold keep_lit. simpl. rewrite Hext. reflexivity. }
      exact (Hl _ Hk). }
  apply (psat_mono (s := s')); [|exact (Hax s' Hcs' Hrun)].
  intros i a Ha H. unfold s' in H. destruct (is_ext a).
  - destruct H as [[_ Hn] | [H _]]; [contradiction | exact H].
  - exact H.
Qed.

(* ====================================================================== *)
(* 9f. Preservation and restart clocks                                    *)
(* ====================================================================== *)

(* The clock of a lower-bounded Until or of an upper-bounded Release is a
   restart clock: it is tested only against lower bounds and constrained
   only by reset markers.  The other clocks are preservation clocks: tested
   only against upper bounds and constrained only by unchanged markers. *)

Definition atom_ok (a : latom) : Prop :=
  match a with
  | LCLe x _ | LCLt x _ | LUnch x => is_restart x = false
  | LCGe x _ | LCGt x _ | LRst x => is_restart x = true
  | _ => True
  end.


Definition has_pos (a : latom) (l : list (plit)) : bool :=
  existsb (fun p => latom_eqb (fst p) a && snd p) l.

Lemma has_pos_iff : forall a l, has_pos a l = true <-> In (a, true) l.
Proof.
  intros a l. unfold has_pos. rewrite existsb_exists. split.
  - intros [[b c] [Hin H]]. apply andb_true_iff in H. destruct H as [Hb Hc].
    apply latom_eqb_true in Hb. simpl in *. subst. exact Hin.
  - intro H. exists (a, true). split; [exact H|]. simpl.
    rewrite andb_true_r. apply latom_eqb_true. reflexivity.
Qed.

(* A preservation clock is reset unless the cube contains its unchanged
   marker; a restart clock is reset exactly when the cube contains its reset
   marker. *)
Definition comp_resets (l : list (plit)) : list (Clock) :=
  filter (fun x => if is_restart x then has_pos (LRst x) l
                   else negb (has_pos (LUnch x) l)) all_clocks.

Definition act_lit (p : plit) : list alit :=
  match fst p with
  | LAct q => [(q, snd p)]
  | LNAct q => [(q, negb (snd p))]
  | _ => []
  end.

Definition pos_atoms (l : list (plit)) : list (latom) := map fst (filter snd l).

Definition complete_trans (t : ptransition) : tba_transition :=
  {| bt_source := pt_src t;
     bt_label := flat_map act_lit (pt_label t);
     bt_guard := map atom_to_guard (pos_atoms (pt_label t));
     bt_resets := comp_resets (pt_label t);
     bt_target := pt_tgt t |}.

Definition complete (A : PBuchi) : TBA :=
  {| tba_nstates := pb_nstates A;
     tba_init := pb_init A;
     tba_transitions := map complete_trans (pb_trans A);
     tba_accepting := pb_accepting A |}.

(* Every literal over an extended atom is positive and of the right kind. *)
Definition labels_ok (A : PBuchi) : Prop :=
  forall t a b, In t (pb_trans A) -> In (a, b) (pt_label t) ->
    is_ext a = true -> b = true /\ atom_ok a.

Lemma relax_labels_ok :
  forall F A, (forall a, In a F -> atom_ok a) -> labels_ok (relax F A).
Proof.
  intros F A HF t a b Ht Hab Hext. simpl in Ht.
  apply in_map_iff in Ht. destruct Ht as [t0 [<- _]].
  simpl in Hab. apply filter_In in Hab. destruct Hab as [_ Hk].
  unfold keep_lit in Hk. simpl in Hk. rewrite Hext in Hk. simpl in Hk.
  apply andb_true_iff in Hk. destruct Hk as [Hb Hin].
  split; [exact Hb|]. apply HF. apply in_atoms_iff. exact Hin.
Qed.

Lemma in_comp_resets :
  forall l x,
    In x (comp_resets l) <->
    (if is_restart x then In (LRst x, true) l else ~ In (LUnch x, true) l).
Proof.
  intros l x. unfold comp_resets. rewrite filter_In.
  split.
  - intros [_ H]. destruct (is_restart x).
    + apply has_pos_iff. exact H.
    + intro Hin. apply has_pos_iff in Hin. rewrite Hin in H. discriminate.
  - intro H. split; [apply all_clocks_complete|]. destruct (is_restart x).
    + apply has_pos_iff. exact H.
    + destruct (has_pos (LUnch x) l) eqn:E; [|reflexivity].
      exfalso. apply H. apply has_pos_iff. exact E.
Qed.

(* Soundness: a run of the completed automaton is a run of the relaxed
   automaton on the propositional word of the same extended word. *)
Lemma complete_trans_sound :
  forall (rho : ext_word) i t,
    (forall a b, In (a, b) (pt_label t) -> is_ext a = true -> b = true /\ atom_ok a) ->
    tba_transition_enabled rho i (complete_trans t) ->
    Forall (plit_holds (word_of rho) i) (pt_label t).
Proof.
  intros rho i t Hok [Hlab [Hg Hres]].
  unfold complete_trans, label_holds in *. simpl in *.
  rewrite Forall_forall in Hlab, Hg. apply Forall_forall.
  intros [a b] Hin. unfold plit_holds, word_of. simpl.
  destruct a as [q|q|x d|x d|x d|x d|x|x].
  - assert (H : alit_holds (C.tw_action (ew_base rho) i) (q, b)).
    { apply Hlab. apply in_flat_map. exists (LAct q, b). split; [exact Hin|].
      left. reflexivity. }
    unfold alit_holds in H. simpl in H. destruct b; exact H.
  - assert (H : alit_holds (C.tw_action (ew_base rho) i) (q, negb b)).
    { apply Hlab. apply in_flat_map. exists (LNAct q, b). split; [exact Hin|].
      left. reflexivity. }
    unfold alit_holds in H. simpl in *. destruct b; simpl in H; [exact H|].
    intro Hn. exact (Hn H).
  - destruct (Hok _ _ Hin eq_refl) as [-> _].
    assert (Hp : In (LCLe x d) (pos_atoms (pt_label t)))
      by (apply in_map_iff; exists (LCLe x d, true); split;
          [reflexivity | apply filter_In; split; [exact Hin | reflexivity]]).
    exact (Hg _ (in_map _ _ _ Hp)).
  - destruct (Hok _ _ Hin eq_refl) as [-> _].
    assert (Hp : In (LCLt x d) (pos_atoms (pt_label t)))
      by (apply in_map_iff; exists (LCLt x d, true); split;
          [reflexivity | apply filter_In; split; [exact Hin | reflexivity]]).
    exact (Hg _ (in_map _ _ _ Hp)).
  - destruct (Hok _ _ Hin eq_refl) as [-> _].
    assert (Hp : In (LCGe x d) (pos_atoms (pt_label t)))
      by (apply in_map_iff; exists (LCGe x d, true); split;
          [reflexivity | apply filter_In; split; [exact Hin | reflexivity]]).
    exact (Hg _ (in_map _ _ _ Hp)).
  - destruct (Hok _ _ Hin eq_refl) as [-> _].
    assert (Hp : In (LCGt x d) (pos_atoms (pt_label t)))
      by (apply in_map_iff; exists (LCGt x d, true); split;
          [reflexivity | apply filter_In; split; [exact Hin | reflexivity]]).
    exact (Hg _ (in_map _ _ _ Hp)).
  - destruct (Hok _ _ Hin eq_refl) as [-> Hk]. simpl in Hk.
    unfold rst_at. apply (proj2 (Hres x)). apply in_comp_resets.
    rewrite Hk. exact Hin.
  - destruct (Hok _ _ Hin eq_refl) as [-> Hk]. simpl in Hk.
    unfold unch_at. apply Bool.not_true_iff_false. intro E.
    apply (proj1 (Hres x)) in E. apply in_comp_resets in E.
    rewrite Hk in E. contradiction.
Qed.

Lemma complete_sound :
  forall A (rho : ext_word),
    labels_ok A -> TBA_ext_accepts (complete A) rho -> PBA_accepts A (word_of rho).
Proof.
  intros A rho Hok [run [Hinit [Hsteps Hacc]]].
  exists run. split; [exact Hinit|]. split; [|exact Hacc].
  intro i. destruct (Hsteps i) as [Hb [tt [Ht [Hs [Hd Hen]]]]].
  split; [exact Hb|]. simpl in Ht. apply in_map_iff in Ht. destruct Ht as [t [<- Ht]].
  exists t. split; [exact Ht|]. split; [exact Hs|]. split; [exact Hd|].
  apply (complete_trans_sound (rho := rho) (i := i)); [|exact Hen].
  intros a b Hab Hext. exact (Hok t a b Ht Hab Hext).
Qed.

(* Clock values determined by an initial valuation and reset decisions. *)
Fixpoint vals (v0 : Clock -> R) (r : nat -> Clock -> bool)
         (w : C.timed_word) (i : nat) (x : Clock) : R :=
  match i with
  | O => v0 x
  | S j => if r j x then C.delta w j else vals v0 r w j x + C.delta w j
  end.

Lemma vals_nonneg :
  forall v0 r w, (forall x, 0 <= v0 x) -> forall i x, 0 <= vals v0 r w i x.
Proof.
  intros v0 r w H0 i x. induction i as [|j IH]; simpl; [apply H0|].
  pose proof (C.delta_nonneg w j). destruct (r j x); lra.
Qed.

(* Completeness (Lemma IV.1 of the paper): along a run of the relaxed
   automaton on the propositional word of a clock-consistent extended word
   [rho], the extended word [rho'] with the same timed word and initial
   values, and with the resets of the completion, is accepted by the
   completed automaton.  Preservation clocks of [rho'] are reset wherever
   those of [rho] are, so their values are smaller and their upper bounds
   still hold; restart clocks of [rho'] are reset only where those of [rho]
   are, so their values are larger and their lower bounds still hold. *)
Lemma complete_complete :
  forall A (rho : ext_word),
    clock_consistent rho -> labels_ok A -> PBA_accepts A (word_of rho) ->
    exists rho' : ext_word,
      ew_base rho' = ew_base rho /\ clock_consistent rho' /\
      TBA_ext_accepts (complete A) rho'.
Proof.
  intros A rho [Hnn Hcc] Hok [run [Hinit [Hsteps Hacc]]].
  set (P := fun i (t : ptransition) =>
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
  set (r := fun i x => if In_dec clock_eq_dec x (comp_resets (lab i))
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
    rewrite (Hcc j x). pose proof (C.delta_nonneg (ew_base rho) j).
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
    rewrite (Hcc j x). pose proof (C.delta_nonneg (ew_base rho) j).
    pose proof (@vals_nonneg (ew_val rho 0) r (ew_base rho) (Hnn 0%nat) j x).
    destruct (r j x) eqn:Erj.
    - apply Hr in Erj. apply in_comp_resets in Erj. rewrite Hx in Erj.
      pose proof (Hsat _ _ _ Erj) as HR. unfold plit_holds, word_of in HR.
      simpl in HR. unfold rst_at in HR. rewrite HR. lra.
    - destruct (ew_reset rho j x); lra. }
  exists rho'. split; [reflexivity|]. split.
  - split.
    + intros i x. apply vals_nonneg. apply Hnn.
    + intros i x. reflexivity.
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
        destruct (Nat.eq_dec (C.tw_action (ew_base rho) i) q0) as [E|E];
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


(* The class of positive clocked-LTL formulas: every atom is polarity-correct. *)
Definition ClassC (phi : ltl) : Prop :=
  forall a, In a (ltl_atoms phi) -> atom_ok a.

(* Timed language of a clocked-LTL formula over clock-consistent words. *)
Definition L_timed (phi : ltl) (w : C.timed_word) : Prop :=
  exists rho : ext_word,
    same_base rho w /\ clock_consistent rho /\ lsat rho 0 phi.

Definition compile_abs (phi : ltl) (A : PBuchi) : TBA :=
  complete (relax (ltl_atoms phi) A).

Theorem abstract_compile_correct :
  forall (phi : ltl) (A : PBuchi) (w : C.timed_word),
    ClassC phi ->
    (forall s : pword, action_consistent s ->
       (PBA_accepts A s <-> psat s 0 phi)) ->
    (L_timed phi w <-> TBA_accepts (compile_abs phi A) w).
Proof.
  intros phi A w Hc HA.
  assert (Hlo : labels_ok (relax (ltl_atoms phi) A))
    by (apply relax_labels_ok; exact Hc).
  unfold L_timed, compile_abs, TBA_accepts.
  split.
  - intros [rho [Hbase [Hclock Hltl]]].
    apply lsat_psat in Hltl.
    apply (proj2 (HA (word_of rho) (word_of_action_consistent rho))) in Hltl.
    apply (relax_complete (ltl_atoms phi)) in Hltl.
    destruct (complete_complete Hclock Hlo Hltl)
      as [rho' [Hb' [Hc' Ha']]].
    exists rho'. split; [unfold same_base in *; rewrite Hb'; exact Hbase|].
    split; [exact Hc' | exact Ha'].
  - intros [rho [Hbase [Hclock Htba]]].
    exists rho. split; [exact Hbase|]. split; [exact Hclock|].
    apply lsat_psat.
    apply (relax_sound (A := A)).
    + apply word_of_action_consistent.
    + intros s' Hcs' Hs'. exact (proj1 (HA s' Hcs') Hs').
    + exact (complete_sound Hlo Htba).
Qed.

End Abstract.

Print Assumptions abstract_compile_correct.
