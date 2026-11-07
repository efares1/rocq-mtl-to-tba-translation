(*
  ClockedLTL_Instance.v

  Links the abstract development (ClockedLTL_Abstract) to the MTL
  development (Core).  For a fixed MTL formula [root], the clocks are
  [C.Clock root]; the abstract notions instantiated at this clock type are
  shown to coincide with the Core notions through a structural
  translation [cv_*] of syntax and automata.

  Main result [MTL_correct_via_abstract]: the MTL-to-TBA correctness
  theorem (compile_with, any backend meeting the contract) is derived from
  the abstract theorem [abstract_compile_correct]; MTL is an instance.
*)
Require Import Arith Lia List Bool Reals Lra.
Import ListNotations.
Open Scope R_scope.
Require MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Require EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.
Require ClockedLTL_Abstract.
Module C := MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.
Module P := EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.
Module G := ClockedLTL_Abstract.

Section Instance.

Variable root : C.mtl.

Local Notation K := (C.Clock root).

Definition cdec : forall x y : K, {x = y} + {x <> y} := @C.clock_eq_dec root.
Definition rst : K -> bool := @C.is_restart root.
Definition allc : list K := @C.all_clocks root.
Definition allc_complete : forall x : K, In x allc := @C.all_clocks_complete root.

(* ------------------------------------------------------------------ *)
(* Translation of syntax                                              *)
(* ------------------------------------------------------------------ *)

Definition cv_atom (a : C.latom root) : G.latom K :=
  match a with
  | C.LAct p => @G.LAct K p
  | C.LNAct p => @G.LNAct K p
  | C.LCLe x d => @G.LCLe K x d
  | C.LCLt x d => @G.LCLt K x d
  | C.LCGe x d => @G.LCGe K x d
  | C.LCGt x d => @G.LCGt K x d
  | C.LRst x => @G.LRst K x
  | C.LUnch x => @G.LUnch K x
  end.

Fixpoint cv_ltl (f : C.ltl root) : G.ltl K :=
  match f with
  | C.LTrue => @G.LTrue K
  | C.LFalse => @G.LFalse K
  | C.LAtom a => @G.LAtom K (cv_atom a)
  | C.LAnd p q => @G.LAnd K (cv_ltl p) (cv_ltl q)
  | C.LOr p q => @G.LOr K (cv_ltl p) (cv_ltl q)
  | C.LNext p => @G.LNext K (cv_ltl p)
  | C.LUntil p q => @G.LUntil K (cv_ltl p) (cv_ltl q)
  | C.LRelease p q => @G.LRelease K (cv_ltl p) (cv_ltl q)
  end.

Lemma ltl_atoms_cv :
  forall f : C.ltl root,
    G.ltl_atoms (cv_ltl f) = map cv_atom (C.ltl_atoms f).
Proof.
  induction f; simpl; try reflexivity;
    try (rewrite map_app; congruence); try congruence.
Qed.

Definition cv_plit (p : C.plit root) : G.plit K := (cv_atom (fst p), snd p).

Definition cv_pt (t : C.ptransition root) : G.ptransition K :=
  {| G.pt_src := C.pt_src t;
     G.pt_label := map cv_plit (C.pt_label t);
     G.pt_tgt := C.pt_tgt t |}.

Definition cv_pba (A : C.PBuchi root) : G.PBuchi K :=
  {| G.pb_nstates := C.pb_nstates A;
     G.pb_init := C.pb_init A;
     G.pb_trans := map cv_pt (C.pb_trans A);
     G.pb_accepting := C.pb_accepting A |}.

Definition cv_cmp (c : C.clock_comparison) : G.clock_comparison :=
  match c with
  | C.CLe => G.CLe | C.CLt => G.CLt | C.CGe => G.CGe
  | C.CGt => G.CGt | C.CEq => G.CEq
  end.

Definition cv_cc (c : C.clock_constraint root) : G.clock_constraint K :=
  {| G.guard_clock := C.guard_clock c;
     G.guard_comparison := cv_cmp (C.guard_comparison c);
     G.guard_bound := C.guard_bound c |}.

Definition cv_tt (t : C.tba_transition root) : G.tba_transition K :=
  {| G.bt_source := C.bt_source t;
     G.bt_label := C.bt_label t;
     G.bt_guard := map (option_map cv_cc) (C.bt_guard t);
     G.bt_resets := C.bt_resets t;
     G.bt_target := C.bt_target t |}.

Definition cv_tba (A : C.TBA root) : G.TBA K :=
  {| G.tba_nstates := C.tba_nstates A;
     G.tba_init := C.tba_init A;
     G.tba_transitions := map cv_tt (C.tba_transitions A);
     G.tba_accepting := C.tba_accepting A |}.

(* Words *)
Definition cv_word (r : C.ext_word root) : G.ext_word K :=
  {| G.ew_base := C.ew_base r; G.ew_val := C.ew_val r;
     G.ew_reset := C.ew_reset r |}.

Definition bk_word (g : G.ext_word K) : C.ext_word root :=
  {| C.ew_base := G.ew_base g; C.ew_val := G.ew_val g;
     C.ew_reset := G.ew_reset g |}.

Lemma bk_cv_word : forall r, bk_word (cv_word r) = r.
Proof. intro r. destruct r. reflexivity. Qed.

Definition bk_pw (g : G.pword K) : C.pword root := fun i a => g i (cv_atom a).

(* ------------------------------------------------------------------ *)
(* Semantics                                                          *)
(* ------------------------------------------------------------------ *)

Lemma psat_cv :
  forall f g i, G.psat g i (cv_ltl f) <-> C.psat (bk_pw g) i f.
Proof.
  induction f; intros g i; simpl; try tauto;
    try (setoid_rewrite IHf1; setoid_rewrite IHf2; reflexivity);
    try (rewrite IHf; reflexivity).
  all: reflexivity.
Qed.

Lemma lsat_cv :
  forall f g i, G.lsat g i (cv_ltl f) <-> C.lsat (bk_word g) i f.
Proof.
  induction f; intros g i; simpl; try tauto;
    try (setoid_rewrite IHf1; setoid_rewrite IHf2; reflexivity);
    try (rewrite IHf; reflexivity).
  match goal with |- context [C.atom_sat _ _ ?a] => destruct a; reflexivity end.
Qed.

(* ------------------------------------------------------------------ *)
(* Atoms and the relaxation / completion helpers                      *)
(* ------------------------------------------------------------------ *)

Lemma cv_atom_inj : forall a b, cv_atom a = cv_atom b -> a = b.
Proof.
  intros a b H. destruct a; destruct b; simpl in H;
    first [discriminate H | (injection H; intros; subst; reflexivity)].
Qed.

Lemma eqb_cv : forall a b,
  G.latom_eqb cdec rst allc_complete (cv_atom a) (cv_atom b)
  = C.latom_eqb a b.
Proof.
  intros a b. apply Bool.eq_iff_eq_true.
  rewrite (G.latom_eqb_true cdec rst allc_complete), C.latom_eqb_true.
  split; [apply cv_atom_inj | intro H; rewrite H; reflexivity].
Qed.

Lemma is_ext_cv : forall a, G.is_ext (cv_atom a) = C.is_ext a.
Proof. intro a. destruct a; reflexivity. Qed.

Lemma in_atoms_cv : forall a F,
  G.in_atoms cdec rst allc_complete (cv_atom a) (map cv_atom F)
  = C.in_atoms a F.
Proof.
  intros a F. unfold G.in_atoms, C.in_atoms.
  induction F as [|b F IH]; simpl; [reflexivity|].
  rewrite eqb_cv, IH. reflexivity.
Qed.

Lemma lit_conflict_cv : forall p q,
  G.lit_conflict cdec rst allc_complete (cv_plit p) (cv_plit q)
  = C.lit_conflict p q.
Proof.
  intros p q. unfold G.lit_conflict, C.lit_conflict, cv_plit. simpl.
  rewrite eqb_cv. reflexivity.
Qed.

Lemma existsb_conflict_cv : forall p l,
  existsb (G.lit_conflict cdec rst allc_complete (cv_plit p)) (map cv_plit l)
  = existsb (C.lit_conflict p) l.
Proof.
  intros p l. induction l as [|q l IH]; simpl; [reflexivity|].
  rewrite lit_conflict_cv, IH. reflexivity.
Qed.

Lemma consistent_cv : forall l,
  G.consistent cdec rst allc_complete (map cv_plit l) = C.consistent l.
Proof.
  intro l. unfold G.consistent, C.consistent.
  assert (Hgen : forall l0,
    forallb (fun p => negb (existsb (G.lit_conflict cdec rst allc_complete p)
                                    (map cv_plit l)))
            (map cv_plit l0)
    = forallb (fun p => negb (existsb (C.lit_conflict p) l)) l0).
  { induction l0 as [|p l0 IH]; simpl; [reflexivity|].
    rewrite IH, existsb_conflict_cv. reflexivity. }
  exact (Hgen l).
Qed.

Lemma keep_lit_cv : forall F p,
  G.keep_lit cdec rst allc_complete (map cv_atom F) (cv_plit p)
  = C.keep_lit F p.
Proof.
  intros F p. unfold G.keep_lit, C.keep_lit, cv_plit. simpl.
  rewrite is_ext_cv, in_atoms_cv. reflexivity.
Qed.

Lemma filter_keep_cv : forall F l,
  filter (G.keep_lit cdec rst allc_complete (map cv_atom F)) (map cv_plit l)
  = map cv_plit (filter (C.keep_lit F) l).
Proof.
  intros F l. induction l as [|p l IH]; simpl; [reflexivity|].
  rewrite keep_lit_cv. destruct (C.keep_lit F p); simpl; rewrite IH; reflexivity.
Qed.

Lemma relax_trans_cv : forall F t,
  cv_pt (C.relax_trans F t)
  = G.relax_trans cdec rst allc_complete (map cv_atom F) (cv_pt t).
Proof.
  intros F t. unfold cv_pt, C.relax_trans, G.relax_trans. simpl.
  rewrite filter_keep_cv. reflexivity.
Qed.

Lemma relax_cv : forall F A,
  cv_pba (C.relax F A)
  = G.relax cdec rst allc_complete (map cv_atom F) (cv_pba A).
Proof.
  intros F A. unfold cv_pba, C.relax, G.relax. simpl.
  f_equal.
  induction (C.pb_trans A) as [|t ts IH]; simpl; [reflexivity|].
  unfold cv_pt at 2. simpl. rewrite consistent_cv.
  destruct (C.consistent (C.pt_label t)); simpl.
  - rewrite IH, relax_trans_cv. reflexivity.
  - exact IH.
Qed.

Lemma act_lit_cv : forall p, G.act_lit (cv_plit p) = C.act_lit p.
Proof. intros [a b]. destruct a; reflexivity. Qed.

Lemma flat_map_act_cv : forall l,
  flat_map (@G.act_lit K) (map cv_plit l) = flat_map (@C.act_lit root) l.
Proof.
  induction l as [|p l IH]; simpl; [reflexivity|].
  rewrite act_lit_cv, IH. reflexivity.
Qed.

Lemma pos_atoms_cv : forall l,
  G.pos_atoms (map cv_plit l) = map cv_atom (C.pos_atoms l).
Proof.
  induction l as [|[a b] l IH]; simpl; [reflexivity|].
  unfold G.pos_atoms, C.pos_atoms in *. simpl.
  destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma atom_to_guard_cv : forall a,
  G.atom_to_guard (cv_atom a) = option_map cv_cc (C.atom_to_guard a).
Proof. intro a. destruct a; reflexivity. Qed.

Lemma has_pos_cv : forall a l,
  G.has_pos cdec rst allc_complete (cv_atom a) (map cv_plit l)
  = C.has_pos a l.
Proof.
  intros a l. unfold G.has_pos, C.has_pos.
  induction l as [|p l IH]; simpl; [reflexivity|].
  change (fst (cv_plit p)) with (cv_atom (fst p));
  change (snd (cv_plit p)) with (snd p).
  rewrite eqb_cv, IH. reflexivity.
Qed.

Lemma comp_resets_cv : forall l,
  G.comp_resets cdec rst allc_complete (map cv_plit l) = C.comp_resets l.
Proof.
  intro l. unfold G.comp_resets, C.comp_resets.
  apply filter_ext. intro x.
  pose proof (has_pos_cv (C.LRst x) l) as H1.
  pose proof (has_pos_cv (C.LUnch x) l) as H2.
  change (cv_atom (C.LRst x)) with (@G.LRst K x) in H1.
  change (cv_atom (C.LUnch x)) with (@G.LUnch K x) in H2.
  change (rst x) with (C.is_restart x).
  destruct (C.is_restart x); [exact H1 | rewrite H2; reflexivity].
Qed.

Lemma complete_trans_cv : forall t,
  cv_tt (C.complete_trans t)
  = G.complete_trans cdec rst allc_complete (cv_pt t).
Proof.
  intro t. unfold cv_tt, C.complete_trans, G.complete_trans, cv_pt. simpl.
  rewrite comp_resets_cv, flat_map_act_cv, pos_atoms_cv, map_map, map_map.
  assert (Hg : map (fun x => option_map cv_cc (C.atom_to_guard x))
                   (C.pos_atoms (C.pt_label t))
             = map (fun x => G.atom_to_guard (cv_atom x))
                   (C.pos_atoms (C.pt_label t)))
    by (apply map_ext; intro a; symmetry; apply atom_to_guard_cv).
  rewrite Hg. reflexivity.
Qed.

Lemma complete_cv : forall B,
  cv_tba (C.complete B) = G.complete cdec rst allc_complete (cv_pba B).
Proof.
  intro B. unfold cv_tba, C.complete, G.complete, cv_pba. simpl.
  rewrite map_map, map_map.
  assert (E : map (fun x => cv_tt (C.complete_trans x)) (C.pb_trans B)
            = map (fun x => G.complete_trans cdec rst allc_complete (cv_pt x))
                  (C.pb_trans B))
    by (apply map_ext; intro t; apply complete_trans_cv).
  rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Acceptance                                                         *)
(* ------------------------------------------------------------------ *)

Lemma pba_cv : forall A g,
  G.PBA_accepts (cv_pba A) g <-> C.PBA_accepts A (bk_pw g).
Proof.
  intros A g. split.
  - intros [run [Hinit [Hsteps Hacc]]].
    exists run. split; [exact Hinit|]. split; [|exact Hacc].
    intro i. destruct (Hsteps i) as [Hn [tt [Ht [Hs [Ht2 Hf]]]]].
    split; [exact Hn|].
    simpl in Ht. apply in_map_iff in Ht. destruct Ht as [t [<- Ht]].
    exists t. split; [exact Ht|]. split; [exact Hs|]. split; [exact Ht2|].
    simpl in Hf. rewrite Forall_map in Hf. exact Hf.
  - intros [run [Hinit [Hsteps Hacc]]].
    exists run. split; [exact Hinit|]. split; [|exact Hacc].
    intro i. destruct (Hsteps i) as [Hn [t [Ht [Hs [Ht2 Hf]]]]].
    split; [exact Hn|].
    exists (cv_pt t). split; [apply in_map; exact Ht|].
    split; [exact Hs|]. split; [exact Ht2|].
    simpl. rewrite Forall_map. exact Hf.
Qed.

Lemma enabled_cv : forall g i t,
  G.tba_transition_enabled g i (cv_tt t)
  <-> C.tba_transition_enabled (bk_word g) i t.
Proof.
  intros g i t. unfold G.tba_transition_enabled, C.tba_transition_enabled.
  simpl.
  assert (Hg : Forall (G.guard_item_holds g i)
                      (map (option_map cv_cc) (C.bt_guard t))
               <-> Forall (C.guard_item_holds (bk_word g) i) (C.bt_guard t)).
  { rewrite Forall_map. split; apply Forall_impl; intro c;
      destruct c as [[x cmp d]|]; simpl; try tauto; destruct cmp; simpl; tauto. }
  split; intros [Hl [Hgd Hr]]; refine (conj Hl (conj _ Hr));
    first [exact (proj1 Hg Hgd) | exact (proj2 Hg Hgd)].
Qed.

Lemma tba_acc_cv : forall T w,
  C.TBA_accepts T w <-> G.TBA_accepts (cv_tba T) w.
Proof.
  intros T w. unfold C.TBA_accepts, G.TBA_accepts. split.
  - intros [rho [Hb [Hc [run [Hinit [Hsteps Hacc]]]]]].
    exists (cv_word rho). split; [exact Hb|]. split; [exact Hc|].
    exists run. split; [exact Hinit|]. split; [|exact Hacc].
    intro i. destruct (Hsteps i) as [Hn [t [Ht [Hs [Ht2 Hen]]]]].
    split; [exact Hn|].
    exists (cv_tt t). split; [apply in_map; exact Ht|].
    split; [exact Hs|]. split; [exact Ht2|].
    apply enabled_cv. rewrite bk_cv_word. exact Hen.
  - intros [g [Hb [Hc [run [Hinit [Hsteps Hacc]]]]]].
    exists (bk_word g). split; [exact Hb|]. split; [exact Hc|].
    exists run. split; [exact Hinit|]. split; [|exact Hacc].
    intro i. destruct (Hsteps i) as [Hn [tt [Ht [Hs [Ht2 Hen]]]]].
    split; [exact Hn|].
    simpl in Ht. apply in_map_iff in Ht. destruct Ht as [t [<- Ht]].
    exists t. split; [exact Ht|]. split; [exact Hs|]. split; [exact Ht2|].
    apply enabled_cv. exact Hen.
Qed.

Lemma atom_ok_cv : forall a, G.atom_ok rst (cv_atom a) <-> C.atom_ok a.
Proof. intro a. destruct a; apply iff_refl. Qed.

(* ------------------------------------------------------------------ *)
(* MTL is an instance of the abstract theorem                         *)
(* ------------------------------------------------------------------ *)

Theorem MTL_correct_via_abstract :
  forall (A : C.PBuchi root) (w : C.timed_word),
    (forall s : C.pword root, C.action_consistent s ->
       (C.PBA_accepts A s <-> C.psat s 0 (C.T root))) ->
    C.well_formed root ->
    (C.msat w 0 root <-> C.TBA_accepts (C.compile_with A) w).
Proof.
  intros A w HA Hwf.
  set (phi := cv_ltl (C.T root)).
  assert (HClass : G.ClassC rst phi).
  { intros a Ha. unfold phi in Ha. rewrite ltl_atoms_cv in Ha.
    apply in_map_iff in Ha. destruct Ha as [b [<- Hb]].
    apply atom_ok_cv. unfold C.T in Hb. exact (C.T_at_atoms_ok Hb). }
  assert (HAG : forall g : G.pword K, G.action_consistent g ->
            (G.PBA_accepts (cv_pba A) g <-> G.psat g 0 phi)).
  { intros g Hg. unfold phi. rewrite pba_cv, psat_cv. apply HA. exact Hg. }
  pose proof (@G.abstract_compile_correct K cdec rst allc allc_complete
                phi (cv_pba A) w HClass HAG) as Habs.
  assert (Hcomp : G.compile_abs cdec rst allc_complete phi (cv_pba A)
                  = cv_tba (C.compile_with A)).
  { unfold G.compile_abs, C.compile_with, phi.
    rewrite ltl_atoms_cv, <- relax_cv, <- complete_cv. reflexivity. }
  rewrite Hcomp in Habs.
  rewrite tba_acc_cv, <- Habs.
  rewrite (P.EncodingCorrect_proved w Hwf).
  unfold G.L_timed. split.
  - intros [rho [Hb [Hc Hl]]].
    exists (cv_word rho). split; [exact Hb|]. split; [exact Hc|].
    unfold phi. apply lsat_cv. rewrite bk_cv_word. exact Hl.
  - intros [g [Hb [Hc Hl]]].
    exists (bk_word g). split; [exact Hb|]. split; [exact Hc|].
    unfold phi in Hl. apply lsat_cv in Hl. exact Hl.
Qed.

End Instance.

Print Assumptions MTL_correct_via_abstract.
