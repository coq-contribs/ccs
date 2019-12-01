(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                           Solange Coupet-Grimal                          *)
(*                                                                          *)
(*                                                                          *)                      
(*                   Laboratoire d'Informatique de Marseille                *)
(*                   URA CNRS 1787                                          *)
(*                   Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*                   e-mail:solange@gyptis.univ-mrs.fr                      *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                               Feb 7th 1995                               *)
(*                                                                          *)
(****************************************************************************)
(*                            Transition systems                            *)
(****************************************************************************)


Section TS.

Variable process action : Set.
Variable T : action.
Variable transition : process -> action -> process -> Prop.
Hypothesis eqT_dec : forall a : action, a = T \/ a <> T.

(*************************** Derivatives **********************************)

Inductive weak_derivative : process -> action -> process -> Prop :=
  | eps : forall p : process, weak_derivative p T p
  | w_single :
      forall (a : action) (p q : process),
      transition p a q -> weak_derivative p a q
  | w_tau_left :
      forall (a : action) (p p' q : process),
      transition p T p' -> weak_derivative p' a q -> weak_derivative p a q
  | w_tau_right :
      forall (a : action) (p q q' : process),
      transition q' T q -> weak_derivative p a q' -> weak_derivative p a q.
Hint Resolve w_single eps.

Inductive derivative : process -> action -> process -> Prop :=
  | single :
      forall (a : action) (p q : process),
      transition p a q -> derivative p a q
  | tau_left :
      forall (a : action) (p p' q : process),
      transition p T p' -> derivative p' a q -> derivative p a q
  | tau_right :
      forall (a : action) (p q q' : process),
      transition q' T q -> derivative p a q' -> derivative p a q.

Hint Resolve single.

Lemma deriv_weak_deriv :
 forall (p p' : process) (a : action),
 derivative p a p' -> weak_derivative p a p'.

intros p p' a H; elim H; clear H; auto.
clear p p' a.
intros a p p' q tr de we.
apply w_tau_left with p'; try trivial.

clear p p' a; intros a p q q' tr de we.
apply w_tau_right with q'; try trivial.

Qed.

Hint Resolve deriv_weak_deriv.

Lemma weak_deriv_deriv :
 forall (p p' : process) (a : action),
 weak_derivative p a p' -> a <> T -> derivative p a p'.
intros p p' a H; elim H; clear H p p' a.
unfold not in |- *.
intros p H; cut False; auto.
intros H1; elim H1.

intros a p q tr H; auto.

intros a p p' q tr we H_ind not_eq.
apply tau_left with p'; auto.

intros a p q q' tr we H_ind notEq.
apply tau_right with q'; auto.
Qed.

Hint Resolve weak_deriv_deriv.

Lemma weak_deriv_tau_left :
 forall (p p' p'' : process) (a : action),
 weak_derivative p T p' ->
 weak_derivative p' a p'' -> weak_derivative p a p''.

cut
 (forall (p : process) (a : action) (p' : process),
  weak_derivative p a p' ->
  a = T ->
  forall (p'' : process) (b : action),
  weak_derivative p' b p'' -> weak_derivative p b p'').
intros H p p' p'' a we we'; apply (H p T p'); auto.

simple induction 1.
simple induction 1; auto.

clear H p' a p.
intros a p q Tpq eqT p'' b we.
rewrite eqT in Tpq.
apply w_tau_left with q; auto.

clear H p p' a.
intros a p p' q Tpq we H_rec eqT p'' b we'.
apply w_tau_left with p'; auto.

clear H p a p'.
intros a p q q' Tr we H_rec eqT p'' b we'.
apply (H_rec eqT).
apply w_tau_left with q; auto.

Qed.

Lemma weak_deriv_tau_right :
 forall (p p' p'' : process) (a : action),
 weak_derivative p a p' ->
 weak_derivative p' T p'' -> weak_derivative p a p''.

cut
 (forall (p' : process) (a : action) (p'' : process),
  weak_derivative p' a p'' ->
  a = T ->
  forall (p : process) (b : action),
  weak_derivative p b p' -> weak_derivative p b p'').
intros H p p' p'' a we we1; apply (H p' T p''); auto.

intros p' a p'' H; elim H; clear H a p' p''; auto.
intros a p q tr eqT p0 b we.
apply w_tau_right with p; auto.
rewrite eqT in tr; auto.

intros a p q q' tr we H_rec eqT p0 b we'.
apply (H_rec eqT).
apply w_tau_right with p; auto.

intros a p q q' tr we H_rec eqT p0 b we'.
apply w_tau_right with q'; auto.

Qed.


Lemma w_deriv_tau_left :
 forall (p p' p'' : process) (a : action),
 weak_derivative p T p' -> derivative p' a p'' -> derivative p a p''.

cut
 (forall (p : process) (a : action) (p' : process),
  weak_derivative p a p' ->
  a = T ->
  forall (p'' : process) (b : action),
  derivative p' b p'' -> derivative p b p'').
intros H p p' p'' a de de1; apply (H p T p'); auto.

intros p a p' H; elim H; clear H a p p'; auto.
intros a p q Tpq eqT p'' b de.
rewrite eqT in Tpq.
apply tau_left with q; auto.

intros a p p' q tr de H_ind eqT p'' d de'.
apply tau_left with p'; auto.

intros a p q q' Tr de H_ind eqT p'' b de'.
apply (H_ind eqT).
apply tau_left with q; auto.

Qed.

Lemma w_deriv_tau_right :
 forall (p p' p'' : process) (a : action),
 derivative p a p' -> weak_derivative p' T p'' -> derivative p a p''.

cut
 (forall (p' : process) (a : action) (p'' : process),
  weak_derivative p' a p'' ->
  a = T ->
  forall (p : process) (b : action), derivative p b p' -> derivative p b p'').
intros H p p' p'' a de de1; apply (H p' T p''); auto.

intros p' a p'' H; elim H; clear H a p' p''.
auto.

intros a p q tr eqT p0 b we.
apply tau_right with p; auto.
rewrite eqT in tr; auto.

intros a p q q' tr we H_rec eqT p0 b we'.
apply (H_rec eqT).
apply tau_right with p; auto.

intros a p q q' tr we H_rec eqT p0 b we'.
apply tau_right with q'; auto.

Qed.

Lemma deriv_tau_left :
 forall (p p' p'' : process) (a : action),
 derivative p T p' -> derivative p' a p'' -> derivative p a p''.

intros p p' p'' a pp' p_p''.
apply w_deriv_tau_left with p'; auto.
Qed.

Lemma deriv_tau_right :
 forall (p p' p'' : process) (a : action),
 derivative p a p' -> derivative p' T p'' -> derivative p a p''.

intros p p' p'' a de1 de2.
apply w_deriv_tau_right with p'; auto.
Qed.

(************************* Strong equivalence ******************************)

CoInductive strong_eq : process -> process -> Prop :=
    str_eq :
      forall p q : process,
      (forall (a : action) (p' : process),
       transition p a p' ->
       exists q' : process, transition q a q' /\ strong_eq p' q') ->
      (forall (a : action) (q' : process),
       transition q a q' ->
       exists p' : process, transition p a p' /\ strong_eq p' q') ->
      strong_eq p q.

(******************* strong_eq is an equivalence relation ******************)


Lemma refl_strong_eq : forall p : process, strong_eq p p.
cofix refl_strong_eq.
intros p; apply str_eq.
intros a p' trans; exists p'; split; auto.
intros a p' trans; exists p'; split; auto.
Qed.

Hint Resolve refl_strong_eq.

Lemma sym_strong_eq : forall p q : process, strong_eq p q -> strong_eq q p.
cofix sym_strong_eq.
intros p q H; inversion_clear H.
apply str_eq.
intros a q'.
intros trans.
elim (H1 a q' trans); clear H1.
intros p' H; elim H; exists p'; split; auto.
intros a p' trans.
elim (H0 a p' trans); clear H0.
intros q' H; elim H; clear H.
intros trans1 str.
exists q'; split; auto.
Qed.

Hint Immediate sym_strong_eq.

Lemma trans_strong_eq :
 forall p q r : process, strong_eq p q -> strong_eq q r -> strong_eq p r.

cofix trans_strong_eq.
intros p q r pq qr.
inversion_clear pq; inversion_clear qr.
apply str_eq.
intros a p' tp.
cut (exists q' : process, transition q a q' /\ strong_eq p' q').
intros G; elim G; clear G.
intros q' G; elim G.
intros tq pq'; elim (H1 a q' tq).
clear G.
intros r' G; elim G; clear G.
intros tr qr'; exists r'; split; auto.
apply trans_strong_eq with q'; auto.
elim (H a p' tp).
intros q' G; elim G; clear G.
intros tq pq'.
exists q'; split; auto.
intros a r' tr.
cut (exists q' : process, transition q a q' /\ strong_eq q' r').
intros G; elim G; clear G.
intros q' G; elim G; clear G.
intros tq qr'.
elim (H0 a q' tq).
intros p' G; elim G; clear G.
intros tp pq'; exists p'; split; auto.
apply trans_strong_eq with q'; auto.
elim (H2 a r' tr).
intros q' G; elim G; clear G.
intros tq qr'; exists q'; split; auto.
Qed.

(**************************** Weak equivalence *****************************)

CoInductive weak_eq : process -> process -> Prop :=
    w_eq :
      forall p q : process,
      (forall (a : action) (p' : process),
       transition p a p' ->
       exists q' : process, weak_derivative q a q' /\ weak_eq p' q') ->
      (forall (a : action) (q' : process),
       transition q a q' ->
       exists p' : process, weak_derivative p a p' /\ weak_eq p' q') ->
      weak_eq p q.

(****************** weak_eq is an equivalence Relation *********************)

Lemma refl_weak_eq : forall p : process, weak_eq p p.
cofix refl_weak_eq.
intros p; apply w_eq.
intros a p' trans; exists p'; split; auto.
intros a p' trans; exists p'; split; auto.
Qed.

Hint Resolve refl_weak_eq.

Lemma sym_weak_eq : forall p q : process, weak_eq p q -> weak_eq q p.
cofix sym_weak_eq.
intros p q H; inversion_clear H.
apply w_eq.
intros a q'.
intros trans.
elim (H1 a q' trans); clear H1.
intros p' H; elim H; exists p'; split; auto.
intros a p' trans.
elim (H0 a p' trans); clear H0.
intros q' H; elim H; clear H.
intros trans1 str.
exists q'; split; auto.
Qed.

Hint Immediate sym_weak_eq.


        (*___________ Proof of Transitivity ______________*)


Remark Hint_Trans :
 forall (q q' r : process) (a : action),
 weak_derivative q a q' ->
 weak_eq q r -> exists r' : process, weak_derivative r a r' /\ weak_eq q' r'.

intros q q' r a H.
generalize r; clear r.
elim H; clear H.
intros p r we; exists r; split; auto.

clear a q q'; intros a p q tr r we.
inversion_clear we.
apply (H a q tr).

clear q q' a; intros a p p' q tr wd H_ind r we.
cut (exists r'' : process, weak_derivative r T r'' /\ weak_eq p' r'').
intros H.
elim H; clear H.
intros r'' Hr''; elim Hr''; clear Hr''; intros rTr'' we'.
cut (exists r' : process, weak_derivative r'' a r' /\ weak_eq q r').
intros H; elim H; clear H.
intros r' Hr'; elim Hr'; clear Hr'; intros wde we''.
exists r'; split; auto.
apply (weak_deriv_tau_left r r'' r' a); auto.

apply (H_ind r''); auto.

inversion_clear we.
apply (H T p' tr); auto.

clear q q' a; intros a p q q' tr wd H_ind r we.
cut (exists r'' : process, weak_derivative r a r'' /\ weak_eq q' r'').
intros H; elim H; clear H.
intros r'' Hr''; elim Hr''; clear Hr''; intros wd' we'.
cut (exists r' : process, weak_derivative r'' T r' /\ weak_eq q r').
intros H; elim H; clear H.
intros r' Hr'; elim Hr'; intros wd'' we''.
exists r'; split; auto.
apply (weak_deriv_tau_right r r'' r' a); auto.

inversion_clear we'; auto.

apply (H_ind r we); auto.

Qed.

Lemma trans_weak_eq :
 forall p q r : process, weak_eq p q -> weak_eq q r -> weak_eq p r.
cofix trans_weak_eq.
intros p q r pq qr.
apply w_eq.

intros a p' tr.
cut (exists q' : process, weak_derivative q a q' /\ weak_eq p' q').
intros H; elim H; clear H; intros q' Hq'; elim Hq'; clear Hq'; intros wd we.
cut (exists r' : process, weak_derivative r a r' /\ weak_eq q' r').
intros Hr'; elim Hr'; clear Hr'; intros r' Hr'; elim Hr'; clear Hr';
 intros wd' we'.
exists r'; split; auto.
apply trans_weak_eq with q'; auto.
apply (Hint_Trans q q' r); auto.
inversion_clear pq; auto.

intros a r' tr.
cut (exists q' : process, weak_derivative q a q' /\ weak_eq q' r').
intros H; elim H; clear H; intros q' Hq'; elim Hq'; clear Hq'; intros wd we.
cut (exists p' : process, weak_derivative p a p' /\ weak_eq q' p').
intros H; elim H; clear H; intros p' Hp'; elim Hp'; clear Hp'; intros wd' we'.
exists p'; split; auto.
apply trans_weak_eq with q'; auto.
apply (Hint_Trans q q' p a); auto.
inversion_clear qr; auto.
Qed.


(******** weaq_eq1 : an equivalent definition for weak equivalence *********)


CoInductive weak_eq1 : process -> process -> Prop :=
    w_eq1 :
      forall p q : process,
      (forall (a : action) (p' : process),
       derivative p a p' ->
       exists q' : process, weak_derivative q a q' /\ weak_eq1 p' q') ->
      (forall (a : action) (q' : process),
       derivative q a q' ->
       exists p' : process, weak_derivative p a p' /\ weak_eq1 p' q') ->
      weak_eq1 p q.

Lemma weak_eq_deriv :
 forall p q : process,
 weak_eq p q ->
 forall (a : action) (p' : process),
 derivative p a p' ->
 exists q' : process, weak_derivative q a q' /\ weak_eq p' q'.

intros p q we a p' de.
generalize we.
generalize q.
elim de; clear de we a p p' q.
intros a p p' tr q we.
inversion we.
elim (H a p' tr); clear H H0.
intros q' H; elim H; clear H; intros wde we'.
exists q'; split; assumption.

intros a p p1 p' tr de H_ind q we.
cut (exists q1 : process, weak_derivative q T q1 /\ weak_eq p1 q1).
intros H; elim H; clear H.
intros q1 H; elim H; clear H; intros wde we'.
cut (exists q' : process, weak_derivative q1 a q' /\ weak_eq p' q').
intros H; elim H; clear H.
intros q' H; elim H; clear H; intros wde1 we1.
exists q'; split; try try try trivial.
apply weak_deriv_tau_left with q1; try try trivial.

apply (H_ind q1); try try trivial.

inversion_clear we.
apply (H T p1); try try trivial.

intros a p p' p1 tr de H_ind q we.
cut (exists q1 : process, weak_derivative q a q1 /\ weak_eq p1 q1).
intros H; elim H; clear H.
intros q1 H; elim H; clear H; intros wde we1.
cut (exists q' : process, weak_derivative q1 T q' /\ weak_eq p' q').
intros H; elim H; clear H.
intros q' H; elim H; clear H; intros wde1 we'.
exists q'; split; try try try trivial.
apply weak_deriv_tau_right with q1; try try trivial.

inversion_clear we1.
apply (H T p'); try try trivial.

apply (H_ind q we).
Qed.

Lemma weak_eq_deriv_sym :
 forall p q : process,
 weak_eq p q ->
 forall (a : action) (q' : process),
 derivative q a q' ->
 exists p' : process, weak_derivative p a p' /\ weak_eq p' q'.

intros p q we a q' de.
cut (weak_eq q p); auto.
intros we'.
elim (weak_eq_deriv q p we' a q' de).
intros p' H; elim H; intros w_de we''.
exists p'; split; auto.

Qed.


Lemma weak_eq1_weak_eq : forall p q : process, weak_eq1 p q -> weak_eq p q.
cofix weak_eq1_weak_eq.
intros p q we1.
apply w_eq.
intros a p' tr.
inversion we1.
elim (H a p').
intros q' G; elim G; clear G; intros wde we1'.
exists q'; split; try try try trivial.
apply weak_eq1_weak_eq; assumption.

apply single; assumption.

intros a q' tr.
inversion we1.
elim (H0 a q').
intros p' G; elim G; intros wde we1'.
exists p'; split; try try try trivial.
apply weak_eq1_weak_eq; assumption.

apply single; try try trivial.
Qed.

Hint Immediate weak_eq1_weak_eq.

Lemma weak_eq_weak_eq1 : forall p q : process, weak_eq p q -> weak_eq1 p q.

cofix weak_eq_weak_eq1.
intros p q we.
apply w_eq1.
intros a p' de.
cut (exists q' : process, weak_derivative q a q' /\ weak_eq p' q').
intros H; elim H; clear H.
intros q' H; elim H; clear H; intros wde we'.
exists q'; split; try try try trivial.
apply weak_eq_weak_eq1; try try trivial.

elim (weak_eq_deriv p q we a p' de).
intros q' H; exists q'; assumption.

intros a q' de.
cut (exists p' : process, weak_derivative p a p' /\ weak_eq p' q').
intros H; elim H; clear H.
intros p' H; elim H; clear H; intros wde we'.
exists p'; split; try try try try trivial.
apply weak_eq_weak_eq1; try try try trivial.

elim (weak_eq_deriv_sym p q we a q' de).
intros p' H; exists p'; assumption.

Qed.

Hint Immediate weak_eq_weak_eq1.


(******************** weak_eq1 is an equivalence relation ******************)

Lemma refl_weak_eq1 : forall p : process, weak_eq1 p p.

auto.
Qed.

Lemma sym_weak_eq1 : forall p q : process, weak_eq1 p q -> weak_eq1 q p.

intros.
apply weak_eq_weak_eq1.
apply sym_weak_eq; auto.

Qed.

Lemma trans_weak_eq1 :
 forall p q r : process, weak_eq1 p q -> weak_eq1 q r -> weak_eq1 p r.

intros p q r pq qr.
apply weak_eq_weak_eq1.
apply trans_weak_eq with q; auto.

Qed.

(****** Observational equivalence: definition, reflexivity,symmetry ******)

Definition obs_eq (p q : process) : Prop :=
  (forall (a : action) (p' : process),
   transition p a p' ->
   exists q' : process, derivative q a q' /\ weak_eq p' q') /\
  (forall (a : action) (q' : process),
   transition q a q' ->
   exists p' : process, derivative p a p' /\ weak_eq p' q').

Lemma refl_obs_eq : forall p : process, obs_eq p p.
unfold obs_eq in |- *.
split; intros a p' trans; exists p'; split; auto.
Qed.

Hint Immediate refl_obs_eq.

Lemma sym_obs_eq : forall p q : process, obs_eq p q -> obs_eq q p.
unfold obs_eq in |- *.
intros p q.
intros H; elim H; clear H; intros Hp Hq.
split.
auto.
intros a q' tr.
elim (Hq a q' tr); clear Hq.
intros p' H; elim H; clear H; intros de we; exists p'; split; auto.
intros a p' tr.
elim (Hp a p' tr); clear Hp.
intros q' H; elim H; clear H; intros de we; exists q'; split; auto.
Qed.

Hint Immediate sym_obs_eq.


(**** obs_eq1 : an equivalent definition for observational equivalence ****)


Definition obs_eq1 (p q : process) : Prop :=
  (forall (a : action) (p' : process),
   derivative p a p' ->
   exists q' : process, derivative q a q' /\ weak_eq p' q') /\
  (forall (a : action) (q' : process),
   derivative q a q' ->
   exists p' : process, derivative p a p' /\ weak_eq p' q').


Lemma obs_eq1_obs_eq : forall p q : process, obs_eq1 p q -> obs_eq p q.
intros p q oe.
unfold obs_eq in |- *; split; elim oe; auto.
Qed.

Hint Resolve obs_eq1_obs_eq.

Remark half_obs_eq_obs_eq1 :
 forall p q : process,
 obs_eq p q ->
 forall (a : action) (p' : process),
 derivative p a p' -> exists q' : process, derivative q a q' /\ weak_eq p' q'.

intros p q oe a p' de; generalize oe; generalize q; clear oe q.
elim de; clear de a p p'.
intros a p p' tr q oe.
unfold obs_eq in oe; elim oe; clear oe; intros oe_l oe_r; clear oe_r.
auto.

intros a p p1 p' tr de H_ind q oe.
cut (exists q1 : process, derivative q T q1 /\ weak_eq p1 q1).
intros H; elim H; clear H.
intros q1 H; elim H; clear H; intros de' we.
cut (exists q' : process, weak_derivative q1 a q' /\ weak_eq p' q').
intros H; elim H; clear H.
intros q' H; elim H; intros de'' we'.
exists q'; split; auto.
elim eqT_dec with a.
intros a_T.
rewrite a_T in de''.
rewrite a_T.
apply w_deriv_tau_right with q1; auto.

intros dif_a_T.
apply weak_deriv_deriv.
apply weak_deriv_tau_left with q1; auto.

auto.

cut (weak_eq1 p1 q1); auto.
intros we1.
cut (exists q' : process, weak_derivative q1 a q' /\ weak_eq1 p' q').
intros H; elim H; clear H; intros q' H; elim H; intros de'' we1'; exists q';
 split; auto.

inversion_clear we1; auto.

unfold obs_eq in oe; elim oe; auto.

intros a p p' p1 tr de H_ind q oe.
cut (exists q1 : process, derivative q a q1 /\ weak_eq p1 q1).
intros H; elim H; clear H.
intros q1 H; elim H; clear H; intros de1 we1.
cut (exists q' : process, weak_derivative q1 T q' /\ weak_eq p' q').
intros H; elim H; clear H; intros q' H; elim H; intros de2 we.
exists q'; split; auto.
apply w_deriv_tau_right with q1; auto.

inversion_clear we1; auto.

apply (H_ind q); auto.

Qed.

Lemma obs_eq_obs_eq1 : forall p q : process, obs_eq p q -> obs_eq1 p q.

intros p q oe.
unfold obs_eq1 in |- *; split.
exact (half_obs_eq_obs_eq1 p q oe).

cut
 (forall (a : action) (q' : process),
  derivative q a q' ->
  exists p' : process, derivative p a p' /\ weak_eq q' p').
intros H a q' de.
elim (H a q' de); clear H.
intros p' H; elim H; clear H; intros; exists p'; split; auto.

cut (obs_eq q p); auto.
exact (half_obs_eq_obs_eq1 q p).

Qed.

Hint Resolve obs_eq_obs_eq1.

(************* obs_eq1 ans obs_eq are equivalence relations ***************)

Lemma refl_obs_eq1 : forall p : process, obs_eq1 p p.

auto.
Qed.

Hint Immediate refl_obs_eq1.

Lemma sym_obs_eq1 : forall p q : process, obs_eq1 p q -> obs_eq1 q p.
intros.
apply obs_eq_obs_eq1.
apply sym_obs_eq.
auto.
Qed.

Hint Immediate sym_obs_eq1.

Remark half_trans_obs_eq1 :
 forall p q r : process,
 obs_eq1 p q ->
 obs_eq1 q r ->
 forall (a : action) (p' : process),
 derivative p a p' -> exists r' : process, derivative r a r' /\ weak_eq p' r'.

intros p q r pq qr a p' de.
cut (exists q' : process, derivative q a q' /\ weak_eq p' q').
intros H; elim H; clear H; intros q' H; elim H; intros de' we; clear H.
elim qr; clear qr; intros qr_l qr_r; clear qr_r.
elim (qr_l a q' de').
intros r' H; elim H; clear H; intros de'' we'; exists r'; split;
 auto.
apply trans_weak_eq with q'; auto.

elim pq; intros pq_l pq_r; clear pq_r; auto.

Qed.

Lemma trans_obs_eq1 :
 forall p q r : process, obs_eq1 p q -> obs_eq1 q r -> obs_eq1 p r.

intros p q r pq qr; unfold obs_eq in |- *; split.
exact (half_trans_obs_eq1 p q r pq qr).

cut
 (forall (a : action) (r' : process),
  derivative r a r' ->
  exists p' : process, derivative p a p' /\ weak_eq r' p').
intros H a r' de.
elim (H a r' de); clear H; intros p' H; elim H; clear H; intros; exists p';
 split; auto.

cut (obs_eq1 q p); auto.
cut (obs_eq1 r q); auto.
exact (half_trans_obs_eq1 r q p).
Qed.

Lemma trans_obs_eq :
 forall p q r : process, obs_eq p q -> obs_eq q r -> obs_eq p r.
intros p q r pq qr.
apply obs_eq1_obs_eq.
apply trans_obs_eq1 with q; auto.

Qed.

(*************************** p~q->p=q->p~~q *******************************)

Lemma strong_weak : forall p q : process, strong_eq p q -> weak_eq p q.
cofix strong_weak.
intros p q.
intros H.
inversion_clear H.
apply w_eq.
intros a p' trans.
elim (H0 a p' trans).
clear H0.
intros q' H; elim H; clear H.
intros trans1 Str.
exists q'.
split.
apply w_single.
try try trivial.

apply strong_weak; try try trivial.

clear H0.
intros a q' trans.
elim (H1 a q' trans); clear H1.
intros p' H; elim H; clear H.
intros trans1 Str; exists p'; split.
apply w_single; try try trivial.

apply strong_weak; try try trivial.
Qed.

Hint Resolve strong_weak.

Lemma strong_obs : forall p q : process, strong_eq p q -> obs_eq p q.

intros p q H.
inversion_clear H.
unfold obs_eq in |- *; split.
clear H1; intros a p' trans.
elim (H0 a p' trans); clear H0.
intros q' H; elim H; clear H.
intros trans1 Str; exists q'; auto.
clear H0; intros a q' trans.
elim (H1 a q' trans); clear H1.
intros p' H; elim H; clear H.
intros trans1 Str; exists p'; split; auto.
Qed.

Hint Resolve strong_obs.

Lemma obs_weak : forall p q : process, obs_eq p q -> weak_eq p q.

unfold obs_eq in |- *.
intros p q H; elim H; clear H; intros H1 H2.
apply w_eq.
intros a p' tr.
elim (H1 a p' tr).
intros q' H; elim H; clear H; intros de we.
exists q'; split; auto.
intros a q' tr.
elim (H2 a q' tr).
intros p' H; elim H; clear H; intros de we.
exists p'; split; auto.
Qed.


End TS.
