Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Init.Datatypes.
Require Export Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import Omega.

(* "Wf_nat" Incluye prueba de que los naturales son bien fundados,
de modo que se pueda demostrar terminación mediante un variante
de tipo natural. *)
Require Import Coq.Arith.Wf_nat.

Fixpoint eqb (b1 : bool) (b2 : bool) : bool :=
match b1 with
| true => match b2 with
  | true => true
  | false => false
  end
| false => match b2 with
  | true => false
  | false => true
  end
end.

Lemma correctitud_eqb: forall b1 b2, eqb b1 b2 = true <-> b1 = b2.
Proof.
intros.
destruct b1.
split.
intro.
destruct b2.
reflexivity.
simpl in H.
congruence.
intro.
destruct b2.
simpl.
reflexivity.
congruence.
split.
intro.
destruct b2.
simpl in H.
congruence.
reflexivity.
intro.
destruct b2.
congruence.
simpl.
reflexivity.
Qed.

(* Definición de suma y producto *)

Fixpoint suma (m:nat) (n:nat) : nat :=
match m with 
  | 0 => n
  | S k => S (suma k n)
end.
Notation "m + n" := (suma m n) (at level 50, left associativity) 
                       : nat_scope.

Fixpoint mult (m:nat) (n:nat) : nat :=
match m with 
  | 0 => 0
  | S k => n + (mult k n)
end.
Notation "m * n" := (mult m n) : nat_scope.

(* Demostraciones útiles sobre suma y producto *)

Lemma suma_0: forall n, n + 0 = n.
Proof.
induction n.
simpl. reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Lemma suma_Sn: forall m, forall n, n + S m = S (n + m).
Proof.
induction n.
simpl. reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Lemma suma_conmutativa: forall m, forall n, m + n = n + m.
Proof.
intros.
induction m.
simpl. 
rewrite -> suma_0 with (n:=n).
reflexivity.
simpl.
rewrite -> IHm.
rewrite -> suma_Sn with (n:=n) (m:=m).
reflexivity.
Qed.

Lemma suma_asociativa: forall n, forall m, forall k, (n + m) + k = n + (m + k).
Proof.
induction n.
simpl.
reflexivity.
simpl.
intros.
rewrite <-  IHn.
reflexivity.
Qed.

Lemma suma_ambos_lados: forall m n k:nat, m = n -> m + k = n + k.
Proof.
intros.
destruct n.
rewrite <- H.
reflexivity.
rewrite <- H.
reflexivity.
Qed.

Lemma mult_0: forall m, m * 0 = 0.
Proof.
induction m.
simpl. reflexivity.
simpl.
rewrite -> IHm.
reflexivity.
Qed.

Lemma suma_n_S: forall m n, S n + m = n + S m.
Proof.
induction n.
simpl.
reflexivity.
simpl.
simpl in IHn.
rewrite IHn.
reflexivity.
Qed.

Lemma suma_swap: forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
intros n m p.
rewrite <- suma_asociativa.
rewrite <- suma_asociativa.
assert (H: suma n m = suma m n).
rewrite -> suma_conmutativa.
reflexivity.
rewrite -> H at 1.
reflexivity.
Qed.

Lemma mult_Sn: forall m, forall n, m * (S n) = m + (m * n).
Proof.
intros.
induction m.
reflexivity.
simpl.
rewrite -> IHm.
rewrite suma_swap.
reflexivity.
Qed.

Lemma mult_conmutativa: forall m n, m * n = n * m.
Proof.
intros.
induction m.
simpl.
rewrite -> mult_0.
reflexivity.
simpl.
rewrite -> mult_Sn.
rewrite -> IHm.
reflexivity.
Qed.

Lemma mult_distributiva: forall m n p, (m + n) * p =  m*p + n*p.
Proof.
intros.
induction p.
rewrite mult_0.
rewrite mult_0.
rewrite mult_0.
simpl.
reflexivity.
rewrite mult_Sn.
rewrite mult_Sn.
rewrite mult_Sn.
rewrite IHp.
rewrite (suma_asociativa m (m*p) (n + n*p)).
rewrite <- (suma_asociativa (m*p) n (n*p)).
rewrite (suma_conmutativa (m*p) n).
rewrite (suma_asociativa n (m*p) _).
rewrite <- (suma_asociativa  m n _).
reflexivity.
Qed.

Lemma mult_asociativa: forall m n p, m * n * p = m * (n * p).
Proof.
intros.
induction m.
simpl.
reflexivity.
simpl.
rewrite <- IHm.
rewrite mult_distributiva.
reflexivity.
Qed.

(* predecesor y resta *)

Fixpoint pred (m : nat) : nat :=
match m with 
  | 0 => 0
  | S k => k
end.

Fixpoint menos (m : nat) (n:nat) : nat :=
match n with
  | 0 => m
  | S k => pred (menos m k)
end.
Notation "m - n" := (menos m n) : nat_scope.

Lemma suc_iny: forall m n:nat, S m = S n <-> m = n.
Proof.
intros.
split.
congruence.
intro.
congruence.
Qed.

(* Igualdad *)
Fixpoint eq_nat (m:nat) (n:nat) : bool :=
match m with
  | 0 => match n with
    | 0 => true
    | S _ => false
    end
 | S k => match n with
   | 0 => false
   | S p => eq_nat k p
   end
end.

Lemma correctitud_eq_nat: forall m n, eq_nat m n = true <-> m = n.
Proof.
induction m.
destruct n.
simpl.
split.
intro.
reflexivity.
intro.
reflexivity.
split.
intro.
simpl in H.
congruence.
intro.
congruence.
intro.
split.
intro.
induction n.
simpl in H.
congruence.
simpl in H.
specialize IHm with n.
destruct IHm.
pose (nH := H0 H).
rewrite <- suc_iny in nH. 
exact nH.
intro.
induction n.
congruence.
specialize IHm with n.
destruct IHm.
rewrite suc_iny in H.
pose (nH := H1 H).
simpl.
exact nH.
Qed.

(* Menor o igual *)

Fixpoint leq_nat (m : nat) (n : nat) : bool :=
match m with
  | 0 =>  true
  | S k => match n with
    | 0 => false
    | S j => leq_nat k j
  end
end.

Lemma def_leq_nat: forall m n, leq_nat m n = true <-> exists k, m + k = n.
Proof.
induction m.
simpl.
intro n.
split.
intro. 
exists n.
reflexivity.
intro.
reflexivity.
induction n.
split.
intro.
simpl in H.
congruence.
intro. simpl in H. 
inversion H.
discriminate H0.
simpl.
specialize IHm with n.
split.
destruct IHm.
intro.
pose (nH := H H1).
destruct nH.
exists x.
rewrite suc_iny.
exact H2.
intro.
destruct H.
rewrite suc_iny in H.
assert (exists k, (m + k) = n).
exists x.
exact H.
destruct IHm.
pose (nnH := H2 H0).
exact nnH.
Qed.

Lemma correctitud_leq_nat: forall m n:nat, leq_nat m n = true <-> m <= n.
Proof.
induction m.
simpl.
intro n.
split.
intro.
induction n.
apply le_n.
apply le_S.
exact IHn.
intro. reflexivity.
induction n.
simpl.
split.
intro.
congruence.
intro.
inversion H.
simpl.
specialize IHm with n.
destruct IHm.
split.
intro.
pose (nH := H H1).
apply le_n_S in nH.
exact nH.
intro.
apply le_S_n in H1.
pose (nH := H0 H1).
exact nH.
Qed.

(* Menor *)

Fixpoint lt_nat (m:nat) (n:nat) : bool :=
match m,n with 
  | 0,0 => false
  | 0, S _ => true
  | S _, 0 => false
  | S x, S y => lt_nat x y
end.

Lemma correctitud_lt_nat: forall m n, lt_nat m n = true <-> m < n.
Proof.
induction m.
intro.
destruct n.
simpl.
split.
intro.
congruence.
intro.
inversion H.
simpl.
split.
intro.
unfold lt.
apply le_n_S.
apply le_0_n.
intro.
reflexivity.
induction n.
simpl.
split.
intro.
congruence.
intro.
inversion H.
split.
intro.
apply lt_n_S.
simpl in H.
specialize IHm with n.
destruct IHm.
pose (nH := H0 H).
exact nH.
intro.
simpl.
apply lt_S_n in H.
specialize IHm with n.
destruct IHm.
pose (nH := H1 H).
exact nH.
Qed.

(* Logica *) Lemma bicond P S T: (P <-> S) -> (S <-> T) -> (P <-> T).
  intuition.
Qed.

(* Logica *) Lemma bicon_conm P S: (P <-> S) -> (S <-> P).
  intuition.
Qed.

Lemma def_lt_nat: forall m n, lt_nat m n = true <-> exists k, m + S k = n.
Proof.
induction m.
destruct n.
simpl.
split.
intro.
inversion H.
intro.
inversion H.
inversion H0.
split.
intro.
exists n.
simpl. reflexivity.
intro.
simpl. reflexivity.
induction n.
split.
intro.
simpl in H. inversion H.
intro.
simpl. simpl in H.
inversion H.
inversion H0.
split.
intro.
specialize IHm with n.
simpl in H.
destruct IHm.
pose (nH := H0 H).
inversion nH.
simpl.
exists x.
rewrite H2.
reflexivity.
intro.
specialize IHm with n.
destruct IHm.
simpl.
simpl in H.
inversion H.
rewrite -> suc_iny in H2.
assert(exists k, m + S k = n).
exists x.
exact H2.
pose (nH := H1 H3).
exact nH.
Qed.

Lemma def_lt: forall m n, m < n <-> exists k, m + S k = n.
intros.
assert (lt_nat m n = true <-> m < n).
apply correctitud_lt_nat.
apply bicon_conm in H.
assert(lt_nat m n = true <-> exists k, m + S k = n).
apply def_lt_nat.
apply (bicond (m<n) (lt_nat m n = true) (exists k, m + S k = n)).
exact H.
exact H0.
Qed.

Lemma lt_S_S: forall m n, S m < S n <-> m < n.
Proof.
intros.
split.
intro.
apply lt_S_n.
exact H.
intro.
apply def_lt.
apply def_lt in H.
destruct H.
simpl.
exists x.
rewrite H.
reflexivity.
Qed.

Lemma def_leq: forall m n, m <= n <-> exists k, m + k = n.
intros.
assert (leq_nat m n = true <-> m <= n).
apply correctitud_leq_nat.
apply bicon_conm in H.
assert(leq_nat m n = true <-> exists k, m + k = n).
apply def_leq_nat.
apply (bicond (m<=n) (leq_nat m n = true) (exists k, m + k = n)).
exact H.
exact H0.
Qed.

Lemma leq_S_S: forall m n, S m <= S n <-> m <= n.
Proof.
intros.
split.
intro.
apply def_leq.
apply def_leq in H.
simpl in H.
destruct H.
exists x.
rewrite suc_iny in H.
exact H.
intro.
apply correctitud_leq_nat.
apply correctitud_leq_nat in H.
simpl.
exact H.
Qed.

Lemma leq_nat_false: forall m n, leq_nat m n = false <-> lt_nat n m = true.
Proof.
induction m.
intros.
split.
intro H.
simpl in H. congruence.
intros.
induction n.
simpl in H.
congruence.
simpl in H.
congruence.
induction n.
split.
intro.
simpl.
reflexivity.
intro.
simpl.
reflexivity.
split. 
intro.
simpl.
simpl in H.
specialize IHm with n.
destruct IHm.
pose(nH := H0 H).
exact nH.
intro.
simpl.
simpl in H.
specialize IHm with n.
destruct IHm.
pose(nH := H1 H).
exact nH.
Qed.

Lemma correctitud_leq_nat_false: forall m n, leq_nat m n = false <-> n < m.
Proof.
intros.
split.
intro.
induction m.
simpl in H.
congruence.
induction n.
rewrite def_lt.
simpl.
exists m.
reflexivity.
apply lt_S_S.
simpl in H.
apply leq_nat_false in H.
apply correctitud_lt_nat.
exact H.
intro.
induction m.
inversion H.
induction n.
simpl.
reflexivity.
simpl.
rewrite lt_S_S in H.
apply leq_nat_false.
apply correctitud_lt_nat.
exact H.
Qed.

Lemma correctitud_lt_nat_false: forall m n, lt_nat m n = false <-> n <= m.
Proof.
induction m.
intros.
split.
intro.
destruct n.
apply le_n.
simpl in H.
congruence.
intro.
destruct n.
simpl.
reflexivity.
inversion H.
induction n.
split.
intro.
apply le_0_n.
intro.
simpl.
reflexivity.
split.
intro.
simpl in H.
specialize IHm with n.
destruct IHm.
pose (nH := H0 H).
apply leq_S_S.
exact nH.
intro.
simpl.
specialize IHm with n.
rewrite IHm.
rewrite leq_S_S in H.
exact H.
Qed.


(* Lemas de resta y pred*) 
Lemma sum_res_n: forall m n:nat, (suma m n) - m = n.
Proof.
induction m.
intros.
simpl.
reflexivity.
intros.
rewrite suma_n_S.
simpl.
rewrite IHm.
simpl.
reflexivity.
Qed.

Lemma resta_suma_n: forall m n:nat, 
leq_nat n m = true -> (menos m n) + n = m.
Proof.
intros.
apply def_leq_nat in H.
destruct H.
rewrite <- H.
rewrite sum_res_n.
apply suma_conmutativa.
Qed.


Lemma pred_suma: forall m n, 0 < m -> (pred m) + n = pred (m + n).
Proof.
intros.
induction m.
simpl.
destruct n.
simpl.
reflexivity.
inversion H.
simpl.
reflexivity.
Qed.

Lemma S_pred:forall m, lt_nat  0 m = true -> S (pred m) = m.
intros.
destruct m.
simpl in H.
congruence.
simpl.
reflexivity.
Qed.

Lemma resta_ambos_lados: forall m n k:nat, m = n -> menos m k = menos n k. 
Proof.
intros.
induction k.
simpl.
rewrite H.
reflexivity.
simpl.
rewrite IHk.
reflexivity.
Qed.

Lemma pred_ambos_lados: forall m n, m = n -> pred m = pred n.
Proof.
intros.
destruct m.
destruct n.
simpl.
reflexivity.
congruence.
congruence.
Qed.

(* Pruebas de terminación *)
Lemma div_term: forall m n, lt_nat 0 n = true -> leq_nat n m = true -> menos m n < m.
Proof.
intros.
apply def_lt_nat in H.
apply def_leq_nat in H0.
simpl in H.
inversion H.
inversion H0.
remember H2.
clear Heqe.
SearchAbout menos.
apply resta_ambos_lados with (n+x0) m n in H2. 
rewrite sum_res_n with n x0 in H2.
assert (exists k, x0 + S k = m).
rewrite <- H1 in e.
exists x.
rewrite suma_conmutativa.
exact e.
rewrite -> H2 in H3.
apply def_lt.
exact H3.
Qed.

Require Recdef.
Function div (m:nat) (n:nat) {measure (fun n => n) m} : nat :=
match lt_nat 0 n with
  | false => 0
  | true => match leq_nat n m with
      | false => 0
      | true => S (div (menos m n) n)
  end
end.
Proof.
apply div_term.
Qed.

Function modulo (m:nat) (n:nat) {measure (fun n => n) m} : nat :=
match lt_nat 0 n with
  | false => 1
  | true => match leq_nat n m with
      | false => m
      | true => modulo (menos m n) n
  end
end.
Proof.
apply div_term.
Qed.

Lemma pred_resta: forall m n, pred(n - m) = (pred n) - m.
intros.
induction m.
simpl.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
Qed.

Lemma n_menos_n: forall n, n - n = 0.
Proof.
induction n.
simpl.
reflexivity.
simpl.
rewrite pred_resta.
simpl.
exact IHn.
Qed.


Lemma suma_resta_n: forall m n, (n + m) - n = m.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite pred_resta.
simpl.
exact IHn.
Qed.

Lemma leq_men_o_igual: forall x y:nat, x <= y -> x = y \/ x < y.
Proof.
intros.
rewrite def_leq in H.
destruct H.
destruct x0.
rewrite suma_0 in H.
apply or_introl.
exact H.
assert(exists k, x + S k = y).
exists x0.
exact H.
apply def_lt in H0.
apply or_intror.
exact H0.
Qed.

Lemma menor_distinto: forall x y:nat, x <> y /\ x <= y -> x < y.
Proof.
intros.
destruct H.
apply leq_men_o_igual in H0.
destruct H0.
congruence.
exact H0.
Qed.
Lemma not_eq_S2: forall m n, S m <> S n -> m <> n.
Proof.
unfold not.      (*                             |- ... -> False *)
  intros m n H C.  (* ..., H : S m = S n -> False |- False *)
  apply H.         (* ...                         |- S m = S n *)
  (* f_equal gets rid of functions applied on both sides of an equality,
     this is probably what you didn't find *)
  (* basically, f_equal turns a goal [f a = f b] into [a = b] *)
  f_equal.         (* ..., C : m = n              |- m = n *)
  exact C.
Qed.


Lemma correctitud_eq_nat_f: forall x y, eq_nat x y = false <-> x <> y.
Proof.
induction x.
destruct y.
split.
intro.
simpl in H.
congruence.
intro.
congruence.
split.
intro.
apply O_S.
induction y.
intro.
simpl.
reflexivity.
intro.
simpl.
reflexivity.
induction y.
split.
intro.
apply not_eq_sym.
apply O_S.
intro.
simpl in H.
simpl.
reflexivity.
split.
intro.
simpl in H.
specialize IHx with y.
destruct IHx.
pose (nH := H0 H).
apply not_eq_S in nH.
exact nH.
intro.
apply not_eq_S2 in H.
specialize IHx with y.
destruct IHx.
pose (nH := H1 H).
simpl.
exact nH.
Qed.

Lemma menos_eq_0: forall n m, m <= n ->  m - n = 0.
Proof.
induction n.
destruct m.
simpl.
reflexivity.
intro.
inversion H.
destruct m.
simpl.
assert(0<=n).
apply le_0_n.
intro.
specialize IHn with 0.
pose(IHn H).
rewrite e.
simpl.
reflexivity.
intro.
simpl.
apply le_S_n in H.
destruct n.
simpl.
destruct m.
reflexivity.
inversion H.
case_eq(eq_nat m (S n)).
intro.
apply correctitud_eq_nat in H0.
rewrite H0.
simpl.
assert(S (S n) = n + 2).
rewrite suma_conmutativa.
simpl.
reflexivity.
rewrite H1.
rewrite suma_resta_n.
reflexivity.
intro.
assert(m < S n).
apply menor_distinto.
split.
rewrite correctitud_eq_nat_f in H0.
exact H0.
exact H.
unfold lt in H1.
specialize IHn with (S m).
pose(IHn H1).
rewrite e.
reflexivity.
Qed.

Lemma not_true: forall m:bool, m = false <-> not (m = true).
intro.
split.
intro.
rewrite H.
congruence.
intro.
destruct m.
congruence.
reflexivity.
Qed.

Lemma resta_0: forall m, 0 - m = 0.
Proof.
induction m.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
Qed.

Lemma lt_nat_pred: forall m n, m < pred n -> m < n.
Proof.
intros.
induction m.
destruct n.
simpl in H.
inversion H.
simpl in H.
apply lt_S.
exact H.
induction n.
simpl in H.
inversion H.
simpl in H.
apply lt_S in H.
exact H.
Qed.

Lemma lt_suma_ambos_lados: forall m n p, m < n -> m + p < n + p.
Proof.
intros.
apply def_lt.
apply def_lt in H.
destruct H.
exists x.
rewrite <- H.
rewrite suma_asociativa.
rewrite (suma_conmutativa p _).
rewrite <- suma_asociativa.
reflexivity.
Qed.

Lemma lt_is_le: forall m n, m < n -> m <= n.
Proof.
intros.
apply def_leq.
apply def_lt in H.
destruct H.
exists (S x).
exact H.
Qed.

Lemma lt_n_n: forall m, lt_nat m m = false.
Proof.
induction m.
reflexivity.
simpl.
exact IHm.
Qed.

Lemma menos_gt_0: forall n m, 0 < m - n <-> n < m.
Proof.
split.
intros.
apply (lt_suma_ambos_lados _ _ n) in H.
simpl in H.
rewrite resta_suma_n in H.
exact H.
case_eq(leq_nat n m).
intro.
reflexivity.
intro.
assert(m - n = 0).
apply menos_eq_0.
apply leq_nat_false in H0.
apply correctitud_lt_nat in H0.
apply lt_is_le in H0.
exact H0.
rewrite H1 in H.
simpl in H.
apply correctitud_lt_nat in H.
rewrite lt_n_n in H.
congruence.
intro.
apply def_lt in H.
destruct H.
rewrite <- H.
rewrite suma_resta_n.
apply def_lt.
exists x.
reflexivity.
Qed.

Lemma resta_S: forall m n, n <= m -> S m - n = S (m - n).
Proof.
intros.
induction n.
reflexivity.
assert (n <> m).
unfold not.
intro.
rewrite H0 in H.
apply correctitud_lt_nat in H.
rewrite lt_n_n in H.
congruence.
apply le_S in H.
rewrite leq_S_S in H.
pose(IHn H).
assert(n < m).
apply menor_distinto.
split.
exact H0.
exact H.
simpl.
rewrite S_pred.
rewrite e.
simpl.
reflexivity.
apply correctitud_lt_nat.
apply menos_gt_0.
exact H1.
Qed.

Lemma suma_resta: forall p m n, p <= m -> (m + n) - p = (m - p) + n.
Proof.
induction n.
intros.
rewrite suma_0.
rewrite suma_0.
reflexivity.
intro.
rewrite suma_Sn.
rewrite suma_Sn.
rewrite resta_S.
pose(IHn H).
rewrite e.
reflexivity.
apply def_leq.
apply def_leq in H.
destruct H.
rewrite <- H.
exists (x + n).
rewrite suma_asociativa.
reflexivity.
Qed.

Lemma minus_0: forall m, 0 - m = 0.
Proof.
induction m.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
Qed.

Lemma mult_pred: forall m n, pred m * n = m * n - n.
induction m.
simpl.
intro.
induction n.
simpl. reflexivity.
simpl.
rewrite <- IHn.
simpl. reflexivity.
intro.
simpl.
rewrite sum_res_n.
reflexivity.
Qed.

Definition divide (m:nat) (n:nat) : bool := eq_nat (modulo n m) 0.

Lemma mult_ambos_lados: forall m n p, m = n -> p*m = p*n.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Lemma div_mult: forall m n, 0 < n -> modulo m n = 0 -> n * div m n = m.
intros.
induction m using (well_founded_ind lt_wf).
case_eq (leq_nat n m).
intro.
rewrite div_equation.
apply correctitud_lt_nat in H.
rewrite H.
rewrite H2.
specialize H1 with (m-n).
assert (m-n < m).
apply div_term.
exact H.
exact H2.
pose (nH := H1 H3).
rewrite modulo_equation in H0.
rewrite H in H0.
rewrite H2 in H0.
pose (nnH := nH H0).
rewrite mult_Sn.
rewrite nnH.
rewrite suma_conmutativa.
apply resta_suma_n.
exact H2.
intro.
rewrite div_equation.
apply correctitud_lt_nat in H.
rewrite H.
rewrite H2.
rewrite modulo_equation in H0.
rewrite H in H0.
rewrite H2 in H0.
rewrite H0.
apply mult_0.
Qed.

Lemma div_ambos_lados: forall m n p, 0 < p -> (m = n -> div m p = div n p).
intros.
rewrite H0.
reflexivity.
Qed.

Lemma div_menor: forall m n, 0 < n -> (m < n <-> div m n = 0).
Proof.
split.
intros.
rewrite div_equation.
apply correctitud_lt_nat in H.
rewrite H.
apply correctitud_lt_nat in H0.
apply leq_nat_false in H0.
rewrite H0.
reflexivity.
intro.
rewrite div_equation in H0.
apply correctitud_lt_nat in H.
rewrite H in H0.
case_eq(leq_nat n m).
intro.
rewrite H1 in H0.
inversion H0.
intro.
apply leq_nat_false in H1.
apply correctitud_lt_nat in H1.
exact H1.
Qed.

Lemma lt_n_n_plus: forall n m, lt_nat (n + m) n = false.
Proof.
intros.
induction n.
simpl.
destruct m.
reflexivity.
reflexivity.
destruct m.
simpl.
rewrite suma_0.
apply lt_n_n.
simpl.
exact IHn.
Qed.

Lemma leq_suma: forall m n, leq_nat n (n + m) = true.
Proof.
intros.
induction n.
reflexivity.
simpl.
exact IHn.
Qed.

Lemma div_res: forall q n r, 0 < n -> r < n -> div (q * n + r) n = q.
Proof.
induction q; intros.
simpl.
apply div_menor.
exact H.
exact H0.
rewrite div_equation.
apply correctitud_lt_nat in H.
rewrite H.
case_eq(leq_nat n (S q * n + r)).
intro.
apply suc_iny.
simpl.
rewrite suma_asociativa.
rewrite suma_resta_n.
rewrite correctitud_lt_nat in H.
specialize IHq with n r.
pose(IHq H H0).
exact e.
intro.
apply leq_nat_false in H1.
simpl in H1.
rewrite suma_asociativa in H1.
rewrite lt_n_n_plus in H1.
congruence.
Qed.

Lemma modulo_res: forall q n r, 0 < n -> r < n -> modulo (q * n + r) n = r.
Proof.
intros.
induction q.
simpl.
apply correctitud_lt_nat in H.
apply correctitud_lt_nat in H0.
rewrite modulo_equation.
rewrite H.
apply leq_nat_false in H0.
rewrite H0.
reflexivity.
simpl.
apply correctitud_lt_nat in H.
apply correctitud_lt_nat in H0.
rewrite modulo_equation.
rewrite H.
assert(leq_nat n (n + q * n + r) = true).
rewrite suma_asociativa.
apply leq_suma.
rewrite H1.
rewrite suma_asociativa.
rewrite suma_resta_n.
exact IHq.
Qed.

Lemma correctitud_divmod: 
forall m n:nat, 0 < n -> forall q r, div m n = q /\ modulo m n = r 
<-> m = q * n + r /\ r < n.
Proof.
induction m using (well_founded_ind  (lt_wf)).
split.
intros.
case_eq (leq_nat n m).
intro.
destruct H1.
rewrite div_equation in H1.
apply correctitud_lt_nat in H0.
rewrite H0 in H1.
rewrite H2 in H1.
assert(menos m n < m).
apply div_term.
exact H0.
exact H2.
destruct H with (menos m n) n (pred q) r.
exact  H4.
apply correctitud_lt_nat.
exact H0.
assert(div (m - n) n = pred q /\ modulo (m - n) n = r).
split.
apply pred_ambos_lados in H1.
simpl in H1.
exact H1.
rewrite modulo_equation in H3.
rewrite H0 in H3.
rewrite H2 in H3.
exact H3.
pose(nH := H5 H7).
destruct nH.
apply suma_ambos_lados with _ _ n in H8.
rewrite resta_suma_n in H8.
rewrite suma_asociativa in H8.
rewrite (suma_conmutativa r n) in H8.
rewrite <- suma_asociativa in H8.
assert (forall x n, mult x n + n = mult (S x) n).
intros.
simpl.
rewrite suma_conmutativa.
reflexivity.
rewrite H10 in H8.
rewrite S_pred in H8.
split.
exact H8.
exact H9.
rewrite def_lt_nat.
simpl.
exists (div (menos m n) n).
exact H1.
exact H2.
intro.
split.
destruct H1.
rewrite div_equation in H1.
rewrite H2 in H1.
apply correctitud_lt_nat in H0.
rewrite H0 in H1.
rewrite modulo_equation in H3.
rewrite H0 in H3.
rewrite H2 in H3.
rewrite <- H1.
simpl.
remember H3.
exact H3.
destruct H1.
rewrite modulo_equation in H3.
apply correctitud_lt_nat in H0.
rewrite H0 in H3.
rewrite H2 in H3.
rewrite <- H3.
apply correctitud_leq_nat_false in H2.
exact H2.
intros.
split.
destruct H1.
apply div_ambos_lados with _ _ n in H1.
rewrite div_res in H1.
exact H1.
exact H0.
exact H2.
exact H0.
destruct H1.
rewrite modulo_equation.
apply correctitud_lt_nat in H0.
apply correctitud_lt_nat in H2.
rewrite H0.
case_eq(leq_nat n m).
intro.
rewrite H1.
rewrite suma_resta.
rewrite <- mult_pred.
apply modulo_res.
apply correctitud_lt_nat.
exact H0.
apply correctitud_lt_nat.
exact H2.
destruct q.
simpl in H1.
rewrite H1 in H3.
apply leq_nat_false in H2.
congruence.
simpl.
apply correctitud_leq_nat.
apply leq_suma.
intro.
rewrite H1 in H3.
apply leq_nat_false in H3.
destruct q.
simpl in H1.
exact H1.
simpl in H3.
rewrite suma_asociativa in H3.
rewrite lt_n_n_plus in H3.
congruence.
Qed.

Lemma m_leq_0: forall m:nat, true = leq_nat m 0 -> m = 0.
Proof.
induction m.
intro. reflexivity.
simpl.
intro.
congruence.
Qed.

Lemma leq_Sn_n: forall n, leq_nat (S n) n = false.
Proof.
induction n.
simpl. reflexivity.
simpl. simpl in IHn. exact IHn.
Qed.


Lemma leq_n_n: forall n, leq_nat n n = true.
Proof.
induction n.
simpl. reflexivity.
simpl.
exact IHn.
Qed.

Lemma intervalo_term: forall m n, leq_nat  m n = true -> S n - S m < S n - m.
Proof.
intros.
apply def_leq_nat in H.
destruct H.
remember H.
clear Heqe.
rewrite <- suc_iny in H.
rewrite <- suma_Sn in H.
apply resta_ambos_lados with _ _ m in H.
rewrite sum_res_n in H.
rewrite <- H.
rewrite <- suc_iny in e.
assert (S (m + x) = S m + x).
simpl.
reflexivity.
rewrite H0 in e.
apply resta_ambos_lados with _ _ (S m) in e.
rewrite sum_res_n in e.
rewrite <- e.
apply def_lt.
exists 0.
rewrite suma_Sn.
rewrite suma_0.
reflexivity.
Qed.

(* Funciones de lista *)

Function member (n:nat) (l : list nat) : bool := match l with
  | nil => false
  | x::xs => match eq_nat x n with
    | true => true
    | false => member n xs
    end
 end.

Definition ancho (par : nat * nat) : nat := match par with
  | (m,n) => S n - m
  end.

Function intervalo (par : nat*nat) {measure ancho par} : list nat :=
match par with
 (m,n) => match leq_nat m n with
    | false => nil
    | true => m :: (intervalo (S m, n))
  end
end.
intros.
unfold ancho.
apply intervalo_term.
exact teq0.
Qed.

(* Intervalo *)
Lemma def_intervalo: forall p:nat, forall par:nat*nat, ancho par = p -> forall k:nat, member k (intervalo par) = true <-> (forall m n, par = (m,n) -> m <= k /\ k<= n).
Proof.
induction p using (well_founded_ind lt_wf).
destruct par.
intro.
case_eq(leq_nat n n0).
intro.
rewrite intervalo_equation.
rewrite H1.
split. (*split.*)
case_eq(eq_nat n k).
intro.
remember H1.
remember H2.
simpl.
rewrite H2.
intro.
clear H3.
intros.
inversion H3.
clear Heqe0.
rewrite correctitud_eq_nat in e0.
rewrite e0 in H5.
rewrite H5.
split.
apply le_n.
clear Heqe.
rewrite e0 in e.
apply correctitud_leq_nat in e.
rewrite H6 in e.
rewrite H5 in e.
exact e.
intro.
simpl.
rewrite H2.
intro.
assert(S n0 - S n < S n0 - n).
apply intervalo_term.
exact H1.
unfold ancho in H0.
rewrite H0 in H4.
specialize H with (S n0 - S n) p k.
pose (nH := H H4).
specialize nH with (S n, n0) k.
unfold ancho in nH.
assert ( S n0 - S n = S n0 - S n).
reflexivity.
pose (nnH := nH H5).
specialize nnH with k.
destruct nnH.
pose (nnnH := H6 H3).
intros.
specialize nnnH with (S m) n1.
inversion H8.
assert ( (S n, n0) = (S m, n1)).
rewrite H10.
rewrite H11.
reflexivity.
pose (neH := nnnH H9).
split.
destruct neH.
apply def_leq in H12.
destruct H12.
apply def_leq.
simpl in H12.
rewrite <- suma_Sn in H12.
exists (S x).
exact H12.
destruct neH.
exact H13.
intros.
case_eq (eq_nat n k).
intro.
simpl.
rewrite -> H3.
reflexivity.
intro.
remember H3.
simpl.
rewrite H3.
specialize H with (ancho (S n, n0)) p k.
unfold ancho in H.
unfold ancho in H0.
rewrite <- H0 in H.
assert(S n0 - S n < S n0 - n).
apply intervalo_term.
exact H1.
pose (nH := H  H4).
specialize nH with (S n, n0) k.
simpl in nH.
assert(pred (S n0 - n) = pred (S n0 - n)).
reflexivity.
pose (nnH := nH H5).
specialize nnH with k.
destruct nnH.
apply H7.
intros.
inversion H8.
rewrite H10.
rewrite <- H11.
specialize H2 with n n0.
assert ((n, n0) = (n, n0)).
reflexivity.
pose (neH := H2 H9).
destruct neH.
clear H9.
clear Heqe.
apply correctitud_eq_nat_f in H3.
assert (n <> k /\ n <= k).
split.
exact H3.
exact H12.
apply menor_distinto in H9.
rewrite <- H10.
split.
unfold lt in H9.
exact H9.
exact H13.
intros.
split.
intro.
rewrite intervalo_equation in H2.
rewrite H1 in H2.
simpl in H2.
congruence.
intro.
specialize H2 with n n0.
assert ((n, n0) = (n, n0)).
reflexivity.
pose (nH := H2 H3).
apply leq_nat_false in H1.
apply correctitud_lt_nat in H1.
destruct nH.
assert (n <= n0).
apply le_trans with k.
exact H4.
exact H5.
assert (n < n).
apply le_lt_trans with n0.
exact H6.
exact H1.
unfold lt in H7.
apply correctitud_leq_nat in H7.
rewrite leq_Sn_n in H7.
congruence.
Qed.

(* Divide *)

Lemma divide_1_n: forall n, divide 1 n = true.
Proof.
intros.
unfold divide.
induction n using (well_founded_ind lt_wf).
rewrite modulo_equation.
assert(lt_nat 0 1 = true).
simpl.
reflexivity.
rewrite H0.
case_eq (leq_nat 1 n).
intro.
assert (0 < n -> n-1 < n).
intro.
apply def_lt in H2.
simpl in H2.
destruct H2.
rewrite <- H2.
simpl.
apply def_lt.
exists 0.
rewrite suma_Sn.
rewrite suma_0.
reflexivity.
assert ( 0 < n).
apply def_lt.
apply def_leq_nat in H1.
destruct H1.
simpl in H1.
rewrite <- H1.
exists x.
simpl.
reflexivity.
pose (nH := H2 H3).
specialize H with (n-1).
pose (nnH := H nH).
exact nnH.
intro.
apply leq_nat_false in H1.
apply def_lt_nat in H1.
destruct H1.
rewrite suma_Sn in H1.
rewrite suc_iny in H1.
assert(n=0).
destruct n.
reflexivity.
simpl in H1.
congruence.
rewrite H2.
simpl. reflexivity.
Qed.

Lemma divide_n_n: forall n, lt_nat 0 n = true -> divide n n = true.
Proof.
intros.
unfold divide.
rewrite modulo_equation.
rewrite H.
assert(leq_nat n n = true).
apply leq_n_n.
rewrite H0.
assert(n-n = 0).
induction n.
simpl.
reflexivity.
simpl.
rewrite pred_resta.
simpl.
apply n_menos_n.
rewrite n_menos_n.
rewrite modulo_equation.
rewrite H.
destruct n.
simpl in H.
congruence.
simpl.
reflexivity.
Qed.

Lemma divide_entre: forall m n, 0 < m /\ 0 < n -> divide m n = true -> 1 <= m <= n.
intros.
unfold divide in H.
case_eq( leq_nat m n).
intro.
split.
unfold lt in H.
destruct H.
exact H.
apply correctitud_leq_nat.
exact H1.
intro.
split.
unfold lt in H.
destruct H.
exact H.
unfold divide in H0.
rewrite modulo_equation in H0.
destruct H.
apply correctitud_lt_nat in H.
rewrite H in H0.
rewrite H1 in H0.
apply correctitud_eq_nat in H0.
rewrite H0 in H1.
destruct m.
simpl in H.
congruence.
simpl in H1.
rewrite H0 in H2.
inversion H2.
Qed.

Definition multiplo (m:nat) (n:nat) : bool := eq_nat (modulo m n) 0.

Lemma multiplo_divide: forall m n, divide m n = multiplo n m.
Proof.
intros.
unfold divide.
unfold multiplo.
split.
Qed.

Lemma mult_S_lt: forall n k, 0 < n -> 0 < k -> lt_nat n (S k * n) = true.
Proof.
intros.
apply def_lt in H.
simpl in H.
destruct H.
rewrite <- H.
rewrite def_lt_nat.
apply def_lt in H0.
destruct H0.
simpl in H0.
exists (pred (k *  S x)).
simpl.
rewrite S_pred.
reflexivity.
rewrite <- H0.
simpl.
reflexivity.
Qed.

Lemma mult_S_leq: forall n k, leq_nat n (S k * n) = true.
Proof.
intros.
rewrite def_leq_nat.
exists (k*n).
simpl.
reflexivity.
Qed.

Lemma resto_multiplo: forall k m n, 0 < n -> k = m * n -> modulo k n = 0.
Proof.
induction k using (well_founded_ind lt_wf).
intros.
case_eq(leq_nat n k).
intro.
rewrite modulo_equation.
apply correctitud_lt_nat in H0.
rewrite H0.
rewrite H2.
assert(k - n < k).
apply div_term.
exact H0.
exact H2.
specialize H with (k - n) m n.
pose (nH := H H3).
specialize nH with (pred m) n.
apply correctitud_lt_nat in H0.
pose (nnH := nH H0).
assert (k - n = pred m * n).
rewrite H1.
induction m.
rewrite mult_pred.
reflexivity.
rewrite mult_pred.
reflexivity.
pose (nnnH := nnH H4).
exact nnnH.
intro.
rewrite modulo_equation.
apply correctitud_lt_nat in H0.
rewrite H0.
rewrite H2.
destruct m.
simpl in H1.
exact H1.
rewrite H1 in H2.
rewrite mult_S_leq in H2.
congruence.
Qed.


Lemma def_multiplo: forall m n, lt_nat 0 n = true -> (multiplo m n = true <-> exists k, n * k = m).
Proof.
intros.
split.
intro.
exists (div m n).
apply div_mult.
rewrite correctitud_lt_nat in H.
exact H.
unfold multiplo in H0.
rewrite correctitud_eq_nat in H0.
exact H0.
intro.
destruct H0.
rewrite <- H0.
unfold multiplo.
assert (modulo (n * x) n = 0).
rewrite H0.
rewrite mult_conmutativa in H0.
rewrite (resto_multiplo m x n).
reflexivity.
apply correctitud_lt_nat. exact H.
rewrite H0.
reflexivity.
rewrite H1.
simpl.
reflexivity.
Qed.

Lemma def_divide: forall m n, lt_nat 0 n = true -> (divide n m = true <-> exists k, n * k = m).
intros.
rewrite multiplo_divide.
apply def_multiplo.
exact H.
Qed.

Lemma multiplo_1: forall n, multiplo n 1 = true.
Proof.
intro.
apply def_multiplo.
simpl.
reflexivity.
simpl.
exists n.
rewrite suma_0.
reflexivity.
Qed.
 
Lemma multiplo_n_n: forall n, lt_nat 0 n = true -> multiplo n n = true.
Proof.
intros.
apply def_multiplo.
exact H.
exists (S 0).
rewrite mult_conmutativa.
simpl.
rewrite suma_0.
reflexivity.
Qed.
 
Definition divisores (m:nat) : list nat := filter (multiplo m) (intervalo (0,m)).

Lemma correctitud_filter: forall  xs:list nat, forall n:nat, forall p: (nat -> bool),
member n (filter p xs) = true <-> p n = true /\ member n xs = true.
Proof.
induction xs.
intros; simpl.
split; intros.
congruence.
destruct H.
congruence.
intros.
case_eq(p a).
intro.
simpl.
rewrite H.
simpl.
case_eq(eq_nat a n).
intro.
split.
intro.
split.
apply correctitud_eq_nat in H0.
rewrite H0 in H.
exact H.
reflexivity.
intro.
reflexivity.
intro.
specialize IHxs with n p.
exact IHxs.
intro.
case_eq(eq_nat a n).
intro.
simpl.
rewrite H.
rewrite H0.
split.
intro.
specialize IHxs with n p.
destruct IHxs.
pose (nH := H2 H1).
split.
destruct nH.
exact H4.
reflexivity.
intro.
destruct H1.
apply correctitud_eq_nat in H0.
rewrite H0 in H.
congruence.
intro.
split.
intro.
simpl in H1.
rewrite H in H1.
specialize IHxs with n p.
destruct IHxs.
pose ( nH :=  H2 H1).
simpl.
rewrite H0.
exact nH.
intro.
simpl.
rewrite H.
simpl in H1.
rewrite H0 in H1.
specialize IHxs with n p.
destruct IHxs.
pose (nH := H3 H1).
exact nH.
Qed.

Lemma m_not_0_then_lt: forall m, m <> 0 -> 0 < m.
Proof.
intros.
unfold not in H.
destruct m.
congruence.
apply lt_0_Sn.
Qed.

Lemma correctitud_divisores: forall m n, 
0 < n  -> (divide m n = true <-> member m (divisores n) = true).
Proof.
intros.
split.
intro.
unfold divisores.
rewrite correctitud_filter.
rewrite <- multiplo_divide.
split.
exact H0.
rewrite (def_intervalo (S n) (0, n)).
intros.
inversion H1.
rewrite <- H4.
Check divide_entre.
case_eq(eq_nat m 0).
intro.
apply correctitud_eq_nat in H2.
rewrite H2.
split.
apply le_n.
apply def_leq.
apply def_lt in H.
destruct H.
simpl in H.
simpl.
exists (S x).
exact H.
intro.
apply not_true in H2.
rewrite correctitud_eq_nat in H2.
apply m_not_0_then_lt in H2.
split.
apply lt_is_le in H2.
exact H2.
apply divide_entre.
split.
exact H2.
exact H.
exact H0.
unfold ancho.
reflexivity.
unfold divisores.
rewrite correctitud_filter.
intros.
destruct H0.
rewrite <- multiplo_divide in H0.
exact H0.
Qed.

Fixpoint eq_lists (l1: list nat) (l2: list nat) : bool :=
match l1 with
| nil => match l2 with
  | nil => true
  | _ :: _ => false
  end
| x :: xs => match l2 with
  | nil => false
  | y :: ys => andb (eq_nat x y) (eq_lists xs ys) 
  end
end.

Lemma correctitud_andb: forall b1 b2, andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
intros.
split.
intro.
split.
case_eq(b1).
intro. reflexivity.
intro.
rewrite H0 in H. simpl in H.
congruence.
case_eq(b1).
intro.
rewrite H0 in H.
simpl in H.
exact H.
intro.
rewrite H0 in H.
simpl in H.
congruence.
intro.
destruct H.
rewrite H.
rewrite H0.
simpl. reflexivity.
Qed.

Lemma eq_nat_n_n: forall n, eq_nat n n = true.
Proof.
intro.
rewrite correctitud_eq_nat.
reflexivity.
Qed.

Lemma eq_lists_ys_ys: forall ys, eq_lists ys ys = true.
Proof.
induction ys.
simpl. reflexivity.
simpl.
rewrite correctitud_andb.
split.
apply eq_nat_n_n.
exact IHys.
Qed.


Lemma iff_contra M N: (M <-> N) -> ((not M) <-> (not N)).
intro.
split.
intro.
intro.
destruct H.
pose (nH := H2 H1).
contradiction.
intro.
intro.
destruct H.
pose (nH := H H1).
contradiction.
Qed.

Lemma correctitud_eq_lists: forall xs ys, eq_lists xs ys = true <-> xs = ys.
Proof.
induction xs.
intros.
split.
intro.
destruct ys.
reflexivity.
simpl in H.
congruence.
intro.
rewrite <- H.
simpl. reflexivity.
induction ys.
split.
intro.
simpl in H.
congruence.
intro.
simpl in H. congruence.
split.
intro.
simpl in H.
apply correctitud_andb in H.
destruct H.
apply correctitud_eq_nat in H.
rewrite H.
specialize IHxs with ys.
destruct IHxs.
pose (nH :=  H1 H0).
rewrite nH.
reflexivity.
intro.
rewrite H.
simpl.
apply correctitud_andb.
split.
induction a0.
simpl. reflexivity.
simpl.
apply eq_nat_n_n.
apply eq_lists_ys_ys.
Qed.

Definition primo (n:nat) : bool := andb (eq_lists (filter (multiplo n) (intervalo (2, n - 1))) nil) (lt_nat 1 n).

Lemma filter_nil: forall xs p, (forall n, member n xs = true -> p n = false) <-> filter p xs = nil.
Proof.
induction xs.
intros.
split.
intro.
simpl.
reflexivity.
intros.
simpl in H0.
congruence.
intros.
split.
intros.
case_eq (p a).
intro.
specialize H with a.
simpl in H.
rewrite eq_nat_n_n in H.
assert(true = true).
reflexivity.
pose( nH := H H1).
congruence.
intro.
simpl.
rewrite H0.
rewrite <- IHxs.
intros.
case_eq(eq_nat a n).
intro.
rewrite correctitud_eq_nat in H2.
rewrite <- H2.
exact H0.
intro.
specialize H with n.
simpl in H.
rewrite H2 in H.
pose( nH := H H1).
exact nH.
case_eq(p a).
intros.
simpl in H0.
rewrite H in H0.
congruence.
intros.
case_eq(eq_nat a n).
intro.
apply correctitud_eq_nat in H2.
rewrite <- H2.
exact H.
intro.
simpl in H0.
rewrite H in H0.
rewrite <- IHxs in H0.
simpl in H1.
rewrite H2 in H1.
specialize H0 with n.
pose (nH := H0 H1).
exact nH.
Qed.

Lemma correctitud_primo: forall n, 1 < n ->
(primo n = true <-> (forall k, 1 < k < n -> divide k n = false)).
Proof.
intros.
split.
intros.
unfold primo in H0.
apply correctitud_andb in H0.
destruct H0.
apply correctitud_eq_lists in H0.
apply not_true.
unfold not.
intro.
rewrite multiplo_divide in H3.
assert (member k (intervalo (2, n-1)) = true).
rewrite (def_intervalo (n - 2)).
intros.
inversion H4.
unfold lt in H1.
split.
destruct H1.
exact H1.
destruct H1.
apply le_S_n. (* Aplica sucesor de ambos lados de un <= *)
rewrite S_pred.
exact H5.
apply correctitud_lt_nat in H.
apply def_lt_nat.
apply def_lt_nat in H.
simpl in H.
destruct H.
simpl.
exists (S x).
exact H.
unfold ancho.
simpl.
reflexivity.
assert(multiplo n k = true /\ member k (intervalo (2, n - 1)) = true).
split.
exact H3.
exact H4.
apply correctitud_filter in H5.
rewrite H0 in H5.
simpl in H5.
congruence.
intro.
unfold primo.
apply correctitud_andb.
split.
apply correctitud_eq_lists. 
assert (forall k, member k (intervalo (2, n-1)) = true <-> 1 < k < n).
intro.
rewrite (def_intervalo (n - 2)).
split.
intros.
specialize H1 with 2 (n-1).
assert( (2, n-1) = (2, n-1)).
reflexivity.
pose (nH := H1 H2).
unfold lt.
split.
destruct nH.
exact H3.
destruct nH.
simpl in H4.
assert (S k <= S (pred n)).
apply le_n_S.
exact H4.
rewrite S_pred in H5.
exact H5.
apply correctitud_lt_nat in H.
apply def_lt_nat.
apply def_lt_nat in H.
destruct H.
simpl in H.
simpl.
exists (S x).
exact H.
intros.
inversion H2.
unfold lt in H1.
destruct H1.
split.
exact H1.
apply le_S_n.
rewrite S_pred.
exact H3.
apply correctitud_lt_nat in H.
apply def_lt_nat.
apply def_lt_nat in H.
destruct H.
simpl in H.
simpl.
exists (S x).
exact H.
unfold ancho.
simpl.
reflexivity.
apply filter_nil.
intro.
specialize H0 with n0.
specialize H1 with n0.
rewrite multiplo_divide in H0.
intro.
destruct H1.
pose (nH := H1 H2).
pose(nnH := H0 nH).
exact nnH.
apply correctitud_lt_nat.
exact H.
Qed.

(* Usa logica clasica *)
Lemma no_primo_entonces_ex_k_divide:
forall n, 1 < n -> (primo n = false <-> exists k, 1 < k < n /\ divide k n = true).
intros.
split.
intro.
rewrite not_true in H0.
rewrite correctitud_primo in H0.
apply not_all_ex_not in H0.
destruct H0.
apply imply_to_and in H0.
rewrite not_true in H0.
destruct H0.
apply NNPP in H1. (* Doble negacion *)
exists x.
split.
exact H0.
exact H1.
exact H.
intro.
apply not_true.
rewrite correctitud_primo.
unfold not.
intro.
destruct H0.
specialize H1 with x.
destruct H0.
pose(nH := H1 H0).
congruence.
exact H.
Qed.


Definition factores (m:nat) : list nat := filter primo (divisores m).

Lemma correctitud_factores: forall m n, 0 < n -> (member m (factores n) = true <-> primo m = true /\ divide m n = true).
Proof.
split.
intros.
unfold factores in H0.
apply correctitud_filter in H0.
split.
destruct H0.
exact H0.
destruct H0.
apply correctitud_divisores in H1.
exact H1.
exact H.
intro.
destruct H0.
unfold factores.
apply correctitud_filter.
rewrite <- correctitud_divisores.
split.
exact H0.
exact H1.
exact H.
Qed.

Lemma lt_sum_derecha: forall m n p, m < n -> m < n + p.
Proof.
intros.
apply def_lt.
apply def_lt in H.
destruct H.
exists (x+p).
assert(m + S (x + p) = m + (S x + p)).
simpl.
reflexivity.
rewrite H0.
rewrite <- suma_asociativa with m (S x) p.
rewrite H.
reflexivity.
Qed.

Lemma lt_pred_is_lt: forall m n, m < pred n -> m < n.
Proof.
intros.
destruct n.
simpl in H.
congruence.
simpl in H.
apply lt_S.
exact H.
Qed.

Lemma lt_nat_false: forall m n, lt_nat m n = false <-> leq_nat n m = true.
Proof.
induction m.
split.
intro.
destruct n.
simpl. reflexivity.
simpl in H. congruence.
intro.
destruct n.
simpl. reflexivity.
simpl in H. congruence.
induction n.
split.
intro.
simpl. reflexivity.
intro.
simpl. reflexivity.
split.
intro. simpl in H. simpl.
specialize IHm with n.
destruct IHm.
pose(nH := H0 H).
exact nH.
intro. simpl. simpl in H.
specialize IHm with n.
destruct IHm.
pose(nH := H1 H).
exact nH.
Qed. 

Lemma descomponer_term: forall m x, 1 < m /\ 1 < x -> div m x < m.
Proof.
induction m using (well_founded_ind lt_wf).
intros.
case_eq(leq_nat x m).
intro.
rewrite div_equation.
destruct H0.
assert(lt_nat 0 x = true).
apply def_lt in H2.
apply def_lt_nat.
simpl.
destruct H2.
simpl in H2.
exists (S x0).
exact H2.
rewrite H3.
rewrite H1.
specialize H with (m - x) x.
assert(m-x < m).
apply div_term.
exact H3.
exact H1.
pose (nH := H H4).
specialize nH with x.
case_eq(lt_nat 1 (m-x)).
intro.
apply correctitud_lt_nat in H5.
assert(1 < m - x /\ 1 < x).
split.
exact H5.
exact H2.
pose( nnH := nH H6).
rewrite def_lt in H2.
simpl in H2.
destruct H2.
assert(div (m - x) x < pred (m - S x0)).
rewrite <- H2 in nnH.
simpl in nnH.
rewrite <- H2.
simpl.
exact nnH.
assert(S(div (m - x) x) < S (pred (m - S x0))).
apply lt_n_S.
exact H7.
rewrite S_pred in H8.
apply (lt_sum_derecha _ _ (S x0)) in H8.
rewrite resta_suma_n in H8.
exact H8.
apply def_leq_nat.
rewrite <- H2 in H1.
apply def_leq_nat in H1.
SearchAbout suma.
destruct H1.
rewrite suma_n_S in H1.
exists (S x1).
exact H1.
rewrite <- H2 in H5.
rewrite correctitud_lt_nat.
apply lt_pred_is_lt.
simpl.
simpl in H5.
apply def_lt.
apply def_lt in H5.
simpl in H5.
destruct H5.
simpl.
exists (S x1).
exact H5.
intro.
rewrite div_equation.
rewrite H3.
assert(leq_nat x (m-x) = false).
apply leq_nat_false.
apply lt_nat_false in H5.
apply correctitud_leq_nat in H5.
apply (le_lt_trans (m-x) 1 x) in H5.
apply correctitud_lt_nat.
exact H5.
exact H2.
rewrite H6.
exact H0.
intro.
destruct H0.
rewrite div_equation.
assert(lt_nat 0 x = true).
apply def_lt_nat.
apply def_lt in H2.
destruct H2.
simpl.
rewrite suma_Sn in H2.
simpl in H2.
exists (S x0).
exact H2.
rewrite H3.
rewrite H1.
apply def_lt.
apply def_lt in H0.
destruct H0.
simpl.
rewrite suma_Sn in H0.
simpl in H0.
exists (S x0).
exact H0.
Qed.

Lemma O_1_no_primo: forall m, m < 1 -> primo m = false.
Proof.
intros.
apply correctitud_lt_nat in H.
unfold primo.
rewrite not_true.
unfold not.
intro.
apply correctitud_andb in H0.
destruct H0.
apply correctitud_lt_nat in H.
apply correctitud_lt_nat in H1.
inversion H.
rewrite H3 in H1.
inversion H1.
inversion H3.
Qed.

Lemma list_not_nil: forall xs, xs <> nil -> (exists y:nat, exists ys, xs = y :: ys).
Proof.
intros.
destruct xs.
congruence.
exists n.
exists xs.
reflexivity.
Qed.

Lemma lt_1_implies_0: forall m, 1 < m -> 0 < m.
Proof.
intros.
apply def_lt.
apply def_lt in H.
destruct H.
simpl in H.
exists (S x).
exact H.
Qed.

Lemma divide_trans: forall m n p, 0 < m /\ 0 < p -> 
divide m n = true /\ divide p m = true -> divide p n = true.
Proof.
intros.
destruct H.
destruct H0.
apply def_divide in H0.
apply def_divide in H2.
apply def_divide.
apply correctitud_lt_nat.
exact H1.
destruct H0.
destruct H2.
rewrite <- H2 in H0.
rewrite mult_asociativa in H0.
exists (x0 * x).
exact H0.
apply correctitud_lt_nat.
exact H1.
apply correctitud_lt_nat.
exact H.
Qed.

Lemma divide_m_n_implies_m_gt_0: forall m n, divide m n = true -> 0 < m.
Proof.
intros.
assert(m <> 0).
unfold not.
intro.
rewrite H0 in H.
unfold divide in H.
rewrite modulo_equation in H.
simpl in H.
congruence.
apply m_not_0_then_lt in H0.
exact H0.
Qed.

Lemma tiene_divisor_primo: forall m:nat,
1 < m -> exists x, divide x m = true /\  primo x = true.
Proof.
intros.
induction m using (well_founded_ind lt_wf).
case_eq(primo m).
intro.
exists m.
split.
apply divide_n_n.
apply lt_1_implies_0 in H.
apply correctitud_lt_nat.
exact H.
exact H1.
intro.
apply no_primo_entonces_ex_k_divide in H1.
destruct H1.
specialize H0 with x.
destruct H1.
destruct H1.
pose( nH := H0 H3).
pose (nnH := nH H1).
destruct nnH.
destruct H4.
assert(divide x m = true /\ divide x0 x = true).
split.
exact H2.
exact H4.
apply divide_trans in H6.
exists x0.
split.
exact H6.
exact H5.
split.
apply lt_1_implies_0 in H1.
exact H1.
apply divide_m_n_implies_m_gt_0 in H4.
exact H4.
exact H.
Qed.

Lemma primo_implies_gt_1: forall m, primo m = true -> 1 < m.
Proof.
intros.
unfold primo in H.
apply correctitud_andb in H.
destruct H.
apply correctitud_lt_nat in H0.
exact H0.
Qed.

Lemma descomponer_term2: forall m, 1 < m -> exists x xs, factores m = x :: xs /\ 1 < x.
intros.
unfold factores.
assert( filter primo (divisores m) <> nil).
unfold not.
intro.
rewrite <- filter_nil in H0.
case_eq(primo m).
intro.
specialize H0 with m.
assert(member m (divisores m) = true).
unfold divisores.
apply correctitud_filter.
split.
apply multiplo_n_n.
apply lt_1_implies_0 in H.
apply correctitud_lt_nat.
exact H.
rewrite (def_intervalo (S m)).
intros.
inversion H2.
split.
apply le_0_n.
apply le_n.
unfold ancho.
simpl.
reflexivity.
pose(nH := H0 H2).
congruence.
intro.
apply no_primo_entonces_ex_k_divide in H1.
destruct H1.
rewrite correctitud_divisores in H1.
apply tiene_divisor_primo in H.
destruct H.
destruct H.
specialize H0 with x0.
rewrite <- correctitud_divisores in H0.
pose ( nH := H0 H).
congruence.
destruct H1.
destruct H1.
apply (lt_trans 0 x m).
apply lt_1_implies_0 in H1.
exact H1.
exact H4.
apply lt_1_implies_0 in H.
exact H.
exact H.
apply list_not_nil in H0.
destruct H0.
destruct H0.
exists x.
exists x0.
split.
exact H0.
assert(member x (filter primo (divisores m)) = true).
rewrite H0.
simpl.
rewrite eq_nat_n_n.
reflexivity.
apply correctitud_filter in H1.
destruct H1.
apply primo_implies_gt_1 in H1.
exact H1.
Qed.

Function descomponer (m:nat) {measure (fun n=> n) m} : list nat :=
match lt_nat 1 m with
  | false => nil
  | true => match factores m with
    | nil => nil
    | x::_ => x :: (descomponer (div m x))
  end
end.
Proof.
intros.
apply correctitud_lt_nat in teq.
assert(member x (factores m) = true).
rewrite teq0.
simpl.
rewrite eq_nat_n_n.
reflexivity.
apply correctitud_factores in H.
destruct H.
unfold primo in H.
apply correctitud_andb in H.
destruct H.
apply correctitud_lt_nat in H1.
apply descomponer_term.
split.
exact teq.
exact H1.
apply def_lt.
apply def_lt in teq.
destruct teq.
simpl in H0.
simpl.
exists (S x0).
exact H0.
Qed.

Fixpoint prodl (l : list nat) : nat :=
match l with
| nil => 1
| x :: xs => x * (prodl xs)
end.

Lemma mult_le: forall m n, 0 < n -> m <= m * n.
Proof.
intros.
induction m.
simpl.
apply le_n.
rewrite def_leq in IHm.
destruct IHm.
rewrite def_leq.
simpl.
rewrite <- H0.
exists (pred n +  x).
rewrite <- suma_Sn.
assert(m + S (pred n + x) = m + (S (pred n) + x)).
simpl.
reflexivity.
rewrite H1.
rewrite S_pred.
rewrite <- (suma_asociativa m n x).
rewrite (suma_conmutativa m n).
rewrite (suma_asociativa n m x).
reflexivity.
apply correctitud_lt_nat.
exact H.
Qed.

Lemma pred_n_is_n_minus_1: forall n, pred n = n - 1.
Proof.
intros.
destruct n.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma mult_identidad: forall n x, 0 < n -> (n * x = n <-> x = 1).
Proof.
intros.
split.
intro.
case_eq(eq_nat x 1).
intro.
apply correctitud_eq_nat in H1.
exact H1.
intro.
apply correctitud_eq_nat_f in H1.
case_eq(eq_nat x 0).
intro.
apply correctitud_eq_nat in H2.
rewrite H2 in H0.
rewrite mult_0 in H0.
rewrite <- H0 in H.
inversion H.
intro.
apply correctitud_eq_nat_f in H2.
assert(lt_nat 1 x = true).
destruct x.
congruence.
destruct x.
congruence.
simpl.
reflexivity.
apply def_lt_nat in H3.
destruct H3.
simpl in H3.
rewrite <- H3 in H0.
apply def_lt in H.
simpl in H.
destruct H.
rewrite mult_Sn in H0.
rewrite mult_Sn in H0.
apply (resta_ambos_lados _ _ n) in H0.
rewrite n_menos_n in H0.
rewrite sum_res_n in H0.
rewrite <- H in H0.
simpl in H0.
inversion H0.
intro.
rewrite H0.
rewrite mult_conmutativa.
simpl.
rewrite suma_0.
reflexivity.
Qed.

Lemma neq_sym: forall m n:nat, m <> n <-> n <> m.
Proof.
split.
congruence.
congruence.
Qed.

Lemma div_gt_1: forall m n, 0 < n -> 1 <= div m n -> 0 < m.
intros.
rewrite div_equation in H0.
apply correctitud_lt_nat in H.
rewrite H in H0.
case_eq(leq_nat n m).
intro.
apply def_lt.
apply def_leq_nat in H1.
apply def_lt_nat in H.
destruct H.
destruct H1.
simpl.
simpl in H.
rewrite <- H in H1.
simpl in H1.
rewrite <- H1.
exists (x + x0).
reflexivity.
intro.
rewrite H1 in H0.
inversion H0.
Qed.

Lemma leq_1: forall m, m <= 1 -> m = 0 \/ m = 1.
Proof.
intros.
destruct m.
apply or_introl.
reflexivity.
rewrite leq_S_S in H.
destruct m.
apply or_intror.
reflexivity.
inversion H.
Qed.

(* Resta *)

Lemma resta_lt: forall m n, n < m -> 0 < m - n.
Proof.
intros.
induction n.
simpl.
exact H.
simpl.
apply def_lt.
simpl.
apply def_lt in H.
simpl in H.
destruct H.
exists x.
apply resta_ambos_lados with _ _ n in H.
apply pred_ambos_lados in H.
rewrite pred_resta in H.
simpl in H.
rewrite suma_resta_n in H.
exact H.
Qed.

Lemma S_resta: forall m n, n <= m -> S( S m - n) = S ( S ( m - n)).
Proof.
intros.
induction n.
reflexivity.
apply suc_iny.
simpl.
rewrite pred_resta.
simpl.
rewrite S_pred.
reflexivity.
apply correctitud_lt_nat.
apply resta_lt.
unfold lt.
exact H.
Qed.

Lemma menos_1_0: forall n, S n - n = 1.
Proof.
induction n.
reflexivity.
simpl.
rewrite pred_resta.
simpl.
exact IHn.
Qed.

Lemma leq_0: forall n, n <= 0 <-> n = 0.
Proof.
split.
intro.
destruct n.
reflexivity.
omega.
intro.
rewrite H.
apply le_n.
Qed.

Lemma resta_eq_0: forall n m, m <= n -> m - n = 0.
Proof.
induction n.
intros.
simpl.
apply leq_0 in H.
exact H.
simpl.
intros.
destruct m.
rewrite resta_0.
reflexivity.
rewrite pred_resta.
simpl.
rewrite leq_S_S in H.
specialize IHn with m.
pose(IHn H).
exact e.
Qed.

Lemma div_0: forall n, 0 < n -> div 0 n = 0.
Proof.
intros.
rewrite div_equation.
apply correctitud_lt_nat in H.
rewrite H.
apply leq_nat_false in H.
rewrite H.
reflexivity.
Qed.

Lemma div_n_n: forall n, 0 < n -> div n n = 1.
intros.
induction n.
omega.
rewrite div_equation.
simpl.
rewrite leq_n_n.
rewrite suc_iny.
rewrite menos_1_0.
simpl.
rewrite div_0.
reflexivity.
exact H.
Qed.

Lemma divide_m_n_y_div_m_n_leq_1: 
forall m n, 0 < m -> divide m n = true /\ div n m =1 -> m = n.
Proof.
intros.
destruct H0.
remember H0.
clear Heqe.
rewrite multiplo_divide in H0.
apply def_multiplo in H0.
destruct H0.
case_eq(eq_nat x (div n m)).
intro.
apply correctitud_eq_nat in H2.
rewrite <- H2 in H1.
rewrite H1 in H0.
rewrite mult_conmutativa in H0.
simpl in H0.
rewrite suma_0 in H0.
exact H0.
intro.
assert((div n m) * m * x = n).
rewrite H1.
simpl.
rewrite suma_0.
exact H0.
rewrite (mult_conmutativa (div n m) _) in H3.
rewrite div_mult in H3.
apply mult_identidad in H3.
rewrite H3 in H0.
rewrite mult_conmutativa in H0.
simpl in H0.
rewrite suma_0 in H0.
exact H0.
assert(1 <= div n m).
rewrite <- H1.
apply le_n.
apply div_gt_1 in H4.
exact H4.
exact H.
exact H.
unfold divide in e.
apply correctitud_eq_nat in e.
exact e.
apply correctitud_lt_nat.
exact H.
Qed.

(* Elimina la primera ocurrencia de un elemento en una lista *)
Fixpoint quitar (e: nat)(l : list nat) : list nat :=
match l with
| nil => nil
| x :: xs => match eq_nat e x with
  | false => x :: quitar e xs
  | true => xs
  end
end.

Fixpoint permutacion (l1: list nat) (l2:list nat) : bool :=
match l1 with
| nil => match l2 with
  | nil => true
  | _::_ => false
  end
| x :: xs => match l2 with
  | nil => false
  | y :: ys => andb (member x (y :: ys)) (permutacion xs (quitar x l2))
end
end.

Fixpoint primel (xs:list nat): bool :=
match xs with
| nil => true
| y::ys => andb (primo y) (primel ys)
end.

Theorem correctitud_descomponer: 
forall m, 1 < m -> primel (descomponer m) = true /\ prodl (descomponer m) = m.
Proof.
intros.
induction m using (well_founded_ind lt_wf).
split.
remember H.
clear Heql.
rewrite descomponer_equation.
apply correctitud_lt_nat in H.
rewrite H.
apply correctitud_lt_nat in H.
apply descomponer_term2 in H.
destruct H.
destruct H.
destruct H.
rewrite H.
simpl.
apply correctitud_andb.
split.
assert(member x (factores m) = true).
rewrite H.
simpl.
rewrite eq_nat_n_n.
reflexivity.
apply correctitud_factores in H2.
destruct H2.
exact H2.
apply lt_1_implies_0 in l.
exact l.
specialize H0 with (div m x).
assert(div m x < m).
apply descomponer_term.
split.
exact l.
exact H1.
pose(H0 H2).
case_eq(lt_nat 1 (div m x)).
intro.
apply correctitud_lt_nat in H3.
pose(a H3).
destruct a0.
exact H4.
intro.
apply correctitud_lt_nat_false in H3.
apply leq_1 in H3.
case_eq H3.
intros.
rewrite e.
rewrite descomponer_equation.
simpl.
reflexivity.
intros.
rewrite e.
rewrite descomponer_equation.
simpl.
reflexivity.
rewrite descomponer_equation.
remember H.
clear Heql.
apply correctitud_lt_nat in H.
rewrite H.
rewrite correctitud_lt_nat in H.
apply descomponer_term2 in H.
destruct H.
destruct H.
destruct H.
rewrite H.
simpl.
specialize H0 with (div m x).
assert(div m x < m).
apply descomponer_term.
split.
exact l.
exact H1.
pose(nH := H0 H2).
case_eq(lt_nat 1 (div m x)).
intro.
apply correctitud_lt_nat in H3.
pose (nnH := nH H3).
destruct nnH.
rewrite H5.
apply div_mult.
apply lt_1_implies_0 in H1.
exact H1.
assert(member x (factores m) = true).
rewrite H.
simpl.
rewrite eq_nat_n_n.
reflexivity.
apply correctitud_factores in H6.
destruct H6.
unfold divide in H7.
apply correctitud_eq_nat in H7.
exact H7.
apply lt_1_implies_0 in l.
exact l.
intro.
rewrite descomponer_equation.
rewrite H3.
simpl.
rewrite mult_conmutativa.
simpl.
rewrite suma_0.
rewrite correctitud_lt_nat_false in H3.
apply leq_1 in H3.
case_eq(H3).
intros.
clear H4.
assert (member x (factores m) = true).
rewrite H.
simpl.
rewrite eq_nat_n_n.
reflexivity.
apply correctitud_factores in H4.
destruct H4.
unfold divide in H5.
apply correctitud_eq_nat in H5.
assert(div m x = 0 /\ modulo m x = 0).
split.
exact e.
exact H5.
apply correctitud_divmod in H6.
destruct H6.
simpl in H6.
rewrite H6 in l.
inversion l.
apply lt_1_implies_0 in H1.
exact H1.
apply lt_1_implies_0 in l.
exact l.
intros.
clear H4.
assert(divide x m = true).
apply correctitud_factores.
apply lt_1_implies_0 in l.
exact l.
rewrite H.
simpl.
rewrite eq_nat_n_n.
reflexivity.
assert(divide x m = true /\ div m x = 1).
split.
exact H4.
exact e.
apply divide_m_n_y_div_m_n_leq_1 in H5.
exact H5.
apply lt_1_implies_0 in H1.
exact H1.
Qed.

Lemma descomponer_gt_1: forall m, 1 < m -> exists x, exists xs, descomponer m = x :: xs.
intros.
rewrite descomponer_equation.
case_eq(lt_nat 1 m).
intro.
assert(exists x xs, factores m = x :: xs /\ 1 < x).
apply descomponer_term2.
exact H.
destruct H1.
destruct H1.
destruct H1.
rewrite H1.
exists x.
exists (descomponer (div m x)).
reflexivity.
intro.
apply not_true in H0.
rewrite correctitud_lt_nat in H0.
congruence.
Qed.

Lemma primo_implies_gt_0: forall m, primo m = true -> 0 < m.
Proof.
intros.
apply primo_implies_gt_1 in H.
apply lt_1_implies_0 in H.
exact H.
Qed.

Lemma divide_mayor: forall m n, n > 0 -> n < m -> divide m n = false.
Proof.
intros.
apply correctitud_eq_nat_f.
unfold not.
intro.
rewrite modulo_equation in H1.
assert(0 < m).
omega.
apply correctitud_lt_nat in H2.
rewrite H2 in H1.
apply correctitud_lt_nat in H0.
apply leq_nat_false in H0.
rewrite H0 in H1.
omega.
Qed.

Lemma correctitud_primo2: forall n, primo n = true -> (forall k, k <> 1 /\ k <> n <-> divide k n = false).
Proof.
intros.
split.
intro.
remember H.
clear Heqe.
rewrite correctitud_primo in e.
case_eq(lt_nat k n).
intro.
apply correctitud_lt_nat in H1.
case_eq(eq_nat k 0).
intro.
apply correctitud_eq_nat in H2.
rewrite H2.
unfold divide.
rewrite modulo_equation.
simpl.
reflexivity.
intro.
apply correctitud_eq_nat_f in H2.
destruct H0.
assert(1 < k).
omega.
assert(1 < k < n).
omega.
specialize e with k.
pose(e H5).
exact e0.
intro.
apply lt_nat_false in H1.
apply correctitud_leq_nat in H1.
case_eq(eq_nat k n).
intro.
apply correctitud_eq_nat in H2.
omega.
intro.
apply correctitud_eq_nat_f in H2.
apply neq_sym in H2.
assert( n <> k /\ n <= k).
split.
exact H2.
exact H1.
apply menor_distinto in H3.
apply divide_mayor.
apply primo_implies_gt_0 in H.
exact H.
exact H3.
apply primo_implies_gt_1 in H.
exact H.
intro.
split.
unfold not.
intro.
rewrite H1 in H0.
rewrite divide_1_n in H0.
congruence.
unfold not.
intro.
rewrite H1 in H0.
rewrite divide_n_n in H0.
congruence.
apply correctitud_lt_nat.
apply primo_implies_gt_0 in H.
exact H.
Qed.

Lemma modulo_menor: forall a b, 0 < b -> modulo a b < b.
Proof.
intros.
induction a using (well_founded_ind lt_wf).
rewrite modulo_equation.
apply correctitud_lt_nat in H.
rewrite H.
case_eq(leq_nat b a).
intro.
specialize H0 with (a - b).
assert(a-b < a).
apply div_term.
exact H.
exact H1.
pose (H0 H2).
exact l.
intro.
apply leq_nat_false in H1.
apply correctitud_lt_nat.
exact H1.
Qed.

Lemma modulo_resta: forall a b, 0 < b ->  b <= a -> modulo a b = modulo (a - b) b.
Proof.
intros.
rewrite modulo_equation.
apply correctitud_lt_nat in H.
apply correctitud_leq_nat in H0.
rewrite H.
rewrite H0.
reflexivity.
Qed.

(* Linda para demo, con la siguiente *)
Lemma not_divide: forall a b, 0 < b -> (divide b a = false <-> exists q r,  0 < r < b /\ a = b * q + r).
Proof.
split.
intro.
exists (div a b).
exists (modulo a b).
unfold divide in H0.
apply correctitud_eq_nat_f in H0.
split.
split.
omega.
apply modulo_menor.
exact H.
induction a using (well_founded_ind lt_wf).
rewrite div_equation.
rewrite modulo_equation.
apply correctitud_lt_nat in H.
rewrite H.
case_eq(leq_nat b a).
intro.
rewrite mult_Sn.
specialize H1 with (a-b).
assert (a-b < a).
apply div_term.
exact H.
exact H2.
pose(H1 H3).
assert(modulo a b = modulo (a - b) b).
apply modulo_resta.
apply correctitud_lt_nat.
exact H.
apply correctitud_leq_nat in H2.
exact H2.
rewrite H4 in H0.
pose (e H0).
rewrite suma_asociativa.
rewrite <- e0.
rewrite suma_conmutativa.
rewrite resta_suma_n.
reflexivity.
exact H2.
intro.
rewrite mult_0.
simpl.
reflexivity.
intro.
destruct H0.
destruct H0.
destruct H0.
assert(a = b * x + x0 /\ x0 < b).
split.
exact H1.
omega.
rewrite mult_conmutativa in H2.
apply correctitud_divmod in H2.
destruct H2.
unfold divide.
apply correctitud_eq_nat_f.
rewrite <- H3 in H0.
omega.
exact H.
Qed.

Lemma resta_resta: forall a b c, a - (b + c) = a - b - c.
Proof.
intros.
induction c.
simpl.
rewrite suma_0.
reflexivity.
simpl.
rewrite <- IHc.
rewrite suma_conmutativa with b _.
simpl.
rewrite suma_conmutativa with c b.
reflexivity.
Qed.

Lemma resta_distributiva: forall a b c, a * (b - c) = a*b - a*c.
Proof.
intros.
induction c.
simpl.
rewrite mult_0.
reflexivity.
simpl.
rewrite mult_Sn.
SearchAbout menos.
rewrite mult_conmutativa.
rewrite mult_pred.
rewrite mult_conmutativa.
rewrite IHc.
rewrite suma_conmutativa with a _.
rewrite resta_resta.
reflexivity.
Qed.

Lemma gcd_term: forall m n, 0 < n -> modulo m n < n.
Proof.
intros.
induction m using (well_founded_ind lt_wf).
rewrite modulo_equation.
apply correctitud_lt_nat in H.
rewrite H.
case_eq (leq_nat n m).
intro.
specialize H0 with (m-n).
assert(m - n < m).
apply div_term.
exact H.
exact H1.
pose( H0 H2).
exact l.
intro.
apply correctitud_leq_nat_false in H1.
exact H1.
Qed. 

Function gcd (a:nat) (b:nat) {measure (fun n => n) b} : nat :=
match b with
  | 0 => b
  | S k => gcd b (modulo a b)
end.
intros.
apply gcd_term.
omega.
Qed.


Lemma mult_div: forall m n, 0 < n -> div (m*n) n = m.
Proof.
intros.
assert(div (m * n) n = m /\ modulo (m*n) n = 0).
apply correctitud_divmod.
exact H.
split.
rewrite suma_0.
reflexivity.
exact H.
destruct H0.
exact H0.
Qed.

Lemma div_ext_mult: forall a b c, 0 < b -> divide b a = true -> c * (div a b) = div (c * a) b.
Proof.
intros.
apply def_divide in H0.
destruct H0.
rewrite <- H0.
rewrite mult_conmutativa with b _.
rewrite mult_div.
rewrite <- mult_asociativa.
rewrite mult_div.
reflexivity.
exact H.
exact H.
apply correctitud_lt_nat.
exact H.
Qed.

Lemma primo_iguales: forall m n, primo m = true -> primo n = true -> divide m n = true -> m = n.
Proof.
intros.
remember H0.
clear Heqe.
assert(forall k, k <> 1 /\ k <> n <-> divide k n = false).
apply correctitud_primo2.
exact H0.
case_eq(lt_nat m n).
intro.
specialize H2 with m.
apply correctitud_lt_nat in H3.
assert(m <> 1 /\ m <> n).
split.
apply primo_implies_gt_1 in H.
omega.
omega.
destruct H2.
pose(H2 H4).
congruence.
intro.
apply lt_nat_false in H3.
apply correctitud_leq_nat in H3.
case_eq(eq_nat n m).
intro.
apply correctitud_eq_nat in H4.
apply eq_sym in H4.
exact H4.
intro.
apply correctitud_eq_nat_f in H4.
assert(n <> m /\ n <= m).
split.
exact H4.
exact H3.
apply menor_distinto in H5.
assert( m <> 1 /\ m <> n).
split.
apply primo_implies_gt_1 in H.
omega.
omega.
specialize H2 with m.
destruct H2.
pose(H2 H6).
congruence.
Qed.

Lemma eq_nat_f_sym: forall m n, eq_nat m n = false <-> eq_nat n m = false.
Proof.
split.
intro.
apply correctitud_eq_nat_f.
apply correctitud_eq_nat_f in H.
omega.
intro.
apply correctitud_eq_nat_f.
apply correctitud_eq_nat_f in H.
omega.
Qed.

Lemma prodl_exists: forall xs m, member m xs = true -> exists ys, prodl xs = m * prodl ys.
Proof.
intros.
exists (quitar m xs).
induction xs.
simpl in H.
congruence.
simpl.
case_eq(eq_nat m a).
intro.
apply correctitud_eq_nat in H0.
rewrite H0.
reflexivity.
intro.
simpl in H.
apply eq_nat_f_sym in H0.
rewrite H0 in H.
simpl.
rewrite <- mult_asociativa.
rewrite mult_conmutativa with m a.
rewrite mult_asociativa.
pose(IHxs H).
rewrite IHxs.
reflexivity.
exact H.
Qed.

Lemma prodl_divide: forall xs m, 0 < prodl xs -> 0 < m -> member m xs = true -> divide m (prodl xs) = true.
Proof.
intros.
apply prodl_exists in H1.
destruct H1.
rewrite H1.
apply def_divide.
apply correctitud_lt_nat.
exact H0.
exists (prodl x).
reflexivity.
Qed.

Lemma primel_xs: forall x xs, primel (x :: xs) = true -> primel xs = true.
Proof.
intros.
simpl in H.
apply correctitud_andb in H.
destruct H.
exact H0.
Qed.

Lemma prod_eq_1: forall m n, m*n = 1 <-> m = 1 /\ n = 1.
Proof.
split.
intro.
destruct m.
simpl in H.
congruence.
destruct n.
rewrite mult_0 in H.
congruence.
simpl in H.
rewrite suc_iny in H.
destruct n.
destruct m.
split.
reflexivity.
reflexivity.
simpl in H.
congruence.
simpl in H.
congruence.
intros.
destruct H.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Lemma prodl_gt_0: forall xs, primel xs = true -> 0 < prodl xs.
Proof.
intros.
induction xs.
simpl.
omega.
simpl in H.
apply correctitud_andb in H.
destruct H.
simpl.
apply primo_implies_gt_1 in H.
apply def_lt in H.
destruct H.
simpl in H.
rewrite <- H.
pose(IHxs H0).
apply def_lt in l.
simpl in l.
destruct l.
rewrite <- H1.
apply def_lt.
simpl.
exists (x0 + S (x0 + x * S x0)).
reflexivity.
Qed.

Lemma prodl_leq_1: forall xs, primel xs = true -> (prodl xs = 1 <-> xs = nil).
Proof.
induction xs.
split.
intro.
reflexivity.
intro.
simpl.
reflexivity.
intro.
simpl in H.
apply correctitud_andb in H.
destruct H.
split.
intro.
pose(IHxs H0).
destruct i.
simpl in H1.
apply prod_eq_1 in H1.
destruct H1.
apply primo_implies_gt_1 in H.
omega.
intro.
rewrite H1.
reflexivity.
Qed.

Lemma prodl_gt_1: forall a xs, primel (a::xs) = true -> 1 < prodl (a::xs).
Proof.
intros.
simpl.
simpl in H.
apply correctitud_andb in H.
destruct H.
apply primo_implies_gt_1 in H.
assert(0 < prodl xs).
apply prodl_gt_0.
exact H0.
apply def_lt.
simpl.
apply def_lt in H.
simpl in H.
destruct H.
rewrite <- H.
apply def_lt in H1.
simpl in H1.
destruct H1.
rewrite <- H1.
simpl.
rewrite suma_conmutativa.
simpl.
exists (x0 + x * S x0 + x0).
reflexivity.
Qed.

Lemma divide_k_1: forall k, divide k 1 = true <-> k = 1.
Proof.
split.
intro.
case_eq(eq_nat k 0).
intro.
apply correctitud_eq_nat in H0.
rewrite H0 in H.
unfold divide in H.
rewrite modulo_equation in H.
simpl in H.
congruence.
intro.
apply correctitud_eq_nat_f in H0.
assert(k > 0).
omega.
apply divide_entre in H.
omega.
omega.
intro.
rewrite H.
apply divide_1_n.
Qed.

Lemma modulo_mult: forall m n, 0 < m -> modulo (m * n) m = 0.
Proof.
intros.
assert(divide m (m*n) = true <-> modulo (m*n) m = 0).
unfold divide.
rewrite correctitud_eq_nat.
apply iff_refl.
rewrite <- H0.
apply def_divide.
apply correctitud_lt_nat.
exact H.
exists n.
reflexivity.
Qed.

Lemma divide_k_k_mult_n: forall k m n, 0 < k -> divide k m = true -> divide k (m * n) = true.
Proof.
intros.
unfold divide.
apply correctitud_eq_nat.
apply def_divide in H0.
destruct H0.
rewrite <- H0.
rewrite mult_asociativa.
apply modulo_mult.
exact H.
apply correctitud_lt_nat.
exact H.
Qed.

Lemma divide_member: forall k xs, 0 < k ->member k xs = true -> divide k (prodl xs) = true.
Proof.
intros.
induction xs.
simpl in H0.
congruence.
case_eq(eq_nat a k).
intro.
simpl.
apply correctitud_eq_nat in H1.
rewrite H1.
apply divide_k_k_mult_n.
exact H.
apply divide_n_n.
apply correctitud_lt_nat.
exact H.
intro.
simpl in H0.
rewrite H1 in H0.
pose(IHxs H0).
simpl.
rewrite mult_conmutativa.
apply divide_k_k_mult_n.
exact H.
exact e.
Qed.

Lemma prime_quitar: forall xs a, primel xs = true -> primel (quitar a xs) = true.
Proof.
intros.
induction xs.
reflexivity.
case_eq(eq_nat a a0).
intro.
apply correctitud_eq_nat in H0.
rewrite H0.
simpl.
rewrite eq_nat_n_n.
simpl in H.
apply correctitud_andb in H.
destruct H.
exact H1.
intro.
simpl.
rewrite H0.
simpl.
apply correctitud_andb.
simpl in H.
apply correctitud_andb in H.
destruct H.
split.
exact H.
pose(IHxs H1).
exact e.
Qed.

(* Lema util para el proximo *)
Lemma quitar_prodl: forall xs k, 0 < k -> member k xs = true -> prodl (quitar k xs) = div (prodl xs) k.
Proof.
intros.
induction xs.
simpl in H0.
congruence.
case_eq(eq_nat a k).
intro.
apply correctitud_eq_nat in H1.
rewrite H1.
simpl.
rewrite eq_nat_n_n.
rewrite mult_conmutativa.
rewrite mult_div.
reflexivity.
exact H.
intro.
simpl in H0.
rewrite H1 in H0.
pose(IHxs H0).
simpl.
rewrite eq_nat_f_sym in H1.
rewrite H1.
simpl.
assert(divide k (prodl xs) = true).
apply def_divide.
apply correctitud_lt_nat.
exact H.
assert(exists ys, prodl xs = k * prodl ys).
apply prodl_exists.
exact H0.
destruct H2.
exists (prodl x).
apply eq_sym.
exact H2.
rewrite <- div_ext_mult.
rewrite e.
reflexivity.
exact H.
exact H2.
Qed.

Lemma quitar_not_member: forall xs k, member k xs = false -> quitar k xs = xs.
Proof.
intros.
induction xs.
reflexivity.
simpl in H.
case_eq(eq_nat a k).
intro.
rewrite H0 in H.
congruence.
intro.
rewrite H0 in H.
simpl.
apply eq_nat_f_sym in H0.
rewrite H0.
pose(IHxs H).
rewrite e.
reflexivity.
Qed.

Lemma prodl_eq: forall xs ys k, 0 < k -> prodl xs = prodl ys -> member k xs = true -> member k ys = true -> prodl (quitar k xs) = prodl (quitar k ys).
Proof.
intros.
rewrite quitar_prodl.
rewrite quitar_prodl.
rewrite H0.
reflexivity.
exact H.
exact H2.
exact H.
exact H1.
Qed.

Lemma mult_lt: forall m n, 0 < m -> 1 < n -> m < n * m.
Proof.
intros.
apply def_lt.
rewrite def_lt in H0.
simpl in H0.
destruct H0.
rewrite <- H0.
apply def_lt in H.
destruct H.
simpl in H.
rewrite <- H.
simpl.
exists (x0 + x * S x0).
reflexivity.
Qed.

Lemma comb_le: forall a1 b1 a2 b2, a1 <= b1 -> a2 <= b2 -> a1 + a2 <= b1 + b2.
Proof.
intros.
apply def_leq.
apply def_leq in H.
destruct H.
apply def_leq in H0.
destruct H0.
rewrite <- H.
rewrite <- H0.
exists (x + x0).
rewrite suma_asociativa with a1 x _.
rewrite <- suma_asociativa with x _ _.
rewrite suma_conmutativa with x a2.
rewrite suma_asociativa with a2 x x0.
rewrite <- suma_asociativa with a1 a2 _.
reflexivity.
Qed.

Lemma le_suma_ambos_lados: forall m n k, m <= n <-> m + k <= n + k.
Proof.
intros.
split.
intro.
apply def_leq in H.
destruct H.
rewrite <- H.
apply def_leq.
exists x.
rewrite suma_asociativa.
rewrite suma_conmutativa with k x.
rewrite <- suma_asociativa.
reflexivity.
intro.
rewrite def_leq in H.
destruct H.
apply resta_ambos_lados with _ _ k in H.
rewrite suma_conmutativa with n k in H.
rewrite suma_resta_n in H.
rewrite suma_conmutativa with m k in H.
rewrite suma_asociativa in H.
rewrite suma_resta_n in H.
rewrite def_leq.
exists x.
exact H.
Qed.

Lemma prod_leq: forall a b m, 0 < m -> (a * m <= b * m <-> a <= b).
Proof.
induction a.
split.
intros.
omega.
induction b.
intros.
simpl.
apply le_n.
intro.
simpl.
omega.
intros.
split.
intro.
destruct b.
simpl in H0.
apply def_lt in H.
destruct H.
simpl in H.
rewrite <- H in H0.
simpl in H0.
omega.
simpl in H0.
rewrite suma_conmutativa in H0.
rewrite suma_conmutativa with m _ in H0.
rewrite <- le_suma_ambos_lados in H0.
specialize IHa with b m.
pose(IHa H).
destruct i.
pose (H1 H0).
apply leq_S_S.
exact l.
intro.
destruct b.
omega.
simpl.
rewrite suma_conmutativa.
rewrite suma_conmutativa with m _.
rewrite <- le_suma_ambos_lados.
specialize IHa with b m.
pose(IHa H).
rewrite leq_S_S in H0.
destruct i.
pose(H2 H0).
exact l.
Qed.

Lemma prodl_concat: forall xs ys, prodl xs * prodl ys = prodl (xs ++ ys).
Proof.
intros.
induction xs.
simpl.
apply suma_0.
simpl.
rewrite mult_asociativa.
rewrite IHxs.
reflexivity.
Qed.

Lemma primel_concat: forall xs ys, primel xs = true -> primel ys = true -> primel (xs ++ ys) = true.
Proof.
intros.
induction xs.
simpl.
exact H0.
simpl.
simpl in H.
apply correctitud_andb in H.
destruct H.
apply correctitud_andb.
split.
exact H.
pose(IHxs H1).
exact e.
Qed.


Lemma member_concat: forall xs ys k, member k (xs ++ ys) = true -> member k xs = true \/ member k ys = true.
Proof.
intros.
induction xs.
simpl.
apply or_intror.
simpl in H.
exact H.
simpl.
case_eq(eq_nat a k).
intro.
apply or_introl.
reflexivity.
intro.
simpl in H.
rewrite H0 in H.
pose(IHxs H).
exact o.
Qed.

Lemma divide_diff: forall a b p, 0 < p -> divide p a = true -> divide p b = true -> divide p (a - b) = true.
Proof.
intros.
apply correctitud_lt_nat in H.
apply def_divide in H0.
apply def_divide in H1.
destruct H0.
destruct H1.
rewrite <- H0.
rewrite <- H1.
rewrite <- resta_distributiva.
apply def_divide.
exact H.
exists (x - x0).
reflexivity.
exact H.
exact H.
Qed.

(* interesante la precondicion de p <= a *)
Lemma diff_divide: forall a p, 0 < p ->  p <= a -> divide p (a - p) = true -> divide p a = true.
intros.
apply correctitud_lt_nat in H.
apply def_divide in H1.
apply def_divide.
exact H.
destruct H1.
apply (suma_ambos_lados _ _ p) in H1.
rewrite resta_suma_n in H1.
assert(p*x + p = p*x + p*1).
rewrite mult_conmutativa with _ 1.
simpl.
rewrite suma_0.
reflexivity.
rewrite H2 in H1.
rewrite mult_conmutativa with p _ in H1.
rewrite mult_conmutativa with p _ in H1.
rewrite <- mult_distributiva in H1.
exists (x + 1).
rewrite mult_conmutativa.
exact H1.
apply correctitud_leq_nat.
exact H0.
exact H.
Qed.

Lemma quitar_member: forall ys k a, eq_nat k a = false -> (member k (quitar a ys) = true <-> member k ys = true).
Proof.
intros.
induction ys.
simpl.
reflexivity.
simpl.
case_eq(eq_nat a a0).
intro.
case_eq(eq_nat a0 k).
intro.
simpl in IHys.
apply correctitud_eq_nat in H1.
rewrite H1 in H0.
apply eq_nat_f_sym in H.
congruence.
intro.
reflexivity.
intro.
case_eq (eq_nat a0 k).
intro.
simpl.
rewrite H1.
reflexivity.
intro.
simpl.
rewrite H1.
exact IHys.
Qed.

Lemma permutacion_member: forall xs ys, permutacion xs ys = true -> (forall k, (member k xs = true <-> member k ys = true)).
Proof.
induction xs.
split.
intro.
simpl in H0.
congruence.
intro.
destruct ys.
simpl in H0.
congruence.
simpl in H.
congruence.
intros.
destruct ys.
simpl in H.
congruence.
case_eq(eq_nat n a).
intro.
simpl in H.
rewrite H0 in H.
simpl in H.
apply correctitud_eq_nat in H0.
rewrite H0 in H.
rewrite eq_nat_n_n in H.
specialize IHxs with ys k.
pose(IHxs H).
simpl.
rewrite H0.
case_eq(eq_nat a k).
intro.
reflexivity.
intro.
specialize i with k.
exact i.
intro.
simpl in H.
rewrite H0 in H.
rewrite eq_nat_f_sym in H0.
rewrite H0 in H.
apply correctitud_andb in H.
destruct H.
simpl.
case_eq(eq_nat a k).
intro.
apply correctitud_eq_nat in H2.
rewrite <- H2.
apply eq_nat_f_sym in H0.
rewrite H0.
rewrite H.
reflexivity.
intro.
rewrite eq_nat_f_sym in H0.
specialize IHxs with (n :: quitar a ys) k.
pose(IHxs H1).
rewrite i.
simpl.
case_eq(eq_nat n k).
intro.
reflexivity.
intro.
apply quitar_member.
apply eq_nat_f_sym.
exact H2.
Qed.

Lemma prod_componentes_lt: forall m n p, 1 < m -> 1 < p -> 1 < n -> m * n = p -> m < p /\ n < p.
Proof.
intros.
apply def_lt in H.
destruct H.
simpl in H.
apply def_lt in H0.
destruct H0.
simpl in H0.
apply def_lt in H1.
destruct H1.
simpl in H1.
rewrite <- H1 in H2.
rewrite <- H0 in H2.
rewrite <- H in H2.
split.
apply def_lt.
rewrite <- H.
rewrite <- H0.
rewrite mult_conmutativa in H2.
rewrite <- H2.
simpl.
exists ((S (x + x1 * S (S x)))).
reflexivity.
apply def_lt.
rewrite <- H1.
rewrite<- H0.
rewrite <- H2.
simpl.
exists ((S (x1 + x * S (S x1)))).
reflexivity.
Qed.

Lemma primel_prod_same: forall xs k, primel xs = true -> primo k = true -> prodl xs = k -> member k xs = true.
Proof.
intros.
remember H0.
clear Heqe.
induction xs.
simpl in H1.
rewrite <- H1 in H0.
unfold primo in H0.
simpl in H0.
apply correctitud_andb in H0.
destruct H0.
congruence.
simpl in H1.
assert(exists h, a * h = k).
exists (prodl xs).
exact H1.
apply def_divide in H2.
rewrite correctitud_primo in H0.
specialize H0 with a.
destruct xs.
simpl in H1.
rewrite mult_conmutativa in H1.
simpl in H1.
rewrite suma_0 in H1.
rewrite H1.
simpl.
rewrite eq_nat_n_n.
reflexivity.
assert(1 < a < k).
split. 
simpl in H.
apply correctitud_andb in H.
destruct H.
apply primo_implies_gt_1 in H.
exact H.
apply divide_entre in H2.
apply prod_componentes_lt in H1.
destruct H1.
assert(1 <= a < k).
omega.
omega.
simpl in H.
apply correctitud_andb in H.
destruct H.
apply primo_implies_gt_1.
exact H.
apply primo_implies_gt_1 in e.
exact e.
apply prodl_gt_1.
simpl in H.
apply correctitud_andb in H.
destruct H.
simpl.
exact H3.
split.
simpl in H.
apply correctitud_andb in H.
destruct H.
apply primo_implies_gt_0 in H.
exact H.
apply primo_implies_gt_0 in e.
exact e.
pose(H0 H3).
congruence.
apply primo_implies_gt_1 in e.
exact e.
apply correctitud_lt_nat.
simpl in H.
apply correctitud_andb in H.
destruct H.
apply primo_implies_gt_0 in H.
exact H.
Qed.

Lemma mult_gt_0: forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
intros.
apply def_lt.
simpl.
apply def_lt in H.
simpl in H.
apply def_lt in H0.
simpl in H0.
destruct H.
destruct H0.
rewrite <- H.
rewrite <- H0.
simpl.
exists (x0 + x * S x0).
reflexivity.
Qed.

Lemma primel_and_same_prod_then_eq_aux: forall n0 n1 xs ys,
(forall y : nat,
    y < prodl (n0 :: xs) ->
    forall xs ys : list nat,
    y = prodl xs ->
    primel xs = true ->
    primel ys = true -> prodl xs = prodl ys -> permutacion xs ys = true) -> primel (n0 :: xs) = true -> primel (n1 :: ys) = true -> prodl (n0 :: xs) = prodl (n1 :: ys) -> n0 <> n1 -> lt_nat n0 n1 = true 
-> permutacion (n0 :: xs) (n1 :: ys) = true.
Proof.
intros.
apply correctitud_lt_nat in H4.
assert(exists xs, primel xs = true /\ prodl xs = (n1 - n0)).
exists (descomponer (n1 - n0)).
case_eq(lt_nat 1 (n1 - n0)).
intro.
apply correctitud_descomponer.
apply correctitud_lt_nat in H5.
exact H5.
intro.
split.
rewrite descomponer_equation.
rewrite H5.
reflexivity.
case_eq(eq_nat (n1 - n0) 1).
intro.
rewrite descomponer_equation.
rewrite H5.
apply correctitud_eq_nat in H6.
rewrite H6.
reflexivity.
intro.
apply correctitud_lt_nat_false in H5.
apply correctitud_eq_nat_f in H6.
assert(n1 - n0 = 0).
omega.
apply menos_gt_0 in H4.
omega.
destruct H5.
assert((prodl ys)*(prodl x) = (prodl ys) * (n1 - n0)).
destruct H5.
rewrite H6.
reflexivity.
rewrite resta_distributiva in H6.
rewrite mult_conmutativa with _ n1 in H6.
assert(n1 * prodl ys = prodl ( n1 :: ys)).
simpl.
reflexivity.
rewrite H7 in H6.
rewrite <- H2 in H6.
rewrite mult_conmutativa with _ n0 in H6.
assert(prodl (n0 :: xs) - n0 * prodl ys < prodl (n0 :: xs)).
apply div_term.
apply correctitud_lt_nat.
apply mult_gt_0.
simpl in H0.
apply correctitud_andb in H0.
destruct H0.
apply primo_implies_gt_0 in H0.
exact H0.
apply prodl_gt_0.
apply primel_xs in H1.
exact H1.
simpl in H2.
simpl.
rewrite H2.
apply correctitud_leq_nat.
apply prod_leq.
apply prodl_gt_0.
apply primel_xs in H1.
exact H1.
omega.
remember H.
clear Heqe.
specialize (H (prodl (n0 :: xs) - n0 * prodl ys)).
pose(H H8).
assert(divide n0 (prodl (n0 :: xs)) = true  /\ divide n0 (n0 * prodl ys) = true).
{
  split.
  apply divide_member.
  simpl in H0.
  apply correctitud_andb in H0.
  destruct H0.
  apply primo_implies_gt_0 in H0.
  exact H0.
  simpl.
  rewrite eq_nat_n_n.
  reflexivity.
  apply def_divide.
  apply correctitud_lt_nat.
  simpl in H0.
  apply correctitud_andb in H0.
  destruct H0.
  apply primo_implies_gt_0 in H0.
  exact H0.
  exists (prodl ys).
  reflexivity.
}
destruct H9.
remember H0.
simpl in H0.
clear Heqe1.
apply correctitud_andb in H0.
destruct H0.
remember H0.
clear Heqe2.
apply primo_implies_gt_0 in H0.
assert(divide n0 (prodl (n0 :: xs) - (n0 * prodl ys)) = true).
apply divide_diff.
exact H0.
exact H9.
exact H10.
rewrite <- H6 in H12.
rewrite prodl_concat in H12.
rewrite prodl_concat in H6.
assert(member n0 (ys ++ x) = true).
{
  apply def_divide in H12.
  destruct H12.
  case_eq(lt_nat 1 x0).
  intro.
  assert(primel (descomponer x0) = true /\ prodl(descomponer x0) = x0).
  apply correctitud_descomponer.
  apply correctitud_lt_nat.
  exact H13.
  destruct H14.
  rewrite <- H15 in H12.
  specialize e0 with (ys ++ x) (n0 :: (descomponer x0)).
  apply eq_sym in H6.
  assert(primel (ys ++ x) = true).
  apply primel_concat.
  apply primel_xs in H1.
  exact H1.
  destruct H5.
  exact H5.
  assert(primel (n0 :: descomponer x0) = true).
  simpl.
  apply correctitud_andb.
  split.
  exact e2.
  exact H14.
  assert(prodl (ys ++ x) = prodl (n0 :: descomponer x0)).
  simpl.
  apply eq_sym.
  exact H12.
  pose(e0 H6 H16 H17 H18).
  apply permutacion_member with _ _ n0 in e3.
  destruct e3.
  assert(member n0 (n0 :: descomponer x0) = true).
  simpl.
  rewrite eq_nat_n_n.
  reflexivity.
  pose(H20 H21).
  exact e3.
  intro.
  apply correctitud_lt_nat_false in H13.
  case_eq(eq_nat x0 0).
  intro.
  apply correctitud_eq_nat in H14.
  rewrite H14 in H12.
  rewrite mult_0 in H12.
  assert(0 < prodl (ys ++ x)).
  apply prodl_gt_0.
  apply primel_concat.
  apply primel_xs in H1.
  exact H1.
  destruct H5.
  exact H5.
  omega.
  intro.
  case_eq(eq_nat x0 1).
  intro.
  apply correctitud_eq_nat in H15.
  rewrite H15 in H12.
  rewrite mult_conmutativa in H12.
  simpl in H12.
  rewrite suma_0 in H12.
  apply primel_prod_same.
  apply primel_concat.
  simpl in H1.
  apply correctitud_andb in H1.
  destruct H1.
  exact H16.
  destruct H5.
  exact H5.
  exact e2.
  apply eq_sym in H12.
  exact H12.
  intro.
  apply correctitud_eq_nat_f in H14.
  apply correctitud_eq_nat_f in H15.
  omega.
  apply correctitud_lt_nat.
  apply primo_implies_gt_0 in e2.
  exact e2.
  }
apply member_concat in H13.
case_eq(H13).
intros.
clear H14.
simpl.
apply correctitud_eq_nat_f in H3.
rewrite H3.
apply correctitud_eq_nat_f in H3.
apply neq_sym in H3.
apply correctitud_eq_nat_f in H3.
rewrite H3.
rewrite e3.
simpl.
specialize (e (prodl xs)).
assert(prodl xs < prodl (n0 :: xs)).
{
simpl.
apply mult_lt.
apply prodl_gt_0.
exact H11.
apply primo_implies_gt_1 in e2.
exact e2.
}
pose (e H14).
specialize e4 with xs (n1 :: quitar n0 ys).
assert(prodl xs = prodl xs).
reflexivity.
assert(primel xs = true).
exact H11.
assert(primel (n1 :: quitar n0 ys) = true).
{
  simpl.
  apply correctitud_andb.
  split. 
  simpl in H1.
  apply correctitud_andb in H1.
  destruct H1.
  exact H1.
  apply prime_quitar.
  apply primel_xs in H1.
  exact H1.
}
assert(prodl xs = prodl (n1 :: quitar n0 ys)).
{
apply prodl_eq with _ _ n0 in H2.
simpl in H2.
rewrite eq_nat_n_n in H2.
apply eq_nat_f_sym in H3.
rewrite H3 in H2.
exact H2.
apply primo_implies_gt_0 in e2.
exact e2.
simpl.
rewrite eq_nat_n_n.
reflexivity.
simpl.
rewrite H3.
exact e3.
}
pose(ii := e4 H15 H16 H17 H18).
exact ii.
intros.
destruct H5.
assert(divide n0 (n1 - n0) = true).
rewrite <- H15.
clear H14.
apply prodl_divide.
apply prodl_gt_0.
exact H5.
exact H0.
exact e3.
apply diff_divide in H16.
simpl in H1.
apply correctitud_andb in H1.
destruct H1.
Check correctitud_primo2.
apply correctitud_primo2 with _ n0 in H1.
assert(n0 <> 1 /\ n0 <> n1).
{
  split.
  apply primo_implies_gt_1 in e2.
  omega.
  exact H3.
}
destruct H1.
pose(H1 H18).
congruence.
apply primo_implies_gt_0 in e2.
exact e2.
omega.
Qed.

Lemma eq_nat_sym: forall a b, eq_nat a b = eq_nat b a.
Proof.
induction a.
destruct b.
reflexivity.
reflexivity.
induction b.
reflexivity.
simpl.
exact (IHa b).
Qed.

Lemma permutacion_quitar: forall ys xs a, member a ys = true -> permutacion (quitar a ys) xs = permutacion ys (a::xs).
Proof.
induction ys.
intros.
simpl in H.
congruence.
intros.
simpl.
case_eq(eq_nat a0 a).
intro.
simpl.
rewrite eq_nat_sym.
rewrite H0.
reflexivity.
intro.
rewrite eq_nat_sym.
rewrite H0.
destruct xs.
reflexivity.
simpl.
case_eq(eq_nat n a).
intro.
simpl.
rewrite eq_nat_sym.
rewrite H1.
specialize IHys with xs a0.
simpl in H.
rewrite eq_nat_sym in H.
rewrite H0 in H.
pose(IHys H).
exact e.
intro.
rewrite eq_nat_sym.
rewrite H1.
specialize IHys with (n :: quitar a xs) a0.
simpl in H.
rewrite eq_nat_sym in H.
rewrite H0 in H.
pose(IHys H).
rewrite e.
reflexivity.
Qed.

Lemma permutacion_conmutativa: forall xs ys, permutacion xs ys = true <-> permutacion ys xs = true.
Proof.
induction xs.
intros.
destruct ys.
reflexivity.
reflexivity.
destruct ys.
reflexivity.
case_eq(member a (n :: ys)).
simpl.
intro.
rewrite H.
simpl.
case_eq (eq_nat a n).
intro.
simpl.
apply correctitud_eq_nat in H0.
rewrite H0.
rewrite eq_nat_n_n.
specialize IHxs with ys.
exact IHxs.
intro.
rewrite eq_nat_f_sym in H0.
rewrite H0.
rewrite H0 in H.
split.
admit.
intro.
apply correctitud_andb in H1.
specialize IHxs with (n :: quitar a ys).
rewrite IHxs.
destruct H1.
destruct xs.
simpl in H1.
congruence.
simpl.
simpl in H1.
rewrite H1.
simpl.
case_eq(eq_nat n n0).
intro.
simpl in H2.
rewrite H3 in H2.
rewrite permutacion_quitar.
exact H2.
exact H.
intro.
rewrite permutacion_quitar.
simpl in H2.
rewrite H3 in H2.
exact H2.
exact H.
intro.
simpl.
case_eq(eq_nat n a).
intro.
simpl.
rewrite eq_nat_sym.
rewrite H0.
simpl.
specialize IHxs with ys.
exact IHxs.
intro.
rewrite eq_nat_sym.
rewrite H0.
specialize IHxs with (n :: quitar a ys).
split.
intro.
apply correctitud_andb in H1.
apply correctitud_andb.
split.
destruct H1.
apply permutacion_member with _ _ n in H2.
simpl in H2.
rewrite eq_nat_n_n in H2.
rewrite H2.
reflexivity.
simpl in H.
rewrite H0 in H.
destruct H1.
congruence.
intro.
apply correctitud_andb.
apply correctitud_andb in H1.
destruct H1.
split.
simpl in H.
rewrite H0 in H.
apply permutacion_member with _ _  a in H2.
simpl in H2.
rewrite eq_nat_n_n in H2.
rewrite H2.
reflexivity.
apply permutacion_member with _ _ a in H2.
simpl in H.
rewrite H0 in H.
rewrite H in H2.
simpl in H2.
rewrite eq_nat_n_n in H2.
inversion H2.
assert(true = true).
reflexivity.
pose(H4 H5).
congruence.
Qed.

Lemma primel_and_same_prod_then_eq: 
forall n xs ys, n = prodl xs -> primel xs = true -> primel ys = true -> prodl xs = prodl ys -> permutacion xs ys = true.
Proof.
induction n using (well_founded_ind lt_wf).
intros.
destruct xs.
destruct ys.
reflexivity.
assert(1 < prodl (n0 :: ys)).
apply prodl_gt_1.
exact H2.
simpl in H3.
simpl in H4.
omega.
destruct ys.
simpl in H3.
assert( 1 < prodl (n0 :: xs)).
apply prodl_gt_1.
exact H1.
simpl in H4.
omega.
case_eq(eq_nat n0 n1).
intro.
apply correctitud_eq_nat in H4.
rewrite H4.
simpl.
rewrite eq_nat_n_n.
simpl.
specialize H with (prodl xs) n0 n0.
assert(prodl xs < n).
  {
  rewrite H0.
  simpl.
 apply mult_lt.
 destruct xs.
 simpl.
 omega.
 assert(1 < prodl (n2 :: xs)).
 apply prodl_gt_1.
 assert(andb (primo n0) (primel (n2 :: xs)) = true).
 simpl.
 simpl in H1.
 exact H1.
 apply correctitud_andb in H5.
 destruct H5.
 exact H6.
 omega. 
 simpl in H1.
 apply correctitud_andb in H1.
 destruct H1.
 apply primo_implies_gt_1 in H1.
 exact H1. 
}
pose(H H5).
specialize e with xs ys.
assert(prodl xs = prodl ys).
{
  intros.
  simpl in H3.
  rewrite H4 in H3.
  assert(0 < n1).
  {
     simpl in H2.
    apply correctitud_andb in H2.
    destruct H2.
    apply primo_implies_gt_0 in H2.
    exact H2.
  }
  apply div_ambos_lados with _ _ n1 in H3.
  rewrite mult_conmutativa with n1 _ in H3.
  rewrite mult_conmutativa with n1 _ in H3.
  rewrite mult_div in H3.
  rewrite mult_div in H3.
  exact H3.
  exact H6.
  exact H6.
  exact H6.
}
assert(prodl xs = prodl xs).
reflexivity.
assert(primel xs = true).
{
  simpl in H1.
  apply correctitud_andb in H1.
  destruct H1.
  exact H8.
}
assert(primel ys = true).
{
  simpl in H2.
  apply correctitud_andb in H2.
  destruct H2.
  exact H9.
}
pose(e H7 H8 H9 H6).
exact e0.
intro.
apply correctitud_eq_nat_f in H4.
case_eq(lt_nat n0 n1).
intro.
apply primel_and_same_prod_then_eq_aux.
rewrite H0 in H.
exact H.
exact H1.
exact H2.
exact H3.
exact H4.
exact H5.
intro.
apply lt_nat_false in H5.
apply correctitud_leq_nat in H5.
assert(n1 < n0).
omega.
apply correctitud_lt_nat in H6.
assert(permutacion (n1 :: ys) (n0 :: xs) = true).
apply (primel_and_same_prod_then_eq_aux n1 n0 ys xs).
rewrite H0 in H.
rewrite <- H3.
exact H.
exact H2.
exact H1.
apply eq_sym.
exact H3.
apply neq_sym.
exact H4.
exact H6.
apply permutacion_conmutativa.
exact H7.
Qed.

Theorem unicidad_descomposicion: forall xs, forall m, 1< m -> (primel xs = true /\ prodl xs = m) -> permutacion xs (descomponer m) = true.
intros.
assert (primel (descomponer m) = true /\ prodl (descomponer m) = m).
apply correctitud_descomponer.
exact H.
destruct H1.
destruct H0.
apply primel_and_same_prod_then_eq with m.
apply eq_sym.
exact H3.
exact H0.
exact H1.
rewrite H2.
exact H3.
Qed.
