(* Copyright (C) 2005-2008 Sebastien Briais *)
(* http://lamp.epfl.ch/~sbriais/ *)

(* This library is free software; you can redistribute it and/or modify *)
(* it under the terms of the GNU Lesser General Public License as *)
(* published by the Free Software Foundation; either version 2.1 of the *)
(* License, or (at your option) any later version. *)

(* This library is distributed in the hope that it will be useful, but *)
(* WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA *)
(* 02110-1301 USA *)

(** Aqui está o primeiro arquivo do projeto, no qual começamos *)
(** a transpor os resultdos desta biblioteca sobre números naturais *)
(** para números inteiros. No decorrer das provas, algumas já existiam *)
(** na biblioteca em coq, mas provamos alguns resultados mesmo assim *)
(** para ter mais intuição de provas e também podermos transpor resultados *)
(** a nossa maneira para podermos aplicar em resultados mais complexos. *)
(** Na parte superior, mantivemos o header com direitos autorais, de maneira *)
(** a garantir a origem da biblioteca original. *)

Require Export ZArith.
Require Export Arith.
Require Export ArithRing.
Require Export Omega.

Unset Standard Proposition Elimination Names.

Open Scope positive_scope.

(** Os teoremas provados nesse arquivo sobre numeros positivos e inteiros servem de base para as provas dos outros arquivos. 
Algumas provas se tentam mapear os positivos para naturais pois os naturais tem mais coisas provadas sobre eles e também são mais simples de trabalhar*)

(** Essa prova so converte o scolpo de positivos para naturais e aproveita a prova ja existente para naturais*)
Lemma add_cresc_positive : forall (n m : positive), n <= n + m.
Proof.
  intros.
  rewrite Pos2Nat.inj_le, Pos2Nat.inj_add.
  apply le_plus_l.
Qed.

Open Scope nat_scope.

(** Prova que a conversão de um positivo para natural da um natural maior ou igual a 1
  Para provar realizamos uma indução no n. utilizamos:
  - todo natural é maior ou igual a 0
  - <= é transitiva
  - um natural é sempre menor ou igual a soma dele com outro número
*)
Lemma to_nat_pos : forall (n : positive), 1 <= Pos.to_nat n.
Proof.
  induction n.
  - rewrite Pos.xI_succ_xO, Pos2Nat.inj_succ.
    apply Peano.le_n_S, Peano.le_0_n.
  - rewrite Pos2Nat.inj_xO. simpl.
    apply Nat.le_trans with (m := Pos.to_nat n).
    * apply IHn.
    * apply Nat.le_add_r.
  - rewrite Pos2Nat.inj_1. 
    apply Peano.le_n_S, Peano.le_0_n.
Qed.

(** Prova equivalente a prova acima para generalização existencial.
  Destruimos os casos e com a prova acima provamos que o consrutor 0 é impossivel logo precisa existir um S m*)
Lemma to_nat_pos_S_n : forall (n : positive), exists m,  Pos.to_nat n = S m.
Proof.
  intros n.
  destruct (Pos.to_nat n) eqn:H.
  - assert (H1: 1 <= Pos.to_nat n). {apply to_nat_pos. } rewrite H in H1. inversion H1.
  - exists n0. reflexivity.
Qed.

(** Prova de que a multiplicação de positivos é sempre crescente
  Convertemos os numeros para naturais da forma S m
  Transformamos a multiplicação em soma e usamos a prova de que (x <= x + ?)*)
Lemma mult_cresc_positive : forall (n m :positive), (n <= n * m)%positive.
Proof.
  intros.
  rewrite Pos2Nat.inj_le, Pos2Nat.inj_mul.
  assert (H1: exists n' , Pos.to_nat n = S n'). apply to_nat_pos_S_n.
  assert (H2: exists m' , Pos.to_nat m = S m'). apply to_nat_pos_S_n.
  inversion H1.
  inversion H2.
  rewrite H, H0.
  rewrite Nat.mul_comm.
  simpl.
  apply le_n_S, le_plus_l.
Qed.

(** Prova que multiplicação é estritamente crescente se o multiplicador é maior que 1
  Converter para naturais da forma S m
  destrinchar a multiplicação como em soma, adicionar um S _ como m > 1 e usando comutatividade e acossiatividade e  termina a prova usando que (x <= x + ?)*)
Lemma mult_cresc_positive_gt_1 : forall (n m : positive), ((m > 1) -> n < n * m)%positive.
Proof.
  intros.
  rewrite Pos2Nat.inj_lt, Pos2Nat.inj_mul.
  rewrite Pos2Nat.inj_gt, Pos2Nat.inj_1 in H.
  assert (H1: exists n' , Pos.to_nat n = S n'). apply to_nat_pos_S_n.
  assert (H2: exists m' , Pos.to_nat m = S m'). apply to_nat_pos_S_n.
  inversion H1.
  inversion H2.
  rewrite H0, H3.
  rewrite H3 in H.
  apply gt_S_n, gt_le_S in H.
  destruct x0.
  - inversion H.
  - simpl. 
    apply lt_n_S, le_lt_n_Sm. 
    rewrite Nat.mul_comm. 
    simpl.
    rewrite plus_comm, plus_assoc_reverse. 
    apply le_plus_l.
Qed.

Open Scope positive_scope.

(** Prova que 1 é o fator nulo da multiplicação 
  Destruir m e provar que se m é da forma m~0 ou m~1 é contradição logo m precisa ser 1*)
Lemma mult_positive_l : forall (n m : positive), (n = n * m -> m = 1)%positive.
Proof.
  intros.
  destruct m.
  - apply Pos.eqb_eq in H.
    rewrite Pos.xI_succ_xO in H. 
    rewrite Pos.mul_succ_r in H.
    assert (H1: n <> n + n*m~0). { apply not_eq_sym. rewrite Pos.add_comm. apply Pos.add_no_neutral. }
    apply Pos.eqb_neq in H1.
    rewrite H in H1. inversion H1.
  - assert(H1: m~0 > 1). {
      rewrite <- Pos.add_diag.
      rewrite Pos2Nat.inj_gt.
      rewrite Pos2Nat.inj_add.
      rewrite Pos2Nat.inj_1.
      assert (H2: exists m' , Pos.to_nat m = S m'). apply to_nat_pos_S_n.
      inversion H2.
      rewrite H0. simpl. rewrite plus_comm. simpl. auto with arith.
    }
    
    assert (H2: n < n * m~0). { 
      apply mult_cresc_positive_gt_1, H1.
    }
    symmetry  in H.
    rewrite H in H2. 
    apply Pos.lt_irrefl in H2. inversion H2.
  - reflexivity.
Qed.

Open Scope Z_scope.

(** Provar fator nulo da multiplicação 0. Já existia na biblioteca, mas *)
(** provamos para renomear o lemma e ficar mais amigável para usarmos *)
Lemma mult_symm_0 : forall (m : Z), m * 0 = 0.
Proof.
  apply Z.mul_0_r.
Qed.

(** Provar fator comutatividade em Z. Já existia na biblioteca, mas *)
(** provamos para renomear o lemma e ficar mais amigável para usarmos *)
Lemma mult_comm_Z : forall (n m : Z), n * m = m * n.
Proof.
  apply Z.mul_comm.
Qed. 

(** Lemma 1 auxiliares: Prova que se, em Z, se n > 0 e m > 0 -> n <= n * m. *)
(** Utilizamos resultados anteriores para provarmos essa propriedade *)
Lemma mult_lemma1_Z : forall (n m : Z), (n > 0) -> (m > 0) -> (n <= n*m).
Proof.
  intros.
  rewrite mult_comm_Z. 
  induction m.
  - inversion H0.
  - destruct n.
     + inversion H.
     + rewrite mult_comm_Z. simpl. apply mult_cresc_positive.
     + inversion H.
  - inversion H0.
Qed.

(** Lemma 2 auxiliares: Prova que se, em Z, se n*m = 0 -> um dos dois é 0. *)
(** Utilizamos resultados anteriores para provarmos essa propriedade, bem *)
(** como o uso de tauto para tautologias encontradas. *)
Lemma mult_lemma2_Z : forall (n m : Z),(n*m = 0) -> (n=0)\/(m=0).
Proof.  
  intros.
  induction n.
  - tauto.
  - destruct m.
    + tauto.
    + inversion H.
    + inversion H.
  - destruct m.
    + tauto.
    + inversion H.
    + inversion H.
Qed.

(** Lemma 3 auxiliares: Prova que se, em Z, se n > 0 e m > 1 -> n < n * m, *)
(** ou seja, estritamente maior. *)
(** Utilizamos resultados anteriores para provarmos essa propriedade, *)
(** destruindo n e m e estudando os casos. *)
Lemma mult_lemma3_Z : forall (n m : Z),(n > 0)->(m > 1)->(n < n*m).
Proof.
  intros.
  induction n.
  - inversion H.
  - destruct m.
    + inversion H0.
    + simpl. apply mult_cresc_positive_gt_1. apply H0.
    + inversion H0.
  - inversion H.
Qed.

(** Lemma 4 auxiliares: n = n*m -> n = 0 \/ m = 1 .*)
(** Utilizamos destruct para estudarmos os casos, bem como o auxílio *)
(** de resultados anteriores. *)
Lemma mult_lemma4_Z : forall (n m : Z), n = n*m -> n = 0 \/ m = 1.
Proof.
  intros n m H.
  destruct n.
  + tauto.
  + right.
    destruct m.
    - inversion H.
    - simpl in H. inversion H. apply mult_positive_l in H1. rewrite H1. reflexivity.
    - inversion H.
  + right.
    destruct m.
    - inversion H.
    - simpl in H. inversion H. apply mult_positive_l in H1. rewrite H1. reflexivity.
    - inversion H.
Qed.

(** Lemma 5 auxiliares: n*m = 1 -> ambos são 1 ou -1 .*)
(** Utilizamos destruct para estudarmos os casos, bem como o auxílio *)
(** de resultados anteriores e da biblioteca de coq. *)
Lemma mult_lemma5_Z : forall (n m : Z),((n * m) =1)-> ((n=1)/\(m=1)) \/ ((n=-1)/\(m=-1)).
Proof.
  intros n.
  induction n.
  + intros m H. inversion H.
  + left.
    split.
    - destruct m.
      * inversion H.
      * simpl in H. 
        inversion H. 
        apply Pos.mul_eq_1_r in H1.
        rewrite H1.
        symmetry. 
        rewrite Pos.mul_comm. 
        rewrite Pos.mul_1_l.
        reflexivity.
      * inversion H.
    - destruct m.
      * inversion H.
      * simpl in H. inversion H.
        apply Pos.mul_eq_1_r in H1.
        rewrite H.
        rewrite H1.
        reflexivity.
      * simpl in H. inversion H.
    + right. split.
        - destruct m.
          * inversion H.
          * inversion H.
          * simpl in H. inversion H. 
            apply Pos.mul_eq_1_l in H1.
            rewrite H1. simpl. symmetry. inversion H.
            apply Pos.mul_eq_1_r in H2.
            rewrite H1. simpl. reflexivity.
        - destruct m.
          * inversion H.
          * inversion H.
          * simpl in H. inversion H. 
            apply Pos.mul_eq_1_l in H1.
            rewrite H1. simpl. symmetry. inversion H.
            apply Pos.mul_eq_1_r in H2. reflexivity.
Qed.

(** Lemma 6 auxiliares: y - y = 0 .*)
(** Utilizamos destruct para estudarmos os casos, bem como o auxílio *)
(** da biblioteca de coq. *)
Lemma minus_same_number_Z : forall (y : Z), y - y = 0.
Proof.
  intros y.
  destruct y.
  + reflexivity.
  + simpl. apply Z.pos_sub_diag.
  + simpl. apply Z.pos_sub_diag.
Qed.

(** Lemma 7 auxiliares: x + y - y = x .*)
(** Utilizamos destruct para estudarmos os casos, bem como o auxílio *)
(** da biblioteca de coq e resultados anteriores. *)
Lemma plus_minus_lemma1 : forall (y x : Z),(x+y-y=x).
Proof.
  intros.
  induction x.
  + simpl. apply minus_same_number_Z.
  + apply Z.add_simpl_r.
  + apply Z.add_simpl_r.
Qed.

(** Lemma 8 auxiliares: a*n-n = (a-1)*n .*)
(** Utilizamos destruct para estudarmos os casos, bem como o auxílio *)
(** da biblioteca de coq. *)
Lemma mult_minus_lemma1_Z : forall (a n : Z),a*n-n = (a-1)*n.
Proof.
  intros.
  symmetry.
  rewrite Z.mul_sub_distr_r.
  assert (H: 1 * n = n).
  {
    destruct n.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

(** Lemma 9 auxiliares: Se n != 0 e (n*a=n*b) -> (a=b) .*)
(** Utilizamos destruct para estudarmos os casos, bem como o auxílio *)
(** da biblioteca de coq. Utilizamos resultados anteriores, injetividade *)
(** entre positives e Z.pos ou Z.neg. *)
Lemma mult_lemma6_Z : forall (a b n : Z),(n <> 0)->(n*a=n*b)->(a=b).
Proof.
  intros.
  induction a.
  - destruct b.
    + reflexivity.
    + rewrite mult_symm_0 in H0.
      symmetry in H0.
      apply mult_lemma2_Z in H0. 
      destruct H0 as [Hn | Hz].
        * unfold not in H. apply H in Hn. inversion Hn.
        * inversion Hz.
    + rewrite mult_symm_0 in H0.
      symmetry in H0.
      apply mult_lemma2_Z in H0. 
      destruct H0 as [Hn | Hz].
        * unfold not in H. apply H in Hn. inversion Hn.
        * inversion Hz.
  - destruct b.
    + rewrite mult_symm_0 in H0.
      apply mult_lemma2_Z in H0. 
      destruct H0 as [Hn | Hz].
        * unfold not in H. apply H in Hn. inversion Hn.
        * inversion Hz.
    + destruct n.
      * rewrite Z.mul_0_l in H0.
        symmetry in H0.
        rewrite Z.mul_0_l in H0.
        unfold not in H.
        apply H in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
        apply Pos.mul_reg_l in H2.
        apply Zpos_eq in H2.
        apply H2.
      * simpl in H0.
        inversion H0.
        apply Pos.mul_reg_l in H2.
        apply Zpos_eq in H2.
        apply H2.
    + destruct n.
      * rewrite Z.mul_0_l in H0.
        symmetry in H0.
        rewrite Z.mul_0_l in H0.
        unfold not in H.
        apply H in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
  - destruct b.
    + rewrite mult_symm_0 in H0.
      apply mult_lemma2_Z in H0. 
      destruct H0 as [Hn | Hz].
        * unfold not in H. apply H in Hn. inversion Hn.
        * inversion Hz.
    + destruct n.
      * rewrite Z.mul_0_l in H0.
        symmetry in H0.
        rewrite Z.mul_0_l in H0.
        unfold not in H.
        apply H in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
    + destruct n.
      * rewrite Z.mul_0_l in H0.
        symmetry in H0.
        rewrite Z.mul_0_l in H0.
        unfold not in H.
        apply H in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
        apply Pos.mul_reg_l in H2.
        apply Pos2Z.inj_neg_iff in H2.
        apply H2.
      * simpl in H0.
        inversion H0.
        apply Pos.mul_reg_l in H2.
        apply Pos2Z.inj_neg_iff in H2.
        apply H2.
Qed.

(** Lemma 10 auxiliares: - x - y = - (x + y) .*)
(** Utilizamos destruct para estudarmos os casos, bem como o auxílio *)
(** da biblioteca de coq. Resultado já provado na biblioteca, mas usamos *)
(** da oportunidade para deixarmos mais explícito para usarmos. *)
Lemma minus_distributive_Z : forall (x y z : Z), - x - y = - (x + y).
Proof.
  intros.
  destruct x.
  + simpl. reflexivity.
  + destruct y.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. symmetry. apply Z.pos_sub_opp.
  + destruct y.
    * simpl. reflexivity.
    * simpl. symmetry. apply Z.pos_sub_opp.
    * simpl. reflexivity.
Qed.

(** Lemma 11 auxiliares:  x - y - z = x - (y + z) .*)
(** Utilizamos destruct para estudarmos os casos, bem como o auxílio *)
(** da biblioteca de coq. Utilizamos injetividade aqui também. *)
Lemma minus_minus_lemma2_Z : forall (x y z : Z), (x - y - z)=(x - (y + z)).
Proof.  
  intros.
  induction x.
  - simpl. destruct y.
    + simpl. reflexivity.
    + destruct z.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. symmetry. apply Z.pos_sub_opp.
    + destruct z.
      * simpl. reflexivity.
      * simpl. symmetry. apply Z.pos_sub_opp.
      * simpl. reflexivity.
  - destruct y.
    + simpl. reflexivity.
    + destruct z.
      * simpl. rewrite Z.sub_0_r. reflexivity.
      * symmetry. apply Z.sub_add_distr.
      * symmetry. apply Z.sub_add_distr.
    + destruct z.
      * simpl. reflexivity.
      * symmetry. apply Z.sub_add_distr.
      * symmetry. apply Z.sub_add_distr.
  - destruct y.
    + reflexivity.
    + destruct z.
      * simpl. reflexivity.
      * simpl. apply Pos2Z.inj_neg_iff.
        symmetry.
        apply Pos.add_assoc.
      * symmetry. apply Z.sub_add_distr.
    + destruct z.
      * simpl. rewrite Z.sub_0_r. reflexivity.
      * symmetry. apply Z.sub_add_distr.
      * symmetry. apply Z.sub_add_distr.
Qed.

(** Lemma 12 auxiliares: x * y * (z * t) = z * (x * y * t) .*)
(** Utilizamos ring para aplicarmos propriedades do anel dos inteiros. *)
Lemma mult_lemma7_Z : forall (x y z t : Z), x * y * (z * t) = z * (x * y * t).
Proof.
  intros.
  ring.
Qed.

(** Lemma 13 auxiliares: (a < b) -> (0 < b - a) .*)
(** Utilizamos omega para aplicarmos propriedades dos inteiros e *)
(** automatizar a prova. *)
Lemma minus_lt_lemma1 : forall (b a : Z),(a < b) -> (0 < b - a).
Proof.
  intros.
  omega.
Qed.

(** Lemma 14 auxiliares: Z.pos p != 0 .*)
(** Prova bem simples, utlizando implicação em falso. *)
Lemma different_from_zero_pos : forall (p : positive), Z.pos p <> 0.
Proof.
  intros.
  unfold not.
  intros H.
  inversion H.
Qed.

(** Lemma 15 auxiliares: Z.neg p != 0 .*)
(** Prova bem simples, utlizando implicação em falso. *)
Lemma different_from_zero_neg : forall (p : positive), Z.neg p <> 0.
Proof.
  intros.
  unfold not.
  intros H.
  inversion H.
Qed.