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


(** Esse arquivo contém as provas básicas acerca de divisibilidade em Z. *)
(** Começamos com a definição de divisibilidade, e provamos resultados *)
(** elementares acerca da definição, como reflexividade da relação, *)
(** transitividade, antissimetria do módulo, relação de ordem entre *)
(** dividendo e divisor, entre outros resultados. *)
(** Para isso utlizamos as bibliotecas importadas em missing.v e resultados *)
(** provados anteriormente acerca de propriedades com números inteiros*)
(** Note que na demonstração dos teoremas e lemmas abaixo geralmente *)
(** se faz uso de unfold divides, onde divides é a definição de *)
(** divisibilidade em Z. *)

Require Import missing.

(** Definição de divisibilidade*)
(** b | a se existe q em Z tal que a = b * q *)
Definition divides (b a : Z) := exists q : Z, a = (b * q).

(** Lemma 1 divisibilidade: 1 divide qualquer número inteiro *)
(** Para provar utilizamos a definição de divides e aplicamos *)
(** que 1 * n = n, para todo n inteiro *)
Lemma one_min_div_Z : forall (n : Z), (divides 1 n).
Proof.
  intros.
  unfold divides.
  exists n.
  symmetry.
  apply Z.mul_1_l.
Qed.

(** Lemma 2 divisibilidade: - 1 divide todo número inteiro *)
(** A prova desse lemma é semelhante à prova anterior *)
Lemma minus_one_min_div_Z : forall (n : Z),(divides (- 1) n).
Proof.
  intros.
  unfold divides.
  exists (- n).
  destruct n.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Lemma 3 divisibilidade: 0 é diviśivel por todo número inteiro *)
(** Mais uma vez destruímos divides e aplicamos n * 0 = 0 *)
Lemma zero_max_div : forall (n : Z), (divides n 0).
Proof.
  intros.
  red.
  exists 0.
  symmetry.
  apply Z.mul_0_r.
Qed.

(** Lemma 4 divisibilidade: 0 só divide ele mesmo *)
(** Esse lemma mostra que 0 não pode dividir nenhum número inteiro a *)
(** não ser ele mesmo. Usamos <-> pela equivalência das implicações *)
Lemma zero_not_divides : forall (a : Z), divides 0 a <-> a = 0.
Proof.
  intros.
  split.
  - unfold divides.
    intros.
    destruct H.
    simpl in H.
    apply H.
  - intros.
    unfold divides.
    exists 0.
    apply H.
Qed.

(** Lemma 5 divisibilidade: a relação de divisibilidade é reflexiva *)
(** Provamos então que a | a, para todo a inteiro, inclusive 0 *)
(** Note que a definição de divisibilidade grante a existência de *)
(** um q tal que 0 * q = 0, onde q = 0, mesmo que a definição da *)
(** operação divisão não esteja bem definida para o divisor 0 *)
Lemma divides_refl : forall (a : Z), (divides a a).
Proof.
  intros.
  red.
  exists 1.
  symmetry.
  apply Z.mul_1_r.
Qed.

(** Lemma 6 divisibilidade: a relação de divisibilidade é transitiva *)
(** Temos que se a | b e b | c -> a | c . Para provarmos,*)
(** assumimos as hipóteses anteriores e, fazendo a instanciação existencial *)
(** em x * x0, provamos o resultado usando a associatividade da multiplicação *)
Lemma divides_trans : forall (a b c : Z), (divides a b)->(divides b c)->(divides a c).
Proof.
  unfold divides.
  intros.
  destruct H.
  destruct H0.
  exists (x * x0).
  rewrite H in H0.
  rewrite H0.
  symmetry.
  apply Z.mul_assoc.
Qed.

(** Lemma 7 divisibilidade: a relação de divisibilidade é antissimétrica *)
(** em módulo, em Z. Ou seja, se a | b e b | a -> |a| = |b| . *)
(** Assim, provamos o resultado que a = b ou a = - b .*)
(** Para isso, destruímos a e b em seus construtores, 0, Z.pos e Z.neg, *)
(** analizando caso a caso e verificando que os casos batiam. *)
(** Como temos uma disjunção \/ , precisou-se quebrá-la também de modo a *)
(** analisar qual das situações se confirmavam, a = b ou a = -b .*)
(** Resultados auxiliares também foram necessários durante a prova.*)
(** Utilizou-se intuition para ajudar em determinadas partes da prova, *)
(** de modo a tornar relações mais visíveis e fazer inferências mais *)
(** automáticas. *)
Lemma divides_antisym_partially : forall (a b : Z), (divides a b) -> (divides b a) -> a = b \/ a = -b.
Proof.
  unfold divides.
  intros.
  destruct H.
  destruct H0.
  rewrite H.
  destruct a.
  - left.
    reflexivity.
  - destruct b.
    * inversion H0.
    * destruct x.
      {
         inversion H.
      }
      {
        destruct x0.
        - inversion H0.
        - rewrite H in H0.
          simpl in H0.
          assert (H1: forall (p : positive), Z.pos p <> 0).
          {
            intros p3. intuition. inversion H1.
          }
          assert (H2: Z.pos p1 * Z.pos p2 = 1).
          {
            apply mult_lemma6_Z with (n:=Z.pos p).
            apply H1.
            rewrite Z.mul_assoc. simpl. symmetry.
            rewrite Pos.mul_1_r.
            apply H0.
          }
          simpl in H2.
          apply Pos2Z.inj_pos in H2.
          apply Pos.mul_eq_1_l in H2.
          rewrite H2.
          left.
          symmetry.
          apply Z.mul_1_r.
        - inversion H0.
      }
      {
        inversion H.
      }
    * destruct x.
      {
         inversion H.
      }
      {
        inversion H.
      }
      {
        destruct x0.
        - inversion H0.
        - inversion H0.
        - simpl in H.
          rewrite H in H0.
          simpl in H0.
          assert (H1: forall (p : positive), Z.pos p <> 0).
          {
            intros p3. intuition. inversion H1.
          }
          assert (H2: Z.pos p1 * Z.pos p2 = 1).
          {
            apply mult_lemma6_Z with (n:=Z.pos p).
            apply H1.
            rewrite Z.mul_assoc. simpl. symmetry.
            rewrite Pos.mul_1_r.
            apply H0.
          }
          simpl in H2.
          apply Pos2Z.inj_pos in H2.
          apply Pos.mul_eq_1_l in H2.
          rewrite H2.
          right.
          simpl.
          symmetry.
          rewrite Pos.mul_1_r.
          reflexivity.
      }
  - destruct b.
    * inversion H0.
    * destruct x.
      {
         inversion H.
      }
      {
        inversion H.
      }
      {
        destruct x0.
        - inversion H0.
        - inversion H0.
        - rewrite H in H0.
          simpl in H0.
          assert (H1: forall (p : positive), Z.neg p <> 0).
          {
            intros p3. intuition. inversion H1.
          }
          assert (H2: Z.neg p1 * Z.neg p2 = 1).
          {
            apply mult_lemma6_Z with (n:=Z.neg p).
            apply H1.
            rewrite Z.mul_assoc. simpl. symmetry.
            rewrite Pos.mul_1_r.
            apply H0.
          }
          simpl in H2.
          apply Pos2Z.inj_pos in H2.
          apply Pos.mul_eq_1_l in H2.
          rewrite H2.
          right.
          simpl.
          symmetry.
          rewrite Pos.mul_1_r.
          reflexivity.
      }
    * destruct x.
      {
         inversion H.
      }
      {
        destruct x0.
        - inversion H0.
        - simpl in H.
          rewrite H in H0.
          simpl in H0.
          assert (H1: forall (p : positive), Z.neg p <> 0).
          {
            intros p3. intuition. inversion H1.
          }
          assert (H2: Z.neg p1 * Z.neg p2 = 1).
          {
            apply mult_lemma6_Z with (n:=Z.neg p).
            apply H1.
            rewrite Z.mul_assoc. simpl. symmetry.
            rewrite Pos.mul_1_r.
            apply H0.
          }
          simpl in H2.
          apply Pos2Z.inj_pos in H2.
          apply Pos.mul_eq_1_l in H2.
          rewrite H2.
          left.
          simpl.
          symmetry.
          rewrite Pos.mul_1_r.
          reflexivity.
        - inversion H0.
      }
      {
        inversion H.
      }
Qed.

(** Corolário 1 divisibilidade: para todo a != 1 e a != -1, ~(a | 1) *)
(** Ou seja, se a divide 1, então |a| = 1. Utilizamos resultados provados *)
(** em missing para ajudar na prova, analisando a conjunção para usarmos *)
(** as hipóteses corretas na prova. *)
Lemma non_div_1 : forall (a : Z), (a <> 1) /\ (a <> -1) -> ~ (divides a 1).
Proof.
  intros.
  red.
  intros.
  destruct H as [H1 Hm1].
  unfold divides in H0.
  destruct H0 as [q Hq].
  symmetry in Hq.
  apply mult_lemma5_Z in Hq.
  destruct Hq as [Hq1 | Hq2].
  - destruct Hq1 as [Hq1' Hq2']. apply H1. apply Hq1'.
  - destruct Hq2 as [Hq1' Hq2']. apply Hm1. apply Hq1'.
Qed.

(** Lemma 8 divisibilidade: se d | a e d | b, então d | (a+b) *)
(** Mostramos que se d divide dois inteiros, d divide a soma deles. *)
(** Para provar isso, usamos a deifinição de divides, bem como *)
(** instanciação existencial, para tirarmos as conclusões. O comando *)
(** ring aplica propriedades de anel em operações para tomar conclusões. *)
(** Como Z é um anel, o comando consegue tomar decisões com relações *)
(** apropriadas (+ e *, como associatividade, comutatividade, etc.). *)
Lemma divides_plus : forall (d a b : Z), (divides d a) -> (divides d b) -> (divides d (a + b)).
Proof.
  unfold divides.
  intros.
  destruct H.
  destruct H0.
  rewrite H.
  rewrite H0.
  exists (x + x0).
  ring.
Qed.

(** Lemma 9 divisibilidade: se d | a então d | a*b *)
(** Mostramos que se d divide um inteiro, d divide qualquer múltiplo dele. *)
(** Para provar isso, usamos a deifinição de divides, bem como *)
(** instanciação existencial, para tirarmos as conclusões O comando *)
(** ring aplica propriedades de anel em operações para tomar conclusões. *)
(** Como Z é um anel, o comando consegue tomar decisões com relações *)
(** apropriadas (+ e *, como associatividade, comutatividade, etc.). *)
Lemma divides_mult : forall (d a b : Z), (divides d a)->(divides d (a * b)).
Proof.
  unfold divides.
  intros.
  destruct H.
  rewrite H.
  exists (x * b).
  ring.
Qed.

(** Lemma 10 divisibilidade: se d | a e d | b, então d | (b-a) *)
(** Mostramos que se d divide dois inteiros, d divide a subtração deles. *)
(** Para provar isso, usamos a deifinição de divides, bem como *)
(** instanciação existencial, para tirarmos as conclusões. O comando *)
(** ring aplica propriedades de anel em operações para tomar conclusões. *)
(** Como Z é um anel, o comando consegue tomar decisões com relações *)
(** apropriadas (+ e *, como associatividade, comutatividade, etc.). *)
Lemma divides_minus : forall (d a b : Z), (divides d a)->(divides d b)->(divides d (b-a)).
Proof.
  unfold divides.
  intros.
  destruct H.
  destruct H0.
  rewrite H.
  rewrite H0.
  exists (x0 - x).
  ring.
Qed.

(** Lemma 11 divisibilidade: unicidade do quociente *)
(** b | a -> existe um único q -> a = b * q *)
(** Para provarmos a unicidade do quociente, usamos a definição de *)
(** divisibilidade e analizamos os casos da conjunção para provarmos *)
(** que os dois quocientes são iguais. *)
Lemma quocient_uniquiness : forall (a b : Z), 
  divides b a -> exists q : Z, a = b * q /\ exists q0 : Z, a = b * q0
    -> q = q0.
Proof.
  intros.
  unfold divides in H.
  destruct H.
  exists x.
  split.
  - apply H.
  - exists x.
    intros.
    reflexivity.
Qed.

(** Lemma 12 divisibilidade: se a > 0 e b > 0 e b | a -> q > 0, onde (a = b * q) *)
(** Esse lemma mostra que se a e b são positivos, o quociente também o é. *)
(** Para provarmos esse lemma, destruímos a e b em seus possíveis construtores *)
(** e analizamos os casos a partir daí, utilizando a definição de divisibilidade *)
(** e eliminando os casos impossíveis, com o uso de inversion na hipótese. *)
Lemma same_signal_pos : forall (a b : Z),
  a > 0 -> b > 0 -> divides b a -> exists q : Z, q > 0 -> a = b * q.
Proof.
  intros.
  unfold divides in H1.
  destruct H1.
  destruct a.
  - inversion H.
  - destruct b.
    + inversion H0.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * apply H1.
      * inversion H2.
    + inversion H0.
  - destruct b.
    + inversion H0.
    + inversion H.
    + inversion H0.
Qed.

(** Lemma 13 divisibilidade: se a < 0 e b < 0 e b | a -> q > 0, onde (a = b * q) *)
(** Esse lemma mostra que se a e b são negativos, o quociente é positivo. *)
(** Para provarmos esse lemma, destruímos a e b em seus possíveis construtores *)
(** e analizamos os casos a partir daí, utilizando a definição de divisibilidade *)
(** e eliminando os casos impossíveis, com o uso de inversion na hipótese. *)
Lemma same_signal_neg : forall (a b : Z),
  a < 0 -> b < 0 -> divides b a -> exists q : Z, q > 0 -> a = b * q.
Proof.
  intros.
  unfold divides in H1.
  destruct H1.
  destruct a.
  - inversion H.
  - destruct b.
    + inversion H0.
    + inversion H0.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * apply H1.
      * inversion H2.
  - destruct b.
    + inversion H0.
    + inversion H0.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * apply H1.
      * inversion H2.
Qed.

(** Lemma 14 divisibilidade: se ((a < 0 e b > 0) ou (a > 0 e b < 0)) e b | a -> q < 0, onde (a = b * q) *)
(** Esse lemma mostra que se a e b têm sinais contrários, o quociente é negativo. *)
(** Para provarmos esse lemma, destruímos a e b em seus possíveis construtores *)
(** e analizamos os casos a partir daí, utilizando a definição de divisibilidade *)
(** e eliminando os casos impossíveis, com o uso de inversion na hipótese. *)
Lemma dif_signal : forall (a b : Z),
  (a > 0 /\ b < 0) \/ (a < 0 /\ b > 0) -> divides b a -> exists q : Z, q < 0 -> a = b * q.
Proof.
  intros.
  unfold divides in H0.
  destruct H0.
  destruct H as [H1 | H2].
  - destruct H1.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * inversion H2.
      * apply H0.
  - destruct H2.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * inversion H2.
      * apply H0.
Qed.

(** Lemma 15 divisibilidade: se a | b e a | c, então a | b*x + c*y *)
(** para todo x, y em Z. Ou seja, a divide qualquer combinação linear *)
(** inteira em b e c. Para provarmos, utilizamos instanciação existencial *)
(** e resultados provados anteriormente, juntamente com a biblioteca *)
(** Zarith. *)
Lemma div_comb_linear : forall (a b c : Z), (divides a b) /\ (divides a c) -> 
  forall (x y : Z), (divides a (b * x + c * y) ).
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  unfold divides.
  rewrite H.
  rewrite H0.
  exists (x0 * x + x1 * y).
  rewrite Z.mul_add_distr_l.
  rewrite Zmult_assoc_reverse.
  rewrite Zmult_assoc_reverse.
  reflexivity.
Qed.

(** Lemma 16 divisibilidade: se a != 0 e b | a -> |a| >= |b| *)
(** Com isso, temos que se b | a, a é maior em módulo que b, *)
(** ou b é 0. Para provarmos, destruímos a e b em seus construtores *)
(** básicos, e utilizamos resultados provados anteriormente (em missing.v), *)
(** bem como a injetividade entre positives e os construtores Z.pos ou Z.neg. *)
Lemma divides_le : forall (a b : Z), (a<>0) -> (divides b a) -> (Z.abs b <= Z.abs a).
Proof.
  intros.
  destruct H0.
  destruct b.
  - destruct a.
    + intuition.
    + intuition.
    + intuition.
  - destruct a.
    + intuition.
    + simpl.
      destruct x.
      * intuition.
      * simpl in H0.
        rewrite H0.
        apply mult_cresc_positive.
      * inversion H0.
    + simpl.
      destruct x.
      * intuition.
      * simpl in H0.
        inversion H0.
      * simpl in H0.
        apply Pos2Z.inj_neg in H0.
        rewrite H0.
        apply mult_cresc_positive.
   - destruct a.
    + intuition.
    + simpl.
      destruct x.
      * intuition.
      * inversion H0.
      * rewrite H0.
        apply mult_cresc_positive.
    + simpl.
      destruct x.
      * intuition.
      * simpl in H0.
        apply Pos2Z.inj_neg in H0.
        rewrite H0.
        apply mult_cresc_positive.
      * inversion H0. 
Qed.

(** Lemma 17 divisibilidade: o lemma diz que é possível se computar q, tal que *)
(** a = b * q, se b | a. Conseguimos provar usando a definição de *)
(** piso em Z. Usando destruct e analisando os casos, conseguimos *)
(** provar para todo a e b em Z. *)
Lemma quo_dec : forall (a b : Z), (divides b a)-> {q : Z | a = b * q}.
Proof.
  intros.
  destruct a.
  - exists 0. symmetry. apply mult_symm_0.
  - destruct b.
    + exists 0.
      destruct H.
      inversion H.
    + unfold divides in H.
      exists (Z.pos p / Z.pos p0).
      destruct H.
      rewrite H.
      rewrite mult_comm_Z.
      rewrite Z_div_mult.
      * ring.
      * intuition.
    + unfold divides in H.
      exists (Z.pos p / Z.neg p0).
      destruct H.
      rewrite H.
      rewrite mult_comm_Z.
      rewrite Z.div_mul.
      * ring.
      * intuition.
        inversion H0.
  - destruct b.
    + exists 0.
      destruct H.
      inversion H.
    + unfold divides in H.
      exists (Z.neg p / Z.pos p0).
      destruct H.
      rewrite H.
      rewrite mult_comm_Z.
      rewrite Z_div_mult.
      * ring.
      * intuition.
    + unfold divides in H.
      exists (Z.neg p / Z.neg p0).
      destruct H.
      rewrite H.
      rewrite mult_comm_Z.
      rewrite Z.div_mul.
      * ring.
      * intuition.
        inversion H0.
Qed.

(** Definição do quociente em função da decidibilidade da divisão *)
Definition quo (a b : Z) (H:(divides b a)) := let (q,_):=(quo_dec a b H) in q.