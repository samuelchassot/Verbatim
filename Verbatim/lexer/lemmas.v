Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.NatInt.NZOrder.

From Verbatim Require Import ltac.
From Verbatim Require Import state.
From Verbatim Require Import lexer.impl.

Module LemmasFn (Import ST : state.T).

  Import ST.Defs.
  Import ST.Ty.
  Module IMPL := ImplFn ST.
  Import IMPL.
  Import MatchSpec.

  Lemma lex'_eq_body :
    forall rules code (Ha : Acc lt (length code)),
      (lex' rules code Ha =
       (match max_of_prefs (max_prefs code rules) as mpref'
              return max_of_prefs (max_prefs code rules) = mpref' -> _
        with
        | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
        | (_, Some ([], _)) => fun _ => ([], code) (* Code cannot be processed further *)
        | (label, Some (ph :: pt, suffix)) =>
          fun Heq =>
            match (lex' rules suffix
                        (acc_recursive_call _ _ _ _ _ _ Ha Heq))
            with
            | (lexemes, rest) => (((label, ph :: pt) :: lexemes), rest)
            end
        end eq_refl)).
  Proof.
    intros rules code Ha. unfold lex'. destruct Ha. auto.
  Qed.

  Lemma lex'_cases_backward :
    forall (rules : list sRule)
      (code : String)
      (Ha : Acc lt (length code))
      (pr : Label * option (Prefix * Suffix))
      (res : list Token * String)
      (Heq : max_of_prefs (max_prefs code rules) = pr),
      match pr as mpref' return max_of_prefs (max_prefs code rules) = mpref' -> _ with
      | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
      | (_, Some ([], _)) => fun _ => ([], code) (* Code cannot be processed further *)
      | (label, Some (h :: t, suffix)) =>
        fun Heq =>
          match (lex' rules suffix
                      (acc_recursive_call _ _ _ _ _ _ Ha Heq))
          with
          | (lexemes, rest) => (((label, h :: t) :: lexemes), rest)
          end
      end Heq = res
      -> match res with
        | ([], code') =>
          code' = code
          /\ (snd pr = None
             \/ exists suf, snd pr = Some ([], suf))
        | ((label, prefix) :: lexemes, rest) =>
          exists h t suffix (Heq' : max_of_prefs (max_prefs code rules) = (label, Some (h :: t, suffix))),
          lex' rules suffix (acc_recursive_call _ _ _ _ _ _ Ha Heq') = (lexemes, rest)
          /\ h :: t = prefix
        end.
  Proof.
    intros rules code Ha pr res Heq.
    repeat dm; intros; subst; simpl in *; try congruence.
    - split; inv H; eauto.
    - inv H. exists s0. exists p1. exists s. exists Heq. split. apply E3. reflexivity.
    - split; inv H; eauto.
  Qed.

  Lemma lex'_cases :
    forall rules code Ha res,
      lex' rules code Ha = res
      -> match res with
        | ([], code') =>
          code' = code
          /\ (snd (max_of_prefs (max_prefs code rules)) = None
             \/ exists suf, snd (max_of_prefs (max_prefs code rules)) = Some ([], suf))
        | ((label, prefix) :: lexemes, rest) =>
          exists h t suffix (Heq' : max_of_prefs (max_prefs code rules) = (label, Some (h :: t, suffix))),
          lex' rules suffix (acc_recursive_call _ _ _ _ _ _ Ha Heq') = (lexemes, rest)
          /\ h :: t = prefix
        end.
  Proof.
    intros rules code Ha res Heq; subst.
    rewrite lex'_eq_body.
    eapply lex'_cases_backward; eauto.
  Qed.

  Lemma nil_is_prefix : forall(xs : String),
      [] ++_= xs.
  Proof.
    intros xs. apply pref_def. exists xs. reflexivity.
  Qed.

  Lemma app_head_prefix : forall(xs ys : String),
      xs ++_= xs ++ ys.
  Proof.
    intros xs ys. apply pref_def. exists ys. reflexivity.
  Qed.

  Lemma cons_prefix : forall(x y : Sigma) (xs ys : String),
      x :: xs ++_= y :: ys <-> x = y /\ xs ++_= ys.
  Proof.
    intros x y xs ys. split; intros H.
    {
      inv H. destruct H1.
      injection H. intros I1 I2. split; subst.
      - reflexivity.
      - apply app_head_prefix.
    }
    {
      destruct H. inv H0. destruct H1.
      apply pref_def. exists x. rewrite <- H. reflexivity.
    }
  Qed.

  Lemma self_prefix : forall(p : String), p ++_= p.
  Proof.
    intros p. apply pref_def. exists []. apply nil_right.
  Qed.

  Lemma eq_len_eq_pref : forall(x s p : String),
      length p = length s
      -> s ++_= x
      -> p ++_= x
      -> s = p.
  Proof.
    induction x; intros s p Heq Hs Hp .
    - inv Hs. inv Hp. destruct H0. destruct H1.
      apply app_eq_nil in H. destruct H.
      apply app_eq_nil in H0. destruct H0.
      subst. reflexivity.
    - destruct s; destruct p.
      + reflexivity.
      + simpl in Heq. discriminate.
      + simpl in Heq. discriminate.
      + apply cons_prefix in Hs. apply cons_prefix in Hp.
        destruct Hs. destruct Hp. subst.
        assert (length p = length s0).
        { simpl in Heq. omega. }
        apply IHx in H.
        * rewrite H. reflexivity.
        * apply H0.
        * apply H2.
  Qed.
       
  Lemma transition_list_hop : forall bs a fsm,
      transition a (transition_list bs fsm)
      = transition_list (bs ++ [a]) fsm.
  Proof.
    induction bs; intros; auto.
    simpl. apply IHbs.
  Qed.

  
  Lemma deriv_list_hop : forall bs a fsm,
      derivative a (derivative_list bs fsm)
      = derivative_list (bs ++ [a]) fsm.
  Proof.
    induction bs; intros; auto.
    simpl. apply IHbs.
  Qed.


  Lemma transition_cons : forall bs a fsm,
      transition_list (a :: bs) fsm = transition_list bs (transition a fsm).
  Proof.
    auto.
  Qed.

  
  Lemma mpref_cons : forall code px sx fsm a,
      max_pref_fn code (transition a fsm) = Some (px, sx)
      <-> max_pref_fn (a :: code) fsm = Some (a :: px, sx).
  Proof.
    intros. simpl. repeat dm; split; intros; try(discriminate).
    - injection H; intros; subst; reflexivity.
    - injection H; intros; subst; reflexivity.
    - clear H. exfalso.
      destruct code.
      + simpl in E. dm; try(discriminate).
      + simpl in E. repeat dm; try(discriminate).
  Qed.

  Lemma accepting_dt : forall b e,
      accepting (transition b (init_state e)) =
      accepting (init_state (derivative b e)).
  Proof.
    intros. destruct (accepting (transition b (init_state e))) eqn:E.
    - rewrite accepts_nil in E. rewrite accepts_transition in E.
      symmetry in E. rewrite accepts_matches in E. apply der_match in E.
      rewrite <- accepts_matches in E. rewrite <- accepts_nil in E. auto.
    - symmetry. rewrite false_not_true in *. intros C. destruct E.
      rewrite accepts_nil. rewrite accepts_transition.
      symmetry. rewrite accepts_matches. apply der_match.
      rewrite <- accepts_matches. rewrite <- accepts_nil. auto.
  Qed.

  Lemma dbl_trans_lst : forall a b e,
    transition a (transition b (init_state e))
    = transition_list [b; a] (init_state e).
  Proof. auto. Qed.

  Lemma dbl_deriv_lst : forall s0 a0 e,
      derivative s0 (derivative a0 e)
      = derivative_list [a0; s0] e.
  Proof. auto. Qed.

  (* ow *)
  Lemma mpref_dt_list : forall code bs e a,
      max_pref_fn code (transition a (init_state e))
      = max_pref_fn code (init_state (derivative a e))
      /\
      max_pref_fn code (transition_list bs (init_state e)) =
      max_pref_fn code (init_state (derivative_list bs e)).
  Proof.
    induction code; induction bs; intros.
    - split; auto. simpl. repeat dm.
      + rewrite accepting_dt in *. rewrite E in E0. discriminate.
      + rewrite accepting_dt in *. rewrite E in E0. discriminate.
    - split.
      + simpl. repeat dm.
        * rewrite accepting_dt in *. rewrite E in E0. discriminate.
        * rewrite accepting_dt in *. rewrite E in E0. discriminate.
      + simpl. repeat dm.
        * rewrite <- transition_cons in E.
          rewrite <- derivative_list_cons in *.
          rewrite accepting_dt_list in *. rewrite E in *. discriminate.
        * rewrite <- transition_cons in E.
          rewrite <- derivative_list_cons in *.
          rewrite accepting_dt_list in *. rewrite E in *. discriminate.
    - assert(IHcode0 : forall (e : regex) (a : Sigma),
           max_pref_fn code (transition a (init_state e)) =
           max_pref_fn code (init_state (derivative a e))).
      { intros. specialize (IHcode []). apply IHcode. }
      assert(IHcode1 : forall (bs : list Sigma) (e : regex),
           max_pref_fn code (transition_list bs (init_state e)) =
           max_pref_fn code (init_state (derivative_list bs e))).
      { intros. specialize (IHcode bs e0 a). apply IHcode. }
      clear IHcode.
      split.
      + destruct (max_pref_fn (a :: code) (transition a0 (init_state e))) eqn:E.
        * destruct p. symmetry.
          destruct p.
          -- simpl in *. repeat dm; try(discriminate).
             ++ rewrite IHcode0 in E3.
                rewrite dbl_trans_lst in E0.
                rewrite dbl_deriv_lst in E3.
                rewrite IHcode1 in *. rewrite E3 in *. discriminate.
             ++ exfalso.
                clear IHcode0 IHcode1 E0 E2 E E3.
                rewrite dbl_trans_lst in *.
                assert(
                    accepting (transition a (init_state (derivative a0 e)))
                    = accepting (transition_list [a] (init_state (derivative a0 e)))
                  ).
                { auto. }
                rewrite H in *. clear H.
                rewrite accepting_dt_list in *.
                simpl in *. rewrite E1 in *. discriminate.
             ++ rewrite accepting_dt in *. rewrite E5 in *. discriminate.
          -- assert(a = s0).
             {
               simpl in E.
               repeat dm; try(discriminate);
                 injection E; intros; subst; auto.
             }
             subst.
             rewrite <- mpref_cons. rewrite <- mpref_cons in E.
             rewrite IHcode0.
             rewrite dbl_trans_lst in *.
             rewrite dbl_deriv_lst in *.
             rewrite <- IHcode1. auto.
        * simpl in *. repeat dm; try(discriminate).
          -- clear E. rewrite IHcode0 in E3. 
             rewrite dbl_trans_lst in E0.
             rewrite dbl_deriv_lst in E3.
             rewrite IHcode1 in *. rewrite E3 in *. discriminate.
          -- rewrite accepting_dt in E4.
             rewrite dbl_trans_lst in *.
             rewrite dbl_deriv_lst in *.
             rewrite accepting_dt_list in *.
             rewrite E4 in *. discriminate.
          -- rewrite accepting_dt in *. rewrite E5 in *. discriminate.       
      + unfold transition_list. unfold derivative_list. auto.
    - assert(IHcode0 : forall (e : regex) (a : Sigma),
           max_pref_fn code (transition a (init_state e)) =
           max_pref_fn code (init_state (derivative a e))).
      { intros. specialize (IHcode []). apply IHcode. }
      assert(IHcode1 : forall (bs : list Sigma) (e : regex),
           max_pref_fn code (transition_list bs (init_state e)) =
           max_pref_fn code (init_state (derivative_list bs e))).
      { intros. specialize (IHcode bs0 e0 a). apply IHcode. }
      clear IHcode.
      assert(IHbs0 : forall (e : regex) (a0 : Sigma),
         max_pref_fn (a :: code) (transition a0 (init_state e)) =
         max_pref_fn (a :: code) (init_state (derivative a0 e))).
      { intros. apply IHbs. }
      assert(IHbs1 : forall (e : regex) (a0 : Sigma),
         max_pref_fn (a :: code) (transition_list bs (init_state e)) =
         max_pref_fn (a :: code) (init_state (derivative_list bs e))).
      { intros. apply IHbs. apply a. }
      clear IHbs.
      split.
      + auto.
      + destruct (max_pref_fn (a :: code) (transition_list (a0 :: bs) (init_state e))) eqn:E.
        * destruct p. destruct p.
          -- simpl in E. simpl. repeat dm; try(discriminate).
             ++ rewrite IHcode0 in *.
                rewrite <- transition_cons in *.
                rewrite <- derivative_list_cons in *.
                rewrite transition_list_hop in *.
                rewrite deriv_list_hop in *.
                rewrite IHcode1 in *. rewrite E3 in *. discriminate.
             ++ rewrite accepting_dt in *.
                rewrite <- transition_cons in *.
                rewrite <- derivative_list_cons in *.
                rewrite transition_list_hop in *.
                rewrite deriv_list_hop in *.
                rewrite IHcode1 in *.
                rewrite accepting_dt_list in *. rewrite E4 in *. discriminate.
             ++ rewrite <- transition_cons in *.
                rewrite <- derivative_list_cons in *.
                rewrite accepting_dt_list in *. rewrite E5 in *. discriminate.
          -- simpl in E. simpl.
             repeat dm; try(discriminate);
               try(injection E; intros; subst;
                rewrite IHcode0 in *; rewrite transition_list_hop in E0;
                rewrite <- transition_cons in E0; rewrite IHcode1 in E0;
                rewrite derivative_list_cons in E0; rewrite <- deriv_list_hop in E0;
                rewrite E0 in E2; discriminate);
               try(injection E; intros; subst;
                rewrite IHcode0 in *; rewrite transition_list_hop in E0;
                rewrite <- transition_cons in E0; rewrite IHcode1 in E0;
                rewrite derivative_list_cons in E0; rewrite <- deriv_list_hop in E0;
                rewrite E0 in E2; injection E2; intros; subst; reflexivity).
             ++ clear E0 E2 E E4.
                rewrite accepting_dt in E3.
                rewrite transition_list_hop in *.
                rewrite deriv_list_hop in *.
                rewrite <- transition_cons in *.
                rewrite <- derivative_list_cons in *.
                rewrite accepting_dt_list in *. rewrite E3 in *. discriminate.             
             ++ clear E0 E2 E E4.
                rewrite accepting_dt in E3.
                rewrite transition_list_hop in *.
                rewrite deriv_list_hop in *.
                rewrite <- transition_cons in *.
                rewrite <- derivative_list_cons in *.
                rewrite accepting_dt_list in *. rewrite E3 in *. discriminate.                
        * simpl in E. simpl. repeat dm; try(discriminate).
          -- rewrite IHcode0 in *; rewrite transition_list_hop in E0;
               rewrite <- transition_cons in E0; rewrite IHcode1 in E0;
                 rewrite derivative_list_cons in E0; rewrite <- deriv_list_hop in E0.
             rewrite E0 in E3. discriminate.
          -- clear E0 E3 E E2.
                rewrite accepting_dt in E4.
                rewrite transition_list_hop in *.
                rewrite deriv_list_hop in *.
                rewrite <- transition_cons in *.
                rewrite <- derivative_list_cons in *.
                rewrite accepting_dt_list in *. rewrite E4 in *. discriminate.  
          -- clear E0 E1 E E3 E4.
             rewrite <- transition_cons in *.
             rewrite <- derivative_list_cons in *.
             rewrite accepting_dt_list in *. rewrite E5 in *. discriminate.  
  Qed.
        
  
  Lemma mpref_dt : forall code a e,
      max_pref_fn code (transition a (init_state e))
      = max_pref_fn code (init_state (derivative a e)).
  Proof.
    assert(L := mpref_dt_list).
    intros. specialize(L code [] e a). destruct L. auto.
  Qed.

  
  
  Lemma max_pref_matches : forall(code p x : String) (e : regex),
      Some (p, x) = max_pref_fn code (init_state e)
      -> exp_match p e.
  Proof.
    induction code; intros.
    - simpl in H. dm; try(discriminate).
      injection H; intros; subst.
      rewrite accepts_nil in E. symmetry in E. rewrite accepts_matches in E. auto.
    - symmetry in H. destruct p.
      + simpl in H. repeat dm.
        * destruct p. injection H; intros; discriminate.
        * injection H; intros; discriminate.
        * rewrite accepts_nil in E1. symmetry in E1. rewrite accepts_matches in E1. auto.
        * discriminate.
      + destruct (Sigma_dec a s).
        * subst. apply mpref_cons in H. symmetry in H. rewrite mpref_dt in H. apply IHcode in H.
          apply der_match. auto.
        * symmetry in H. apply max_pref_fn_splits in H. injection H. intros. contradiction.
  Qed.

  
   Theorem re_max_pref_correct__None : forall(code : String) (e : regex),
      re_no_max_pref code e
      <-> None = max_pref_fn code (init_state e).
   Proof.
     
     induction code.
     {
       split; intros.
       - simpl. inv H. dm. specialize (H1 []). destruct H1.
         + apply self_prefix.
         + rewrite accepts_nil in E. symmetry in E. rewrite accepts_matches in E. auto.
       - simpl in H. dm; try(discriminate).
         + apply re_MP0. intros. intros C. apply false_not_true in E.
           destruct E.
           symmetry. rewrite accepts_nil. apply accepts_matches.
           destruct cand; auto.
           inv H0. destruct H1. discriminate.
     }
     {
       split; intros.
       - simpl. repeat dm.
         + rewrite mpref_cons in E.
           symmetry in E.
           assert(E1 := E).
           apply max_pref_fn_splits in E. injection E. intros. clear E.
           apply max_pref_matches in E1.
           inv H. specialize (H1 (a :: p0)). destruct H1; auto.
           apply pref_def. exists s. auto.
         + clear H. symmetry in E. rewrite mpref_dt in E. apply IHcode in E.
           inv E. specialize (H1 []). destruct H1. apply nil_is_prefix.
           rewrite accepts_nil in E0. rewrite accepts_transition in E0.
           symmetry in E0. apply accepts_matches in E0. apply der_match. auto.
         + symmetry in E. rewrite mpref_dt in E. apply IHcode in E.
           inv E. specialize (H1 []). destruct H1. apply nil_is_prefix.
           inv H. specialize (H1 []). destruct H1.
           * apply nil_is_prefix.
           * rewrite accepts_nil in E1. symmetry in E1. apply accepts_matches in E1.
             auto.
       - simpl in H. repeat dm; try(discriminate).
         clear H. rewrite mpref_dt in E. symmetry in E. apply IHcode in E.
         inv E. apply re_MP0. intros. intros C. inv H. destruct H0.
         destruct cand.
         + rewrite false_not_true in E1. destruct E1.
           rewrite accepts_nil. symmetry. rewrite accepts_matches. auto.
         + injection H. intros. rewrite H2 in *. clear H H2.
           specialize (H1 cand). destruct H1.
           * apply pref_def. eexists. eauto.
           * apply der_match. auto.
     } 
   Qed.          
  
  Theorem re_max_pref_correct__Some : forall(code p : String) (e : regex),
      re_max_pref code e p
      <-> exists(q : String), Some (p, q) = max_pref_fn code (init_state e).
  Proof.
    induction code.
    {
      intros p e. split; intros H.
      - exists []. simpl. assert (A0 : p = []).
        {
          inv H. inv H1. destruct H0. destruct x.
          - rewrite nil_right in H. apply H.
          - destruct p.
            + reflexivity.
            + discriminate.
        }
        dm.
        + rewrite A0. reflexivity.
        + inv H. rewrite accepts_nil in E. apply accepts_matches in H2.
          rewrite E in H2. discriminate.
      - destruct H. apply re_MP1.
        + apply max_pref_fn_splits in H. symmetry in H.
          apply pref_def. exists x. apply H.
        + apply max_pref_matches in H. apply H.
        + intros cand H0. inv H0. destruct H1.
          assert (A0 : cand = []).
          {
            destruct cand.
            - reflexivity.
            - discriminate.
          }
          assert (A1 : p = []).
          {
            simpl in H. dm.
            - injection H. intros I1 I2. apply I2.
            - discriminate.
          }
          rewrite A0. rewrite A1. left. omega.
    }
    {
      intros p e. split; intros H.
      - destruct p.
        + exists (a :: code). inv H. simpl.
          dm.
          * destruct p. symmetry in E.
            rewrite mpref_dt in E.
            assert (Ae : exists q, Some (p, q) = max_pref_fn code (init_state (derivative a e))).
            { exists s. apply E. }
            apply IHcode in Ae. inv Ae.
            assert (Ap : a :: p ++_= a :: code).
            { apply cons_prefix. split. reflexivity. apply H0. }
            apply H3 in Ap. destruct Ap.
            -- simpl in H. omega.
            -- exfalso. destruct H. apply der_match. auto.
          * assert (A0 : accepting (transition a (init_state e)) = false).
            {
              destruct code.
              - simpl in E. dm.
                + discriminate.
              - simpl in E. dm.
                + destruct p. discriminate.
                + dm.
                  * discriminate.
                  * dm.
                    -- discriminate.
            }
            rewrite A0. apply accepts_matches in H2. rewrite <- accepts_nil in H2.
            rewrite <- H2. reflexivity.
        + inv H. inv H1. destruct H0. injection H.
          intros I1 I2. clear H. exists x. subst s.
          assert (Ap : p ++_= code).
          { apply pref_def. exists x. apply I1. }
          simpl. dm; symmetry in E.
          * destruct p0.
            assert (Ae : exists q, Some (p0, q) = max_pref_fn code (init_state (derivative a e))).
            { exists s. symmetry in E. rewrite mpref_dt in E. auto. }
            apply IHcode in Ae. inv Ae. inv H1. destruct H5. apply max_pref_fn_splits in E.
            (* Want to show p = p0 *)
            assert (A0 : p ++_= p ++ x).
            { apply pref_def. exists x. reflexivity. }
            assert (A1 : a :: p0 ++_= a :: p ++ x).
            { apply pref_def. exists x0. rewrite <- H. reflexivity. }
            apply H3 in A1. apply H4 in A0.
            (* should follow that p and p0 are prefixes of the same length and thus equal *)
            assert (A0' : length p <= length p0).
            {
              destruct A0.
              - apply H1.
              - exfalso. destruct H1. apply der_match. auto.
            }
            assert (A1' : length p0 <= length p).
            {
              destruct A1.
              - simpl in H1. omega.
              - exfalso. destruct H1. apply der_match; auto.
            }
            assert (A : length p = length p0).
            { omega. }
            assert (As : p0 ++_= p ++ x).
            { apply pref_def. exists x0. apply H. }
            apply eq_len_eq_pref with (x := p ++ x) in A.
            -- rewrite A. rewrite A in E. apply app_inv_head in E. rewrite E. reflexivity.
            -- apply As.
            -- apply Ap.
          * rewrite mpref_dt in E. apply re_max_pref_correct__None in E. inv E.
            assert (A0 : p = []).
            {
              assert (A1 : p ++_= p ++ x).
              { apply pref_def. exists x. reflexivity. }
              apply H1 in A1. destruct A1. apply der_match. auto.
            }
            assert (A1 : accepting (transition a (init_state e)) = true).
            {
              rewrite A0 in H2. symmetry. rewrite accepts_nil. rewrite accepts_transition.
              apply accepts_matches. auto.
            }
            rewrite A1. rewrite A0. reflexivity.
      - destruct H. apply re_MP1.
        + apply max_pref_fn_splits in H. apply pref_def. exists x. symmetry. apply H.
        + apply max_pref_matches in H. apply H.
        + intros cand Hpref. destruct p.
          * simpl in H.
            dm.
            -- destruct p. discriminate.
            -- dm.
               ++ discriminate.
               ++ dm.
                  ** symmetry in E. rewrite mpref_dt in E.
                     apply re_max_pref_correct__None in E. inv E. destruct cand.
                     { left. omega. }
                     {
                       right. inv Hpref. destruct H0. injection H0. intros I1 I2.
                       unfold not. intros C. assert (A : cand ++_= code).
                       { apply pref_def. exists x0. apply I1. }
                       
                       apply H1 in A. destruct A. subst.
                       apply der_match; auto.
                     }
                  ** discriminate.
          * simpl in H.
            dmh; symmetry in E.
            -- destruct p0. injection H. intros I1 I2 I3.
               rewrite mpref_dt in E.
               assert (Ae : exists q, Some (p0, q) = max_pref_fn code (init_state (derivative a e))).
               { exists s0. apply E. }
               apply IHcode in Ae. inv Ae. destruct cand.
               ++ left. simpl. omega.
               ++ inv Hpref. destruct H0. injection H0. intros I1 I2. subst s.
                  assert (Apref : cand ++_= code).
                  { apply pref_def. exists x. apply I1. }
                  apply H3 in Apref. destruct Apref.
                  ** left. simpl. omega.
                  ** right. intros C. destruct H4. apply der_match. auto.
            -- rewrite mpref_dt in E. apply re_max_pref_correct__None in E. inv E.
               assert (A0 : accepting (transition a (init_state e)) = true).
               {
                 repeat dm;
                   try(reflexivity); try(discriminate).
               }
               assert (A1 : [] ++_= code).
               { apply nil_is_prefix. }
               apply H1 in A1. destruct A1. apply accepts_matches. rewrite <- accepts_nil.
               symmetry. rewrite accepts_nil in *. rewrite accepts_transition in A0.
               symmetry in A0. symmetry.
               rewrite accepts_matches in *.
               apply der_match. apply A0.
    }
  Qed.

  Lemma no_tokens_suffix_self : forall rus code rest Ha,
      lex' rus code Ha = ([], rest) -> code = rest.
  Proof.
    intros rus code rest Ha H.
    apply lex'_cases in H. destruct H.
    symmetry. apply H.
  Qed.

  Lemma pref_not_no_pref : forall code p r,
      re_max_pref code r p
      -> ~(re_no_max_pref code r).
  Proof.
    intros code p r H C. inv H. inv C.
    apply H0 in H1. contradiction.
  Qed.

  Lemma max_pref_fn_Some_or_None : forall code fsm,
      (exists p q, Some (p, q) = max_pref_fn code fsm)
      \/ None = max_pref_fn code fsm.
  Proof.
    intros code fsm. destruct (max_pref_fn code fsm).
    - left. destruct p. exists p. exists s. reflexivity.
    - right. reflexivity.
  Qed.

  
  Lemma re_pref_or_no_pref : forall code r,
      (exists p, re_max_pref code r p) \/ re_no_max_pref code r.
  Proof.
    intros code r. 
    assert(L := max_pref_fn_Some_or_None).
    specialize (L code). specialize (L (init_state r)). destruct L.
    - left. destruct H as [p]. apply re_max_pref_correct__Some in H.
      eexists; eauto.
    - right. apply re_max_pref_correct__None in H. auto.
  Qed.

  Lemma part_around_in : forall (T : Type) (xs : list T) (x : T),
      In x xs -> exists xs1 xs2, xs = xs1 ++ (x :: xs2).
  Proof.
    intros T. induction xs; intros x Hin. contradiction.
    simpl in Hin. destruct Hin.
    - exists []. exists xs. rewrite H. reflexivity.
    - apply IHxs in H. destruct H as (xs1 & xs2 & H).
      rewrite H. exists (a :: xs1). exists xs2. reflexivity.
  Qed.

  Lemma at_index_In : forall rus ru,
      (exists n, at_index ru n rus) <-> In ru rus.
  Proof.
    induction rus; intros ru; split; intros H.
    - inv H. inv H0.
    - contradiction.
    - inv H.
      simpl. destruct x.
      + inv H0. left. reflexivity.
      + inv H0. right. apply IHrus. exists x. apply IH.
    - simpl in H. destruct H.
      + exists 0. apply AI0. auto.
      + apply IHrus in H. inv H. exists (S x).
        apply AI1. apply H0.
  Qed.

  Lemma In_least_index : forall rus ru,
      In ru rus <-> (exists n, least_index ru n rus).
  Proof.
    intros rus ru. split.
    {
      generalize dependent ru. induction rus; intros ru H. contradiction.
      destruct (ru_dec a ru).
      {
        subst. exists 0. apply LI1.
        - apply AI0. auto.
        - intros n' Hlt. omega.
      }
      {
        destruct H.
        - contradiction.
        - apply IHrus in H. destruct H. exists (S x). inv H. apply LI1.
          + apply AI1. apply Hat.
          + intros n' Hlt. intros C. destruct n'.
            * inv C. contradiction.
            * assert(Hlt' : n' < x). omega.
              apply Hnot in Hlt'. inv C. contradiction.
      }
    }
    {
      generalize dependent ru. induction rus; intros ru H.
      - inv H. inv H0. inv Hat.
      - destruct (ru_dec a ru); subst.
        + simpl. auto.
        + inv H. destruct x.
          * inv H0. inv Hat. contradiction.
          * simpl. right. apply IHrus. exists x. inv H0. apply LI1.
            -- inv Hat. apply IH.
            -- intros n' Hlt. specialize (Hnot (S n')).
               assert(A : S n' < S x). omega.
               apply Hnot in A. intros C. destruct A.
               apply AI1. apply C.
    }
  Qed.

  Lemma at_index_num_prev : forall rus1 ru rus2,
      at_index ru (length rus1) (rus1 ++ ru :: rus2).
  Proof.
    induction rus1; intros ru rus2.
    - simpl. apply AI0. reflexivity.
    - simpl. apply AI1. apply IHrus1.
  Qed.

  Lemma part_around_least_index : forall rus n ru,
      least_index ru n rus -> (exists rus1 rus2,
                                 rus = rus1 ++ (ru :: rus2)
                                 /\ length rus1 = n
                                 /\ ~(In ru rus1)).
  Proof.
    induction rus; intros n ru H.
    {
      inv H. inv Hat.
    }
    {
      inv H. inv Hat.
      - exists []. exists rus. split; [| split]; try(auto).
      - assert(least_index ru n0 rus).
        {
          apply LI1.
          - apply IH.
          - intros n' H C.
            assert(A0 : S n' < S n0).
            { omega. }
            apply Hnot in A0. destruct A0.
            apply AI1. apply C.
        }
        apply IHrus in H.
        destruct H as (rus1 & rus2 & IH').
        destruct IH' as (Heq & Hlen & Hnin).
        exists (a :: rus1). exists rus2. split; [| split].
        + rewrite Heq. reflexivity.
        + simpl. omega.
        + intros C. destruct Hnin. simpl in C. destruct C.
          * specialize (Hnot 0). rewrite H in Hnot. destruct Hnot.
            -- omega.
            -- apply AI0. reflexivity.
          * apply H.
    }
  Qed.

  (* Ah so this is what proof automation can do... *)
  Lemma lgr_pref_assoc : forall a b c,
      longer_pref (longer_pref a b) c = longer_pref a (longer_pref b c).
  Proof.
    intros a b c. unfold longer_pref.
    repeat dm; repeat inj_all; subst; repeat eqb_eq_all; repeat ltb_lt_all;
      try(discriminate);
      try(omega);
      try(auto).
  Qed.

  Lemma all_mprefs_nil : forall label p ps suffix rs r,
      max_of_prefs (max_prefs [] (r :: rs)) <> (label, Some (p :: ps, suffix)).
  Proof.
    intros label p ps suffix. induction rs; intros.
    - intro C. simpl in *. unfold extract_fsm_for_max in *. unfold longer_pref in *. simpl.
      repeat dm; repeat inj_all; dm; try(discriminate).
    - specialize (IHrs a). intros C. destruct IHrs.
      simpl in *. unfold extract_fsm_for_max in *. unfold longer_pref in *. simpl.
      repeat dm;
        repeat inj_all; subst; repeat ltb_lt_all; repeat eqb_eq_all;
          subst; simpl in *; try(omega); repeat dm; try(discriminate).
  Qed.

  Lemma mpref_app_dist : forall ps1 ps2,
      max_of_prefs (ps1 ++ ps2) = longer_pref (max_of_prefs ps1) (max_of_prefs ps2).
  Proof.
    induction ps1; intros ps2.
    - simpl. destruct (max_of_prefs ps2). reflexivity.
    - simpl. rewrite IHps1. symmetry. apply lgr_pref_assoc.
  Qed.

  Lemma mpref_cons_longer : forall ps p,
      max_of_prefs (p :: ps) = longer_pref p (max_of_prefs ps).
  Proof.
    intros ps p. simpl. reflexivity.
  Qed.

  
  Lemma nil_mpref_nil_or_no_pref : forall rus code s l l1 r,
      max_of_prefs (max_prefs code (map init_srule rus)) = (l1, Some ([], s))
      -> In (l, r) rus
      -> re_max_pref code r [] \/ re_no_max_pref code r.
  Proof.
    intros rus code s l l1 r Hmax Hin. assert(L := re_pref_or_no_pref code r).
    destruct L.
    - destruct H. destruct x.
      + left. apply H.
      (* This was a fun one *)
      + exfalso.
        apply re_max_pref_correct__Some in H. destruct H as [q]. symmetry in H.
        assert(L := (part_around_in _ rus (l, r)) Hin).
        destruct L as (rus1 & rus2 & L). subst rus. clear Hin.
        rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
        unfold max_prefs in Hmax. rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
        rewrite H in Hmax. rewrite mpref_app_dist in Hmax. rewrite mpref_cons_longer in Hmax.
        simpl in Hmax. unfold longer_pref in Hmax.
        (* 32 subgoals, 7 subproofs ! *)
        repeat dmh; subst;
          try (discriminate);
          try(injection Hmax; intros I1 I2 I3; subst p0;
              destruct p2; [discriminate | simpl in E5; discriminate]);
          try(injection E2; intros; subst; discriminate);
          try(rewrite Hmax in E1; discriminate).
        * injection E2; intros; injection Hmax; intros; subst;
            rewrite E11 in E5; simpl in E5; discriminate.
        * injection E2; intros; injection Hmax; intros; subst;
            destruct (length p0); simpl in E6; rewrite Nat.ltb_lt in E6; omega.
        * rewrite Hmax in E1. injection E1; intros; subst. simpl in E7; discriminate.
    - right. apply H.
  Qed.
   

  
  Lemma no_mpref_no_pref : forall rus code l l1 r,
      max_of_prefs (max_prefs code (map init_srule rus)) = (l1, None)
      -> In (l, r) rus
      -> re_no_max_pref code r.
  Proof.
    intros rus code l l1 r Hmax Hin. assert(L := re_pref_or_no_pref code r).
    destruct L.
    - exfalso. destruct H.
      (*apply invert_init_correct_max in H.*)
      apply re_max_pref_correct__Some in H. destruct H as [q]. symmetry in H.
      assert(L := (part_around_in _ rus (l, r)) Hin).
      destruct L as (rus1 & rus2 & L). subst rus. clear Hin.
      rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
      unfold max_prefs in Hmax. rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
      rewrite H in Hmax. rewrite mpref_app_dist in Hmax. rewrite mpref_cons_longer in Hmax.
      simpl in Hmax. unfold longer_pref in Hmax.
      repeat dmh; repeat inj_all; subst;
        try(discriminate);
        try(rewrite Hmax in E1; discriminate).
    - apply H.
  Qed.
  

  
  Lemma no_tokens_no_pref : forall code rest rus l r Ha,
      lex' (map init_srule rus) code Ha = ([], rest)
      -> In (l, r) rus
      -> re_max_pref code r [] \/ re_no_max_pref code r.
  Proof.
    intros code rest rus l r Ha Hlex Hin.
    apply lex'_cases in Hlex. destruct Hlex.
    destruct H0; destruct (max_of_prefs (max_prefs code (map init_srule rus))) eqn:E0;
      simpl in H0; [| destruct H0 as (suf & H0)]; rewrite H0 in E0.
    - apply no_mpref_no_pref with (l := l) (r := r) in E0.
      + right. apply E0.
      + apply Hin.
    - apply nil_mpref_nil_or_no_pref with (l := l) (r := r) in E0.
      + apply E0.
      + apply Hin.
  Qed.

  Lemma max_pref_unique : forall code r p p',
      re_max_pref code r p
      -> re_max_pref code r p'
      -> p = p'.
  Proof.
    intros code r p p' Hp Hp'.
    inv Hp. inv Hp'.
    assert(Hp := H1). assert(Hp' := H0).
    apply H5 in H1. apply H3 in H0. clear H3 H5.
    assert(A : length p <= length p' /\ length p' <= length p).
    { split; [destruct H1 | destruct H0]; try (apply H); try (contradiction). }
    assert (Aeq : length p' = length p).
    { omega. }
    apply eq_len_eq_pref with (x := code) in Aeq.
    apply Aeq. apply Hp. apply Hp'.
  Qed.

  Lemma max_pref_longer : forall xs l p s l' p' s' code,
      max_of_prefs xs = (l, Some(p, s))
      -> In (l', Some(p', s')) xs
      -> (l', Some(p', s')) <> (l, Some(p, s))
      -> p ++_= code
      -> p' ++_= code
      -> longer_pref (l, Some(p, s)) (l', Some(p', s')) = (l, Some(p, s)).
  Proof.
    intros xs l p s l' p' s' code Hmax Hin Hneq Hpref Hpref'.
    assert(Apart : exists xs1 xs2, xs = xs1 ++ ((l', Some(p', s')) :: xs2)).
    { apply part_around_in. apply Hin.  }
    destruct Apart as (xs1 & xs2 & Apart).
    rewrite Apart in *.
    rewrite mpref_app_dist in Hmax. rewrite mpref_cons_longer in Hmax.
    destruct (max_of_prefs xs1); destruct (max_of_prefs xs2).
    unfold longer_pref in Hmax. unfold longer_pref.
    repeat dm; subst;
      try(rewrite <- E0 in Hmax; injection Hmax; intros; subst);
      repeat inj_all;
      repeat ltb_lt_all;
      repeat eqb_eq_all;
      try(omega);
      try(discriminate).
  Qed.

  Lemma app_smaller_pref : forall {T : Type} (rus p1 p2 s1 s2 : list T) a1 a2,
      length p1 < length p2
      -> rus = p1 ++ a1 :: s1
      -> rus = p2 ++ a2 :: s2
      -> exists x y, (x ++ a2 :: y = s1
                /\ p1 ++ a1 :: x = p2
                /\ rus = p1 ++ (a1 :: x) ++ (a2 :: y) ).
  Proof.
    intros T. induction rus; intros.
    - exfalso. assert(L := app_cons_not_nil p1 s1 a1). contradiction.
    - destruct p1; destruct p2; try(simpl in H; omega).
      + simpl in H0. injection H0. injection H1. intros. subst.
        exists p2. exists s2. split; [|split]; reflexivity.
      + injection H0. injection H1. intros.
        assert(H' : length p1 < length p2).
        { simpl in H. omega. }
        apply IHrus with (s1 := s1) (s2 := s2) (a1 := a1) (a2 := a2) in H'.
        2:{ apply H4. }
        2:{ apply H2. }
        subst.
        destruct H' as (x & y & H'). destruct H'. destruct H3.
        exists x. exists y. split; [|split].
        * auto.
        * simpl. rewrite H3. auto.
        * simpl. simpl in H5. rewrite H5. auto.
  Qed.

  Lemma exists_rus_of_mpref : forall rus code l ph pt suffix,
      max_of_prefs (max_prefs code (map init_srule rus)) = (l, Some (ph :: pt, suffix))
      -> (exists r, In (l, r) rus
              /\ max_pref_fn code (init_state r) = Some (ph :: pt, suffix)).
  Proof.
    induction rus; intros.
    {
      simpl in H. discriminate.
    }
    {
      unfold max_prefs in H.
      repeat first [rewrite map_cons in H | rewrite map_app in H].
      symmetry in H. apply max_first_or_rest in H. destruct H.
      - destruct a. simpl in H. injection H; intros; subst.
        exists r. split.
        * left. auto.
        * auto.
      - symmetry in H. apply IHrus in H. destruct H as [r]. destruct H.
        exists r. split.
        + right. apply H.
        + apply H0.
    }
  Qed.

  Lemma first_token_mpref : forall rus code l ph pt suffix,
      max_of_prefs (max_prefs code (map init_srule rus)) = (l, Some (ph :: pt, suffix))
      -> rules_is_function rus
      -> first_token code rus (l, ph :: pt).
  Proof.
    intros rus code l ph pt suffix H Hfunc.
    assert(Aex := exists_rus_of_mpref rus code l ph pt suffix H).
    destruct Aex as [r]. destruct H0 as (Hin & Hmpref_fn).
    assert(Hmpref : re_max_pref code r (ph :: pt)).
    {
      symmetry in Hmpref_fn.
      assert(exists q, Some (ph :: pt, q) = max_pref_fn code (init_state r)).
      { eexists; eauto. }
      apply re_max_pref_correct__Some in H0. auto.
    }
    apply FT1 with (r := r).
    - intros C. discriminate.
    - apply Hin.
    - apply Hmpref.
    - intros l0 r0 p0 Hlen Hmpref'. intros C.
      apply re_max_pref_correct__Some with (e := r0) in Hmpref'. destruct Hmpref'.
      assert(Ain : In (l0, max_pref_fn code (init_state r0))
                      (max_prefs code (map init_srule rus))).
      {
        apply part_around_in in C. destruct C as (rus1 & rus2 & C). rewrite C.
        unfold max_prefs. repeat rewrite map_app. repeat rewrite map_cons. simpl.
        apply in_or_app. right. simpl. left. reflexivity.
      }
      assert(Aneq : (l0, max_pref_fn code (init_state r0)) <> (l, Some (ph :: pt, suffix))).
      { rewrite <- H0. intros C1. injection C1; intros; subst. omega. }
      apply max_pref_longer
        with (l' := l0) (p' := p0) (s' := x) (code := code)
        in H.
      + rewrite <- H0 in *. unfold longer_pref in H. repeat dmh.
        * eqb_eq_all. omega.
        * contradiction.
        * ltb_lt_all. omega.
      + rewrite <- H0 in Ain. apply Ain.
      + rewrite <- H0 in Aneq. apply Aneq.
      + inv Hmpref. apply H1.
      + assert(A : exists q, Some (p0, q) = max_pref_fn code (init_state r0)).
        { exists x. apply H0. }
        apply re_max_pref_correct__Some in A. inv A. apply H1.
    - intros r0 l0 Hearly Hin0 Hmpref0.
      assert(Hmpref_fn0 : max_pref_fn code (init_state r0) = Some (ph :: pt, suffix)).
      {
        apply re_max_pref_correct__Some with (e := r0) in Hmpref0.
        destruct Hmpref0 as (x & Hmpref_fn0).
        assert(Asuff : x = suffix).
        {
          symmetry in Hmpref_fn. apply max_pref_fn_splits in Hmpref_fn.
          apply max_pref_fn_splits in Hmpref_fn0.
          rewrite Hmpref_fn in Hmpref_fn0. apply app_inv_head in Hmpref_fn0.
          symmetry. apply Hmpref_fn0.
        }
        subst. auto.
      }
      assert(Aneq : l <> l0).
      {
        intros C. subst. unfold rules_is_function in Hfunc.
        apply Hfunc with (r := r0) in Hin.
        2:{ apply Hin0. }
        subst. inv Hearly. apply In_least_index in Hin0.
        destruct Hin0. apply H0 with (n1 := x) in H1.
        2:{ apply H1. }
        omega.
      }
      inv Hearly. apply In_least_index in Hin. apply In_least_index in Hin0.
      assert(Hin' := Hin).
      destruct Hin as (n2 & Hleast). destruct Hin0 as (n1 & Hleast').
      assert(Alt : n1 < n2).
      { auto. }
      apply part_around_least_index in Hleast.
      destruct Hleast as (rus1 & rus2 & Hleast). destruct Hleast as (Heq & Hlen & Hnin).
      apply part_around_least_index in Hleast'.
      destruct Hleast' as (rus1' & rus2' & Hleast'). destruct Hleast' as (Heq' & Hlen' & Hnin').
      rewrite <- Hlen in Alt. rewrite <- Hlen' in Alt.
      clear Hlen Hlen'.
      apply app_smaller_pref with (rus0 := rus)
                                  (s1 := rus2')
                                  (s2 := rus2)
                                  (a2 := (l,r))
                                  (a1 := (l0, r0)) in Alt.
      2:{ apply Heq'. }
      2:{ apply Heq. }
      destruct Alt as (x & y & H1). destruct H1. destruct H2.
      clear H0 Heq Heq'.
      rewrite H3 in *.
      assert(A0 : max_of_prefs (map (extract_fsm_for_max code) (map init_srule rus1')) <>
                  (l, Some (ph :: pt, suffix))).
      {
        intros C. apply exists_rus_of_mpref in C.
        destruct C as (r' & C). destruct C as (C1 & C2).
        destruct (regex_eq r r') eqn:E.
        - destruct Hnin.  apply regex_eq_correct in E. subst. apply in_or_app. left. apply C1.
        - subst. apply In_least_index in Hin'.
          assert(C1' : In (l, r') (rus1' ++ ((l0, r0) :: x) ++ (l, r) :: y)).
          { apply in_or_app. left. apply C1. }
          apply false_not_true in E. destruct E. apply regex_eq_correct.
          unfold rules_is_function in Hfunc. apply Hfunc with (l1 := l).
          + apply Hin'.
          + apply C1'.
      }
      unfold max_prefs in H.
      repeat first [rewrite map_cons in H | rewrite map_app in H].
      repeat first [rewrite mpref_cons_longer in H | rewrite mpref_app_dist in H].
      unfold longer_pref in H. 
      repeat dmh; repeat simpl in *; rewrite Hmpref_fn in *; rewrite Hmpref_fn0 in *;
        repeat inj_all; subst; repeat ltb_lt_all; repeat eqb_eq_all; subst;
          try(omega); try(contradiction); try(discriminate).
  Qed.

  Lemma lex'_splits : forall ts code rest rus Ha,
      lex' (map init_srule rus) code Ha = (ts, rest)
      -> code = (concat (map snd ts)) ++ rest.
  Proof.
    induction ts; intros code rest rus Ha H.
    {
      simpl. apply no_tokens_suffix_self in H. auto.
    }
    {
      destruct a. apply lex'_cases in H.
      destruct H as (h & t & H). destruct H as (s & Heq & H).
      destruct H. apply IHts in H.
      apply exists_rus_of_mpref in Heq. destruct Heq. destruct H1.
      symmetry in H2. apply max_pref_fn_splits in H2.
      subst. simpl.
      replace ((t ++ concat (map snd ts)) ++ rest)
        with (t ++ concat (map snd ts) ++ rest).
      2:{ apply app_assoc. }
      reflexivity.
    }
  Qed.

  Lemma eq_index_eq_ru : forall n rus ru1 ru2,
      at_index ru1 n rus
      -> at_index ru2 n rus
      -> ru1 = ru2.
  Proof.
    induction n; intros.
    - inv H. inv H0. auto.
    - inv H. inv H0. eapply IHn; eauto.
  Qed.

  Lemma eq_LI_eq_ru : forall n rus ru1 ru2,
      least_index ru1 n rus
      -> least_index ru2 n rus
      -> ru1 = ru2.
  Proof.
    intros. inv H. inv H0. eapply eq_index_eq_ru; eauto.
  Qed.

  Lemma least_index_unique : forall rus ru n1 n2,
      least_index ru n1 rus
      -> least_index ru n2 rus
      -> n1 = n2.
  Proof.
    intros. inv H. inv H0.
    destruct (Nat.lt_trichotomy n1 n2); [| destruct H].
    - apply Hnot0 in H. contradiction.
    - auto.
    - apply Hnot in H. contradiction.
  Qed.

  Lemma earlier_rule_split : forall rus ru1 ru2,
      In ru1 rus
      -> In ru2 rus
      -> ru1 = ru2 \/
        earlier_rule ru1 ru2 rus \/
        earlier_rule ru2 ru1 rus.
  Proof.
    intros.
    apply In_least_index in H. destruct H as [n1].
    apply In_least_index in H0. destruct H0 as [n2].
    assert(L := Nat.lt_trichotomy n1 n2). destruct L as [| L]; [|destruct L].
    - right. left. apply ERu1. intros.
      apply least_index_unique with (n1 := n0) in H; auto; subst.
      apply least_index_unique with (n1 := n3) in H0; auto; subst.
      auto.
    - left. subst. apply eq_LI_eq_ru with (ru1 := ru1) in H0; auto.
    - right. right. apply ERu1. intros.
      apply least_index_unique with (n1 := n3) in H; auto; subst.
      apply least_index_unique with (n1 := n0) in H0; auto; subst.
      auto.
  Qed.

  Lemma flip_gt : forall n m,
      n > m <-> m < n.
  Proof.
    intros. omega.
  Qed.

  Lemma first_token_unique : forall t t' code rus,
      first_token code rus t
      -> first_token code rus t'
      -> t = t'.
  Proof.
    intros. inv H; inv H0.
    (* show p and p0 are prefixes of equal length and thus equal *)
    assert(Alen : length p = length p0).
    {
      destruct (Nat.lt_trichotomy (length p) (length p0)); [|destruct H].
      - apply flip_gt in H. eapply Hout in H; destruct H; eauto.
      - auto.
      - apply flip_gt in H. apply Hout0 with (l' := l) (r' := r) in H; destruct H; auto.
    }
    assert(Aeq : p = p0).
    {
      inv Hmpref. inv Hmpref0.
      eapply eq_len_eq_pref in Alen; eauto.
    }
    subst.
    (* show neither rule can be earlier than the other and thus they are equal *)
    specialize (Hlater r0 l0).
    specialize (Hlater0 r l).
    clear Hout Hout0 Hnempt Hnempt0.
    assert(L := earlier_rule_split rus (l,r) (l0,r0) Hex Hex0). destruct L; [| destruct H].
    - inv H. auto.
    - apply Hlater0 in H; auto. contradiction.
    - apply Hlater in H; auto. contradiction.
  Qed.

End LemmasFn.
