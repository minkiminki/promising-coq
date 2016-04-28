Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Set Implicit Arguments.


Module Threads.
  Definition syntax := IdentMap.t {lang:Language.t & lang.(Language.syntax)}.
  Definition t := IdentMap.t {lang:Language.t & Thread.t lang}.

  Definition init (s:syntax): t :=
    IdentMap.map (fun s => existT _ _ (Thread.init _ s.(projT2))) s.

  Definition singleton tid lang th: t :=
    IdentMap.add tid (existT _ lang th) (IdentMap.empty _).

  Definition is_terminal (ths:t): Prop :=
    forall tid lang th (FIND: IdentMap.find tid ths = Some (existT _ lang th)),
      Thread.is_terminal th.

  Inductive consistent (ths:t) (mem:Memory.t): Prop :=
  | consistent_intro
      (DISJOINT:
         forall tid1 lang1 th1
           tid2 lang2 th2
           (TID: tid1 <> tid2)
           (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 th1))
           (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 th2)),
           Memory.disjoint th1.(Thread.promise) th2.(Thread.promise))
      (THREADS: forall tid lang th
                  (TH: IdentMap.find tid ths = Some (existT _ lang th)),
          <<WF: Thread.wf th mem>> /\ <<CONSISTENT: Thread.consistent th mem>>)
      (MEMORY: Memory.wf mem)
  .

  Inductive disjoint (ths1 ths2:t): Prop :=
  | disjoint_intro
      (THREAD:
         forall tid lth1 lth2
           (TH1: IdentMap.find tid ths1 = Some lth1)
           (TH2: IdentMap.find tid ths2 = Some lth2),
           False)
      (MEMORY:
         forall tid1 lang1 th1
           tid2 lang2 th2
           (TH1: IdentMap.find tid1 ths1 = Some (existT _ lang1 th1))
           (TH2: IdentMap.find tid2 ths2 = Some (existT _ lang2 th2)),
           Memory.disjoint th1.(Thread.promise) th2.(Thread.promise))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs; i.
    - eapply THREAD; eauto.
    - symmetry. eapply MEMORY; eauto.
  Qed.

  Definition compose_option {A} (th1 th2:option A) :=
    match th1 with
    | None => th2
    | Some _ => th1
    end.

  Definition compose (ths1 ths2:t): t :=
    IdentMap.map2 compose_option ths1 ths2.

  Lemma compose_spec ths1 ths2 tid:
    IdentMap.find tid (compose ths1 ths2) = compose_option (IdentMap.find tid ths1) (IdentMap.find tid ths2).
  Proof. apply IdentMap.Facts.map2_1bis; auto. Qed.
End Threads.


Module Configuration.
  Structure t := mk {
    threads: Threads.t;
    memory: Memory.t;
  }.

  Definition init (s:Threads.syntax): t := mk (Threads.init s) Memory.init.
  Definition is_terminal (conf:t): Prop := Threads.is_terminal conf.(threads).

  Definition consistent (conf:t): Prop :=
    Threads.consistent conf.(threads) conf.(memory).

  Inductive step (e:option Event.t) (c1:t): forall (c2:t), Prop :=
  | step_intro
      tid lang th1 th2 memory2 th3 memory3
      (TID: IdentMap.find tid c1.(threads) = Some (existT _ lang th1))
      (STEPS: rtc (@Thread._internal_step lang) (th1, c1.(memory)) (th2, memory2))
      (STEP: Thread.step e th2 memory2 th3 memory3)
      (CONSISTENT: Thread.consistent th3 memory3):
      step e c1 (mk (IdentMap.add tid (existT _ _ th3) c1.(threads)) memory3)
  .

  Ltac simplify :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some _ = Some _ |- _] =>
             inv H
           | [H: existT ?P ?p _ = existT ?P ?p _ |- _] =>
             apply inj_pair2 in H
           | [H: existT ?P ?p _ = existT ?P ?q _ |- _] =>
             apply eq_sigT_sig_eq in H; inv H
           end;
       ss; subst).

  Lemma step_consistent
        e c1 c2
        (STEP: step e c1 c2)
        (CONSISTENT1: consistent c1):
    <<CONSISTENT2: consistent c2>> /\
    <<FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    inv CONSISTENT1. inv STEP. s.
    exploit THREADS; eauto. i. des.
    exploit Thread.rtc_internal_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. i. des.
    splits; [|by etransitivity; eauto].
    econs.
    - i. simplify.
      + congruence.
      + exploit THREADS; try apply TH1; eauto. i. des. inv WF1.
        exploit Thread.rtc_internal_step_disjoint; eauto. s. i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        symmetry. auto.
      + exploit THREADS; try apply TH2; eauto. i. des. inv WF1.
        exploit Thread.rtc_internal_step_disjoint; eauto. s. i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        auto.
      + eapply DISJOINT; [|eauto|eauto]. auto.
    - i. simplify.
      exploit THREADS; try apply TH; eauto. i. des. inv WF1.
      exploit Thread.rtc_internal_step_disjoint; eauto. i. des.
      exploit Thread.step_disjoint; eauto. i. des.
      splits.
      + econs; auto. eapply Commit.future_wf; eauto.
        etransitivity; eauto.
      + ii. apply CONSISTENT1; auto.
        repeat (etransitivity; eauto).
    - simplify.
  Qed.

  Lemma step_disjoint
        e c1 c2 ths
        (STEP: step e c1 c2)
        (DISJOINT: Threads.disjoint c1.(threads) ths)
        (CONSISTENT1: consistent c1)
        (CONSISTENT: consistent (mk ths c1.(memory))):
      <<DISJOINT: Threads.disjoint c2.(threads) ths>> /\
      <<CONSISTENT: consistent (mk ths c2.(memory))>>.
  Proof.
    inv STEP. ss. splits.
    - econs; s; ii; simplify.
      + inv DISJOINT. eapply THREAD; eauto.
      + inv DISJOINT. eapply THREAD; eauto.
      + exploit Thread.rtc_internal_step_future; eauto.
        { eapply CONSISTENT1; eauto. }
        { eapply CONSISTENT1; eauto. }
        exploit Thread.rtc_internal_step_disjoint; eauto.
        { s. inv DISJOINT. eapply MEMORY; eauto. }
        { eapply CONSISTENT1; eauto. }
        { eapply CONSISTENT; eauto. }
        { eapply CONSISTENT; eauto. }
        s. i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        auto.
      + inv DISJOINT. eapply MEMORY; eauto.
    - exploit Thread.rtc_internal_step_future; eauto.
      { eapply CONSISTENT1; eauto. }
      { eapply CONSISTENT1; eauto. }
      s. i. des.
      exploit Thread.step_future; eauto. i. des.
      econs; s; eauto.
      + i. eapply CONSISTENT; eauto.
      + i.
        exploit Thread.rtc_internal_step_disjoint; eauto.
        { s. inv DISJOINT. eapply MEMORY; eauto. }
        { eapply CONSISTENT1; eauto. }
        { eapply CONSISTENT; eauto. }
        { eapply CONSISTENT; eauto. }
        i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        splits.
        * econs; auto. eapply Commit.future_wf.
          { eapply CONSISTENT. eauto. }
          { s. etransitivity; eauto. }
        * inv CONSISTENT. exploit THREADS; eauto. i. des.
          ii. eapply CONSISTENT; eauto.
          repeat (etransitivity; eauto).
  Qed.

  Lemma rtc_step_consistent
        c1 c2
        (STEPS: rtc (step None) c1 c2)
        (CONSISTENT1: consistent c1):
    <<CONSISTENT2: consistent c2>> /\
    <<FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    revert CONSISTENT1. induction STEPS; i.
    - splits; auto. reflexivity.
    - exploit step_consistent; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto. etransitivity; eauto.
  Qed.

  Lemma rtc_step_disjoint
        c1 c2 ths
        (STEPS: rtc (step None) c1 c2)
        (DISJOINT: Threads.disjoint c1.(threads) ths)
        (CONSISTENT1: consistent c1)
        (CONSISTENT: consistent (mk ths c1.(memory))):
      <<DISJOINT: Threads.disjoint c2.(threads) ths>> /\
      <<CONSISTENT: consistent (mk ths c2.(memory))>>.
  Proof.
    revert DISJOINT CONSISTENT1 CONSISTENT. induction STEPS; auto. i.
    exploit step_consistent; eauto. i. des.
    exploit step_disjoint; eauto. i. des.
    apply IHSTEPS; auto.
  Qed.
End Configuration.
