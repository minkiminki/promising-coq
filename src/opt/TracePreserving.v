Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Simulation.
Require Import Compatibility.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive opt_lang_step: forall (e:option ProgramEvent.t) (st1 st2:State.t), Prop :=
| opt_lang_step_none
    st:
    opt_lang_step None st st
| opt_lang_step_some
    e st1 st2
    (STEP: lang.(Language.step) e st1 st2):
    opt_lang_step e st1 st2
.

Definition SIM_TRACE :=
  forall (sim_regs:SIM_REGS)
    (st1_src:lang.(Language.state))
    (st1_tgt:lang.(Language.state)), Prop.

Definition _sim_trace
           (sim_trace:SIM_TRACE)
           (sim_regs:SIM_REGS)
           (st1_src:lang.(Language.state))
           (st1_tgt:lang.(Language.state)): Prop :=
  <<TERMINAL:
    forall (TERMINAL_TGT: lang.(Language.is_terminal) st1_tgt),
    exists st2_src,
      <<STEPS: rtc (lang.(Language.step) None) st1_src st2_src>> /\
      <<TERMINAL_SRC: lang.(Language.is_terminal) st2_src>> /\
      <<TERMINAL: sim_regs st2_src.(State.regs) st1_tgt.(State.regs)>>>> /\
  <<STEP:
    forall e st3_tgt
      (STEP_TGT: lang.(Language.step) e st1_tgt st3_tgt),
    exists st2_src st3_src,
      <<STEPS: rtc (lang.(Language.step) None) st1_src st2_src>> /\
      <<STEP_SRC: opt_lang_step e st2_src st3_src>> /\
      <<SIM: sim_trace sim_regs st3_src st3_tgt>>>>.

Lemma _sim_trace_mon: monotone3 _sim_trace.
Proof.
  ii. unfold _sim_trace in *. des. splits; ss.
  i. exploit STEP; eauto. i. des. esplits; eauto.
Qed.
Hint Resolve _sim_trace_mon: paco.

Definition sim_trace: SIM_TRACE := paco3 _sim_trace bot3.

Lemma rtc_lang_tau_step_rtc_thread_tau_step
      st1 st2 lc sc mem
      (STEP: rtc (lang.(Language.step) None) st1 st2):
  rtc (@Thread.tau_step lang) (Thread.mk lang st1 lc sc mem) (Thread.mk lang st2 lc sc mem).
Proof.
  induction STEP.
  - econs 1.
  - econs 2; eauto. econs.
    + econs 2. econs 1. ss.
    + ss.
Qed.

Lemma sim_trace_sim_thread
      sim_regs
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_trace sim_regs st1_src st1_tgt)
      (LOCAL: sim_local lc1_src lc1_tgt):
  sim_thread
    (sim_terminal sim_regs)
    st1_src lc1_src sc1_src mem1_src
    st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  revert_until sim_regs. pcofix CIH. i.
  generalize SIM. i. punfold SIM0. unfold _sim_trace in SIM0. des.
  pfold. ii. splits.
  - i. exploit TERMINAL; eauto. i. des.
    exploit rtc_lang_tau_step_rtc_thread_tau_step; eauto. i.
    esplits; eauto. econs. ss.
  - i. exploit sim_local_future; (try by apply LOCAL); eauto. i. des.
    esplits; eauto.
    + etrans.
      * apply Memory.max_timemap_spec; eauto. committac.
      * apply sim_memory_max_timemap; eauto.
    + etrans.
      * apply Memory.max_timemap_spec; eauto. committac.
      * apply Memory.future_max_timemap; eauto.
    + apply Memory.max_timemap_closed. committac.
  - i. exploit sim_local_memory_bot; eauto. i.
    esplits; eauto.
  - ii. inv STEP_TGT; inv STEP0.
    + exploit sim_local_promise; eauto. i. des.
      esplits; (try exact SC); eauto.
      econs 2. econs 1. econs; eauto.
    + exploit STEP; eauto. i. des; [|done].
      inv STEP_SRC.
      { esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC);
          eauto.
        econs 1.
      }
      { esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC);
          eauto.
        econs 2. econs 2. econs 1; eauto.
      }
    + exploit STEP; eauto. i. des; [|done].
      inv STEP_SRC.
      exploit sim_local_read; eauto; try refl. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * econs 2. econs 2. econs 2; eauto.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des; [|done].
      inv STEP_SRC.
      hexploit sim_local_write;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl; try by committac. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * econs 2. econs 2. econs 3; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des; [|done].
      inv STEP_SRC.
      exploit Local.read_step_future; eauto. i. des.
      exploit sim_local_read; eauto; try refl. i. des.
      exploit Local.read_step_future; eauto. i. des.
      hexploit sim_local_write;
        (try exact LOCAL0);
        (try exact SC);
        eauto; try refl; try by committac. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * econs 2. econs 2. econs 4; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des; [|done].
      inv STEP_SRC.
      exploit sim_local_fence;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * econs 2. econs 2. econs 5; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des; [|done].
      inv STEP_SRC.
      exploit sim_local_fence;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * econs 2. econs 2. econs 6; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
Qed.

Lemma sim_trace_sim_stmts
      (sim_regs1 sim_regs2:SIM_REGS)
      stmts1_src
      stmts1_tgt
      (SIM: forall rs1_src rs1_tgt
              (SIM_REGS1: sim_regs1 rs1_src rs1_tgt),
          sim_trace sim_regs2 (State.mk rs1_src stmts1_src) (State.mk rs1_tgt stmts1_tgt)):
  sim_stmts sim_regs1
            stmts1_src
            stmts1_tgt
            sim_regs2.
Proof.
  ii. apply sim_trace_sim_thread; auto.
Qed.
