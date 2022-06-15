
theory LTS
imports Main "HOL.Option"
begin


text \<open> Given a set of states $\mathcal{Q}$ and an alphabet $\Sigma$,
a labeled transition system is a subset of $\mathcal{Q} \times \Sigma
\times \mathcal{Q}$.  Given such a relation $\Delta \subseteq
\mathcal{Q} \times \Sigma \times \mathcal{Q}$, a triple $(q, \sigma,
q')$ is an element of $\Delta$ iff starting in state $q$ the state
$q'$ can be reached reading the label $\sigma$. \<close>

  
type_synonym ('q,'a) LTS = "('q * 'a set * 'q) set"

subsubsection  \<open>Reachability\<close>

text \<open>Often it is enough to consider just the first and last state of
a path. This leads to the following definition of reachability. Notice, 
that @{term "LTS_is_reachable \<Delta>"} is the reflexive, transitive closure of @{term \<Delta>}.\<close>


inductive LTS_is_reachable :: "(('q, 'a) LTS * ('q * 'q) set) \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" where
   LTS_Empty[intro!]:"LTS_is_reachable lts q [] q"|
   LTS_Step1:"(q, q'') \<in> snd lts \<and> LTS_is_reachable lts q'' l q' \<Longrightarrow> LTS_is_reachable lts q l q'" |
   LTS_Step2[intro!]:"(\<exists>q'' \<sigma>. a \<in> \<sigma> \<and> (q, \<sigma>, q'') \<in> fst lts \<and> LTS_is_reachable lts q'' w q') \<Longrightarrow> LTS_is_reachable lts q (a # w) q'"



lemma subLTSlemma:"LTS_is_reachable l1 q x y \<Longrightarrow> LTS_is_reachable (fst l1 \<union> l2, snd l1 \<union> l3) q x y"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty lts q)
    then show ?case by auto
  next
    case (LTS_Step1 q lts l q')
    then show ?case 
      by (metis LTS_is_reachable.LTS_Step1 Un_iff snd_conv)
  next
    case (LTS_Step2 a q lts w q')
    then show ?case 
      by (smt (z3) LTS_is_reachable.LTS_Step2 UnI1 fst_conv)
  qed


lemma subLTSlemma1:"LTS_is_reachable l1 q x y \<Longrightarrow> LTS_is_reachable (fst l1 \<union> {(f q a, va, f q' a)|q va q'. (q,va,q') \<in> fst l1}, snd l1 \<union> l3) q x y"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty lts q)
    then show ?case by auto
  next
    case (LTS_Step1 q lts l q')
    then show ?case 
      by (meson LTS_is_reachable.LTS_Step1 subLTSlemma)
  next
    case (LTS_Step2 a q lts w q')
    then show ?case 
      by (smt (z3) LTS_is_reachable.LTS_Step2 UnI1 fst_conv)
  qed

lemma DeltLTSlemma1:"LTS_is_reachable lts q l q' \<Longrightarrow>LTS_is_reachable ({(f q a, va, f q' a)| q va q'. (q, va, q')\<in> fst lts}, {(f q a, f q' a)| q q'. (q, q') \<in> snd lts}) (f q a) l (f q' a)"
  proof (induction rule: LTS_is_reachable.induct)  
    case (LTS_Empty lts q)
    then show ?case by auto
  next
    case (LTS_Step1 q lts l q')
    then show ?case apply auto
    proof -
      have "(f q a, f lts a) \<in> snd ({(f aa a, B, f ab a) |aa B ab. (aa, B, ab) \<in> fst l}, {(f aa a, f ab a) |aa ab. (aa, ab) \<in> snd l})"
        using LTS_Step1.IH by auto
      then show ?thesis
        by (smt (z3) LTS_Step1.IH LTS_is_reachable.LTS_Step1)
    qed
  next
    case (LTS_Step2 a q lts w q')
    then show ?case apply auto by blast
  qed




lemma joinLTSlemma:"LTS_is_reachable l q x p \<Longrightarrow>  LTS_is_reachable l p y q''\<Longrightarrow> LTS_is_reachable l q (x@y) q''"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty lts q)
    then show ?case apply auto done
  next
    case (LTS_Step1 q lts l q')
    then show ?case 
      by (meson LTS_is_reachable.LTS_Step1)
  next
    case (LTS_Step2 a q lts w q')
    then show ?case apply auto done
  qed
end
