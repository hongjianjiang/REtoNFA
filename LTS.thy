
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


inductive LTS_is_reachable :: "('q, 'a) LTS   \<Rightarrow>   ('q * 'q) set \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" where
   LTS_Empty[intro!]:"LTS_is_reachable l1 l2 q [] q"|
   LTS_Step1:"(q, q'') \<in> l2 \<and> LTS_is_reachable l1 l2 q'' l q' \<Longrightarrow> LTS_is_reachable l1 l2 q l q'" |
   LTS_Step2[intro!]:"(\<exists>q'' \<sigma>. a \<in> \<sigma> \<and> (q, \<sigma>, q'') \<in> l1 \<and> LTS_is_reachable l1 l2 q'' w q') \<Longrightarrow> LTS_is_reachable l1 l2 q (a # w) q'"


lemma subLTSlemma:"LTS_is_reachable l1 l2 q x y \<Longrightarrow> LTS_is_reachable (l1 \<union> l3) (l2 \<union> l4) q x y"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty l1 l2 q)
    then show ?case by auto
  next
    case (LTS_Step1 q q'' l2 l1 l q')
    then show ?case apply auto 
      by (meson LTS_is_reachable.LTS_Step1 UnI1)
  next
    case (LTS_Step2 a q l1 l2 w q')
    then show ?case by auto
  qed
  
lemma subLTSlemma1:"LTS_is_reachable l1 l2  q x y \<Longrightarrow> LTS_is_reachable (l1 \<union> {(f q a, va, f q' a)|q va q'. (q,va,q') \<in> l1}) (l2 \<union> l4) q x y"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty l1 l2 q)
    then show ?case by auto 
  next
    case (LTS_Step1 q q'' l2 l1 l q')
    then show ?case apply auto
      by (meson LTS_is_reachable.LTS_Step1 subLTSlemma)
  next
    case (LTS_Step2 a q l1 l2 w q')
    then show ?case by auto
  qed

lemma DeltLTSlemma1:"LTS_is_reachable l1 l2 q l q' \<Longrightarrow> LTS_is_reachable ({(f q a, va, f q' a)| q va q'. (q, va, q')\<in> l1})  ({(f q a, f q' a)| q q'. (q, q') \<in> l2}) (f q a) l (f q' a)"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty l1 l2 q)
    then show ?case by auto
  next
    case (LTS_Step1 q q'' l2 l1 l q')
    then show ?case apply auto
      by (smt (verit, best) LTS_is_reachable.LTS_Step1 mem_Collect_eq)
  next
    case (LTS_Step2 a q l1 l2 w q')
    then show ?case apply auto 
      by blast
  qed  




lemma joinLTSlemma:"LTS_is_reachable l1 l2 q x p \<Longrightarrow>  LTS_is_reachable l1 l2 p y q''\<Longrightarrow> LTS_is_reachable l1 l2 q (x@y) q''"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty l1 l2 q)
    then show ?case by auto
  next
    case (LTS_Step1 q q'' l2 l1 l q')
    then show ?case apply auto
      by (meson LTS_is_reachable.LTS_Step1)
  next
    case (LTS_Step2 a q l1 l2 w q')
    then show ?case by auto
  qed 


end
