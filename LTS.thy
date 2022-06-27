
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

inductive LTS_is_reachable :: "('q, 'a) LTS \<Rightarrow>  ('q * 'q) set \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" for \<Delta> and \<Delta>' where
  LTS_Empty[intro!]: "LTS_is_reachable \<Delta> \<Delta>' q [] q" |
  LTS_Step1: "LTS_is_reachable \<Delta> \<Delta>' q l q'" if "(q, q'') \<in> \<Delta>'" and "LTS_is_reachable \<Delta> \<Delta>' q'' l q'" |
  LTS_Step2[intro!]: "LTS_is_reachable \<Delta> \<Delta>' q (a # w) q'" if "a \<in> \<sigma>" and "(q, \<sigma>, q'') \<in> \<Delta>" and "LTS_is_reachable \<Delta> \<Delta>' q'' w q'"


lemma Delta1Empty: "LTS_is_reachable d1 d2 p l q \<Longrightarrow> d1 =  {} \<Longrightarrow> l = []"
  by (induction rule: LTS_is_reachable.induct) auto 


lemma subLTSlemma:"LTS_is_reachable \<Delta> \<Delta>' q x y \<Longrightarrow> LTS_is_reachable ( \<Delta> \<union> l1) (\<Delta>' \<union> l2) q x y"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty q)
    then show ?case by auto
  next
    case (LTS_Step1 q q'' l q')
    then show ?case 
      by (meson LTS_is_reachable.LTS_Step1 UnI1)
  next
    case (LTS_Step2 a \<sigma> q q'' w q')
    then show ?case by auto
  qed
 
lemma subLTSlemma1:"LTS_is_reachable \<Delta> \<Delta>' q x y \<Longrightarrow> LTS_is_reachable (\<Delta> \<union> {(f q a, va, f q' a)|q va q'. (q,va,q') \<in> \<Delta>}) (\<Delta>' \<union> l1) q x y"
  by (simp add: subLTSlemma)

lemma DeltLTSlemma1:"LTS_is_reachable \<Delta> \<Delta>' q l q' \<Longrightarrow> LTS_is_reachable ({(f q a, va, f q' a)| q va q'. (q, va, q') \<in> \<Delta>}) ({(f q a, f q' a)| q q'. (q, q') \<in> \<Delta>'}) (f q a) l (f q' a)"
proof (induction rule: LTS_is_reachable.induct)
  case (LTS_Empty q)
  then show ?case by auto
next
  case (LTS_Step1 q q'' l q')
  then show ?case 
    using LTS_is_reachable.simps by fastforce
next
  case (LTS_Step2 a \<sigma> q q'' w q')
  then show ?case by auto
qed

lemma DeltLTSlemma2:"\<exists>l. LTS_is_reachable \<Delta> \<Delta>' q l q' \<Longrightarrow> \<exists>l. LTS_is_reachable ({(f q a, va, f q' a)| q va q'. (q, va, q') \<in> \<Delta>}) ({(f q a, f q' a)| q q'. (q, q') \<in> \<Delta>'}) (f q a) l (f q' a)"
  apply(rule exE) apply auto subgoal for la  proof -
    assume "LTS_is_reachable \<Delta> \<Delta>' q la q'" 
    then have "LTS_is_reachable {(f q a, va, f q' a) |q va q'. (q, va, q') \<in> \<Delta>} {(f q a, f q' a) |q q'. (q, q') \<in> \<Delta>'} (f q a) la (f q' a)" apply(rule LTS_is_reachable.induct)
      subgoal by auto
      subgoal for q q'' l q'
        using LTS_is_reachable.simps by fastforce
      subgoal for aa \<sigma> q q'' w q'
        by auto
      done
    then show ?thesis by auto
  qed
  done
 

lemma joinLTSlemma:"LTS_is_reachable  \<Delta> \<Delta>' q x p \<Longrightarrow>  LTS_is_reachable  \<Delta> \<Delta>' p y q''\<Longrightarrow> LTS_is_reachable  \<Delta> \<Delta>' q (x@y) q''"
proof (induction rule: LTS_is_reachable.induct)
case (LTS_Empty q)
then show ?case by auto
next
  case (LTS_Step1 q q'' l q')
then show ?case  by (meson LTS_is_reachable.LTS_Step1)
next
  case (LTS_Step2 a \<sigma> q q'' w q')
  then show ?case by auto
qed

lemma joinLTSlemma1:"\<exists>x. LTS_is_reachable  \<Delta> \<Delta>' q x p \<Longrightarrow>  \<exists>y. LTS_is_reachable  \<Delta> \<Delta>' p y q''\<Longrightarrow> \<exists>x y. LTS_is_reachable  \<Delta> \<Delta>' q (x@y) q''"
  by (meson joinLTSlemma)     
end
