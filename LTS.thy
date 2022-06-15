
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


inductive LTS_is_reachable :: "('q, 'a) LTS \<Rightarrow>  ('q * 'q) set \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" where
   LTS_Empty[intro!]:"LTS_is_reachable \<Delta> \<Delta>' q [] q"|
   LTS_Step1:"(q, q'') \<in> \<Delta>' \<and> LTS_is_reachable \<Delta> \<Delta>' q'' l q' \<and> q \<noteq> q''\<Longrightarrow> LTS_is_reachable \<Delta> \<Delta>' q l q'" |
   LTS_Step2[intro!]:"\<exists>q'' \<sigma>. a \<in> \<sigma> \<and> (q, \<sigma>, q'') \<in> \<Delta> \<and> LTS_is_reachable \<Delta> \<Delta>' q'' w q' \<Longrightarrow> LTS_is_reachable \<Delta> \<Delta>' q (a # w) q'"



lemma subLTSlemma:"LTS_is_reachable  \<Delta> \<Delta>' q x y \<Longrightarrow> LTS_is_reachable ( \<Delta> \<union> l1) (\<Delta>' \<union> l2) q x y"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty \<Delta> \<Delta>' q)
    then show ?case by auto
  next
    case (LTS_Step1 q q'' \<Delta>' \<Delta> l q')
    then show ?case apply auto
      by (meson LTS_is_reachable.LTS_Step1 UnI1)
  next
    case (LTS_Step2 a q \<Delta> \<Delta>' w q')
    then show ?case by auto
  qed


lemma subLTSlemma1:"LTS_is_reachable \<Delta> \<Delta>' q x y \<Longrightarrow> LTS_is_reachable (\<Delta> \<union> {(f q a, va, f q' a)|q va q'. (q,va,q') \<in> \<Delta>}) (\<Delta>' \<union> l1) q x y"
  by (simp add: subLTSlemma)


lemma DeltLTSlemma1:"LTS_is_reachable \<Delta> \<Delta>' q l q' \<Longrightarrow> LTS_is_reachable ({(f q a, va, f q' a)| q va q'. (q, va, q') \<in> \<Delta>}) ({(f q a, f q' a)| q q'. (q, q') \<in> \<Delta>'}) (f q a) l (f q' a)"
proof (induction rule: LTS_is_reachable.induct)
  case (LTS_Empty \<Delta> \<Delta>' q)
  then show ?case by auto
next
  case (LTS_Step1 q q'' \<Delta>' \<Delta> l q')
  then show ?case apply auto
    by (smt (verit, ccfv_SIG) CollectI LTS_is_reachable.LTS_Step1)
next
  case (LTS_Step2 a q \<Delta> \<Delta>' w q')
  then show ?case 
    apply auto 
    by blast
qed




lemma joinLTSlemma:"LTS_is_reachable  \<Delta> \<Delta>' q x p \<Longrightarrow>  LTS_is_reachable  \<Delta> \<Delta>' p y q''\<Longrightarrow> LTS_is_reachable  \<Delta> \<Delta>' q (x@y) q''"
proof (induction rule: LTS_is_reachable.induct)
  case (LTS_Empty \<Delta> \<Delta>' q)
  then show ?case by auto
next
  case (LTS_Step1 q q'' \<Delta>' \<Delta> l q')
  then show ?case 
    apply auto 
    by (meson LTS_is_reachable.LTS_Step1)
next
  case (LTS_Step2 a q \<Delta> \<Delta>' w q')
  then show ?case by auto 
qed
    
end
