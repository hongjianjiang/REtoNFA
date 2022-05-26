
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

inductive LTS_is_reachable :: "('q, 'a) LTS  \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool"  where 
   LTS_Empty:"LTS_is_reachable \<Delta> q [] q"|
   LTS_Step:"(\<exists>q'' \<sigma>. a \<in> \<sigma> \<and> (q, \<sigma>, q'') \<in> \<Delta> \<and> LTS_is_reachable \<Delta> q'' w q') \<Longrightarrow> 
              LTS_is_reachable \<Delta> q (a # w) q'"|
   LTS_Epi:"(\<exists>q''. (q,{},q'') \<in> \<Delta> \<and>  LTS_is_reachable \<Delta> q'' [] q') \<Longrightarrow>   LTS_is_reachable \<Delta> q [] q'"|
   LTS_Epi1:"(\<exists>q''. (q,{},q'') \<in> \<Delta> \<and>  LTS_is_reachable \<Delta> q'' l q') \<Longrightarrow>   LTS_is_reachable \<Delta> q l q'"


inductive_cases LTS_Step_cases[elim!]:"LTS_is_reachable \<Delta> q (a # w) q'"

inductive_cases LTS_Epi_cases[elim!]:"LTS_is_reachable \<Delta> q [] q"

inductive_cases LTS_Epi1_cases[elim!]:"LTS_is_reachable \<Delta> q l q"



lemma DeltLTSlemma1:"LTS_is_reachable Δ q al y \<Longrightarrow>LTS_is_reachable {(f u, v, f w)| u v w. (u,v,w)\<in> Δ } (f q) al (f y)"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty Δ q)
    then show ?case 
      by (simp add: LTS_is_reachable.LTS_Empty)
  next
    case (LTS_Step a q Δ w q')
    then show ?case 
      by (smt (verit, best) CollectI LTS_is_reachable.LTS_Step)
  next
    case (LTS_Epi q Δ q')
    then show ?case 
      by (smt (verit, ccfv_threshold) CollectI LTS_is_reachable.LTS_Epi)
  next
    case (LTS_Epi1 q Δ l q')
    then show ?case 
      by (metis (mono_tags, lifting) CollectI LTS_is_reachable.LTS_Epi1)
  qed

lemma subLTSlemma:"LTS_is_reachable l1 q x y \<Longrightarrow> LTS_is_reachable (l1 \<union> l2) q x y"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty Δ q)
    then show ?case 
      by (simp add: LTS_is_reachable.LTS_Empty)
  next
    case (LTS_Step a q Δ w q')
    then show ?case 
      by (meson LTS_is_reachable.LTS_Step UnI1)
  next
    case (LTS_Epi q Δ q')
    then show ?case 
      by (meson LTS_is_reachable.LTS_Epi Un_iff)
  next
    case (LTS_Epi1 q Δ l q')
    then show ?case 
      by (meson LTS_is_reachable.LTS_Epi1 UnI1)
  qed




lemma joinLTSlemma:"LTS_is_reachable l1 q a y \<Longrightarrow> LTS_is_reachable l1 y b z \<Longrightarrow> LTS_is_reachable l1 q (a@b) z"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty Δ q)
    then show ?case 
      by simp
  next
    case (LTS_Step a q Δ w q')
    then show ?case 
      by (metis LTS_is_reachable.LTS_Step append_Cons)
  next
    case (LTS_Epi q Δ q')
    then show ?case 
      by (meson LTS_Epi1)
  next
    case (LTS_Epi1 q Δ l q')
    then show ?case 
      by (meson LTS_is_reachable.LTS_Epi1)
  qed



end