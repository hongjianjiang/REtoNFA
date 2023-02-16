
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


thm LTS_is_reachable.cases 
thm LTS_is_reachable.induct

lemma removeExtraConstrans: "LTS_is_reachable \<Delta> (insert (e1, e2) \<Delta>') ini l end \<Longrightarrow> \<forall>q \<sigma>. (q, \<sigma>, e1) \<notin> \<Delta> \<Longrightarrow> \<forall>q. (q, e1) \<notin> \<Delta>' \<Longrightarrow> ini \<noteq> e1 \<Longrightarrow> LTS_is_reachable \<Delta> \<Delta>' ini l end"
  proof (induction rule: LTS_is_reachable.induct)
    case (LTS_Empty q)
    then show ?case by auto
  next
    case (LTS_Step1 q q'' l q')
    then show ?case 
      by (metis LTS_is_reachable.LTS_Step1 insert_iff prod.inject)
  next
    case (LTS_Step2 a \<sigma> q q'' w q')
    then show ?case by auto
  qed


lemma removeExtraConstrans1: "LTS_is_reachable (insert (e1, \<sigma> e2) \<Delta>)  \<Delta>' ini l end \<Longrightarrow> \<forall>q \<sigma>. (q, \<sigma>, e1) \<notin> \<Delta> \<Longrightarrow> \<forall>q. (q, e1) \<notin> \<Delta>' \<Longrightarrow> ini \<noteq> e1 \<Longrightarrow> LTS_is_reachable \<Delta> \<Delta>' ini l end"
      proof (induction rule: LTS_is_reachable.induct)
        case (LTS_Empty q)
        then show ?case apply auto done
      next
        case (LTS_Step1 q q'' l q')
        then show ?case by (metis LTS_is_reachable.LTS_Step1)
      next
        case (LTS_Step2 a \<sigma> q q'' w q')
        then show ?case apply auto done
      qed


lemma removeExtraTrans1: "LTS_is_reachable (\<Delta>1 \<union> \<Delta>2) (\<Delta>1' \<union> \<Delta>2') ini l end \<Longrightarrow> \<Delta>1 = \<Delta>2 \<Longrightarrow> \<Delta>1' = \<Delta>2' \<Longrightarrow> LTS_is_reachable \<Delta>1 \<Delta>1' ini l end "
  by simp

lemma removeExtraTrans2: "LTS_is_reachable (\<Delta>1 \<union> \<Delta>2) (\<Delta>1' \<union> \<Delta>2') ini l end \<Longrightarrow> \<Delta>1 \<noteq> \<Delta>2 \<Longrightarrow> \<Delta>1' = \<Delta>2' \<Longrightarrow> LTS_is_reachable (\<Delta>1 \<union> \<Delta>2) \<Delta>1' ini l end "
  by simp

lemma removeExtraTrans3: "LTS_is_reachable \<Delta>1 (\<Delta>1' \<union> \<Delta>2') ini l end \<Longrightarrow> \<forall>q p \<sigma> n.(q, n) \<in> \<Delta>2' \<and> ((n, \<sigma>, p) \<notin> \<Delta>1 \<or> (n, p) \<notin> \<Delta>1') \<and> \<not> LTS_is_reachable \<Delta>1 \<Delta>2' ini l end
      \<Longrightarrow> LTS_is_reachable \<Delta>1 \<Delta>1' ini l end" 
    proof (induction rule: LTS_is_reachable.induct)
      case (LTS_Empty q)
      then show ?case apply auto done 
    next
      case (LTS_Step1 q q'' l q')
      then show ?case apply auto 
        by (metis Collect_cong Collect_mem_eq LTS_is_reachable.LTS_Step1 Un_insert_right insertI1 insert_absorb surj_pair)
    next
      case (LTS_Step2 a \<sigma> q q'' w q')
      then show ?case apply auto done
    qed


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


lemma insertHeadofTrans2:"LTS_is_reachable d1 d2 p l q \<Longrightarrow> LTS_is_reachable d1 (insert (n, p) d2) n l q"
  by (metis LTS_Step1 Un_insert_right insertI1 subLTSlemma sup.idem)

lemma insertHeadofTrans2None:"LTS_is_reachable d1 d2 p l q \<Longrightarrow> LTS_is_reachable d1 (insert (p, q) d2) p  l q"
  by (metis Un_insert_right subLTSlemma sup.idem)

lemma insertHeadofTrans2None1:"LTS_is_reachable d1 d2 ini l end \<Longrightarrow> LTS_is_reachable d1 (insert (p, q) d2) ini  l end"
  by (metis Un_insert_right subLTSlemma sup.idem)

lemma insertHeadofTrans2None2:"LTS_is_reachable d1 (insert (r1, r2) d2) r1 l end \<Longrightarrow> \<forall>(p, \<sigma>, q) \<in> d1. p \<noteq> r1 \<Longrightarrow> \<forall>(p, q) \<in> d2. p \<noteq> r1 \<Longrightarrow> r1 \<noteq> end \<Longrightarrow> LTS_is_reachable d1 (insert (r1, r2) d2) r2 l end"
proof (induction rule: LTS_is_reachable.induct)
  case (LTS_Empty q)
  then show ?case apply fastforce done
next
  case (LTS_Step1 q q'' l q')
  then show ?case 
    by fastforce
next
  case (LTS_Step2 a \<sigma> q q'' w q')
  then show ?case apply auto done
qed

lemma removeFromAtoEndTrans:"LTS_is_reachable d1 (insert (r1, end) d2) ini l end \<Longrightarrow> l \<noteq> [] \<Longrightarrow> \<forall>(p, \<sigma>, q) \<in> d1. p \<noteq> r1 \<Longrightarrow>  \<forall>(p, \<sigma>, q) \<in> d1. q \<noteq> r1 \<Longrightarrow>
 \<forall>(p, q) \<in> d2. p \<noteq> r1 \<Longrightarrow> \<forall>(p, q) \<in> d2. q \<noteq> r1 \<Longrightarrow>  \<forall>(p, \<sigma>, q) \<in> d1. p \<noteq> r1 \<and> q \<noteq> end \<Longrightarrow> \<forall>(p, q) \<in> d2. (p = end \<and> q = end) \<or> p \<noteq> end \<Longrightarrow>  LTS_is_reachable d1 d2 ini l end"
  sorry

lemma insertHeadofTrans2None3:"LTS_is_reachable d1 (insert (r1, ini) d2) ini l end \<Longrightarrow> \<forall>(p, \<sigma>, q) \<in> d1. p \<noteq> r1 \<Longrightarrow>  \<forall>(p, \<sigma>, q) \<in> d1. q \<noteq> r1 \<Longrightarrow> \<forall>(p, q) \<in> d2. p \<noteq> r1 \<Longrightarrow> \<forall>(p, q) \<in> d2. q \<noteq> r1 \<Longrightarrow> r1 \<noteq> end \<Longrightarrow> LTS_is_reachable d1 d2 ini l end"
  sorry

end