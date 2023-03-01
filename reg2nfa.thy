theory reg2nfa 
  imports AReg NFA
begin

section "definition of nondeterministic finite automaton"

fun ConcatRegexp :: "'v regexp \<Rightarrow> 'v regexp\<Rightarrow> 'v regexp" where
  "ConcatRegexp r1 r2 = Concat r2 r1"

fun ConcatRegexp2 :: "'v regexp \<Rightarrow> 'v regexp\<Rightarrow> 'v regexp" where
  "ConcatRegexp2 r1 r2 = Concat (Concat r2 r1) r1"

fun renameDelta1 :: "('v regexp * 'v set * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp *'v set *'v regexp) set" where 
    "renameDelta1 ss f = {(f q,v, f q')| q v q' . (q, v, q')\<in> ss}"

fun renameDelta2 :: "('v regexp * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp  *'v regexp) set" where  
    "renameDelta2 ss f = {(f q, f q')| q q'.(q, q')\<in> ss}"


inductive_set star_transition :: "(('v regexp × 'v set × 'v regexp) set * 'v regexp * 'v regexp) list set ⇒ (('v regexp × 'v set × 'v regexp) set * 'v regexp * 'v regexp) list set" 
  for r :: "(('v regexp × 'v set × 'v regexp) set * 'v regexp * 'v regexp) list set" where
zero_transition[intro!]:"[] ∈ star_transition r"|
step_transition[intro!]:"x ∈ r ∧ y ∈ star_transition r ⟹ x @ y ∈ star_transition r"


fun concat_transition ::"(('v regexp × 'v set × 'v regexp) set * 'v regexp * 'v regexp) list set \<Rightarrow> (('v regexp × 'v set × 'v regexp) set * 'v regexp * 'v regexp) list set \<Rightarrow> (('v regexp × 'v set × 'v regexp) set * 'v regexp * 'v regexp) list set" where
"concat_transition lset1 lset2 = {x@y| x y. x\<in> lset1 \<and> y\<in>lset2}"


primrec trans2LTS :: "'v regexp ⇒ 'v set ⇒ (('v regexp × 'v set × 'v regexp) set * 'v regexp * 'v regexp) list set"  where
    "trans2LTS (LChr v) alp_set= {[({(LChr v, {v}, \<epsilon>)}, LChr v, \<epsilon>)]}"|
    "trans2LTS (ESet) alp_set= {[({(ESet, {} ,\<epsilon>)},ESet,\<epsilon>)]}"|
    "trans2LTS (\<epsilon>) alp_set = {[({},\<epsilon>,\<epsilon>)]}"|
    "trans2LTS (Dot) alp_set = {[({(Dot, alp_set, \<epsilon>)},Dot,\<epsilon>)]}"|
    "trans2LTS (Alter r1 r2) alp_set = trans2LTS r1 alp_set \<union>  trans2LTS r2 alp_set"|
    "trans2LTS (Concat r1 r2) alp_set = concat_transition (trans2LTS r1 alp_set) (trans2LTS r2 alp_set)" |
    "trans2LTS (Star r) alp_set = star_transition (trans2LTS r alp_set)" |
    "trans2LTS (Ques r) alp_set = {[({(Ques r, {}, \<epsilon>)},Ques r, \<epsilon>)]} \<union> trans2LTS r alp_set"
  
primrec reg2q :: "'v regexp \<Rightarrow> 'v set \<Rightarrow>  ('v regexp) set" where
    "reg2q Dot a = {Dot, \<epsilon>}"|
    "reg2q (LChr p) a =  {(LChr p), \<epsilon>}"|
    "reg2q (Alter r1 r2) a = {(Alter r1 r2)} \<union> reg2q r1 a \<union> reg2q r2 a"|
    "reg2q (Star r) a = {Star r, \<epsilon>} \<union> ConcatRegexp (Star r) ` reg2q r a" |
    (*"reg2q (Plus r) a = {Plus r, \<epsilon>} \<union> ConcatRegexp (Star r)` reg2q r a" |*)
    "reg2q (Ques r) a = {(Ques r)} \<union> reg2q r a" |
    "reg2q ESet a = {ESet, \<epsilon>}" |
    "reg2q \<epsilon> a = {\<epsilon>}" |
    "reg2q (Concat r1 r2) a = ConcatRegexp r2 ` reg2q r1 a \<union> reg2q r2 a"

fun reg2nfa :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> ('v regexp,'v) NFA_rec" where 
    "reg2nfa r a= \<lparr>  \<Q> = reg2q r a,
                  \<Sigma> = alp_reg  r a,
                  \<Delta> = (trans2LTS r a),
                  \<I> ={r}, 
                  \<F> ={\<epsilon>}\<rparr> " 

section "function correctness of transition from regexp expression to  nondeterministic finite automaton"

theorem Completeness_Proof :
  fixes r v  
  assumes a:"v \<noteq> {}"
  shows " \<forall> q\<in> sem_reg r v. q\<in> \<L> (reg2nfa r v)"
proof(induction r)
  case ESet
  then show ?case apply(unfold \<L>_def NFA_accept_def ) by auto
next
  case (LChr x)
  then show ?case apply(unfold \<L>_def NFA_accept_def ) by auto
next
  case (Concat r1 r2)
  then show ?case   apply(unfold \<L>_def NFA_accept_def ) apply auto subgoal for qa q proof -
      assume a1:"∀q∈sem_reg r1 v. ∃x∈trans2LTS r1 v. single_LTS_reachable_by_path q x"
          and a2:"∀q∈sem_reg r2 v. ∃x∈trans2LTS r2 v. single_LTS_reachable_by_path q x"
          and a3:"qa ∈ sem_reg r1 v"
          and a4:"q ∈ sem_reg r2 v"
      show "∃x. (∃xa y. x = xa @ y ∧ xa ∈ trans2LTS r1 v ∧ y ∈ trans2LTS r2 v) ∧ single_LTS_reachable_by_path (qa @ q) x" 
      proof -
        from a1 a3 have c1:"∃x∈trans2LTS r1 v. single_LTS_reachable_by_path qa x"  by auto
        from a2 a4 have c2:"∃x∈trans2LTS r2 v. single_LTS_reachable_by_path q x"  by auto
        from c1 c2 show ?thesis apply auto subgoal for x xa proof -
            assume b1:"x ∈ trans2LTS r1 v" and b2:"single_LTS_reachable_by_path qa x" and b3:"xa ∈ trans2LTS r2 v"
                  and b4:"single_LTS_reachable_by_path q xa"
            have "single_LTS_reachable_by_path (qa @ q) (x @ xa)" using b1 b2 b3 b4 
              by (simp add: concat_lemma)
            then show ?thesis 
              using b1 b3 by blast
          qed
          done
      qed
    qed
    done
next
  case (Alter r1 r2)
  then show ?case apply(unfold \<L>_def NFA_accept_def) by auto
next
  case Dot
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto done
next
  case (Ques r)
  then show ?case apply(unfold \<L>_def NFA_accept_def) by auto 
next
  case (Star r)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto subgoal for q proof -
      assume a1:"∀q∈sem_reg r v. ∃x∈trans2LTS r v. single_LTS_reachable_by_path q x" and a2:"q ∈ star (sem_reg r v)"
      show "∃x∈star_transition (trans2LTS r v). single_LTS_reachable_by_path q x" using a2 a1 proof(induction q)
        case zero
        then show ?case 
          using single_LTS_reachable_by_path.simps(1) by blast
      next
        case (step x y)
        then show ?case apply auto subgoal for xa proof -
            assume b1:"∀q∈sem_reg r v. ∃a∈trans2LTS r v. single_LTS_reachable_by_path q a" and b2:"x ∈ sem_reg r v"
             and b3:"y ∈ star (sem_reg r v)"
             and b4:"xa ∈ star_transition (trans2LTS r v)"
             and b5:"single_LTS_reachable_by_path y xa" 
            show "∃a∈star_transition (trans2LTS r v). single_LTS_reachable_by_path (x @ y) a"
              using b1 concat_lemma step.IH by blast
          qed
          done
      qed
    qed done
next
  case ε
  then show ?case apply(unfold \<L>_def NFA_accept_def) by auto 
qed

theorem Soundness_Proof :
  fixes r v  
  assumes a:"v \<noteq> {}"
  shows " \<forall> q \<in> \<L> (reg2nfa r v). q\<in> sem_reg r v"
proof(induction r)
  case ESet
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto 
    using remdups_adj.cases by force
next
  case (LChr x)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto  by (simp add:LChr_lemma) 
next
  case (Concat r1 r2)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto subgoal for q xa y
    proof -
      assume a1:"∀q. (∃x∈trans2LTS r1 v. single_LTS_reachable_by_path q x) ⟶ q ∈ sem_reg r1 v" and 
            a2:"∀q. (∃x∈trans2LTS r2 v. single_LTS_reachable_by_path q x) ⟶ q ∈ sem_reg r2 v" and 
            a3:"single_LTS_reachable_by_path q (xa @ y)" and 
            a4:"xa ∈ trans2LTS r1 v" and a5:"y ∈ trans2LTS r2 v" 
      show "∃qa p. q = qa @ p ∧ qa ∈ sem_reg r1 v ∧ p ∈ sem_reg r2 v" proof -
      from a3 a4 have c1:"(∃p qa. (q = qa @ p ∧ single_LTS_reachable_by_path qa xa ∧ single_LTS_reachable_by_path p y))" 
        using inverse_concat_lemma by blast 
      from c1 a1 a2 a3 a4 a5 show ?thesis  by blast
    qed
  qed done
next
  case (Alter r1 r2)
  then show ?case  apply(unfold \<L>_def NFA_accept_def) by auto 
next
  case Dot
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply  auto 
    subgoal for q 
      by (smt (verit, ccfv_threshold) LTS_is_reachable.simps(1) LTS_is_reachable.simps(2) Pair_inject assms image_iff regexp.distinct(49) remdups_adj.cases singletonD)
    done
next
  case (Ques r)
  then show ?case apply(unfold \<L>_def NFA_accept_def ) apply auto subgoal for q proof - 
      assume a1:"LTS_is_reachable {(Ques r, {}, ε)} (Ques r) q ε"
      from a1 show ?thesis
        by (smt (verit, del_insts) LTS_is_reachable.simps(2) Pair_inject empty_iff remdups_adj.cases singletonD)
    qed done   
next
  case (Star r)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto subgoal for q x proof -
      assume a1:"∀q. (∃x∈trans2LTS r v. single_LTS_reachable_by_path q x) ⟶ q ∈ sem_reg r v"
        and a2:"x ∈ star_transition (trans2LTS r v)" and a3:"single_LTS_reachable_by_path q x" 
      show "q ∈ star (sem_reg r v)" using a2 a1 a3 proof(induction x)
        case zero_transition
        then show ?case by auto 
      next
        case (step_transition x y)
        then show ?case   apply auto apply(induct y arbitrary:q) 
           apply auto 
           apply (metis append.right_neutral star.step star.zero)
          subgoal for a aa b y q sorry
          done
      qed    
    qed done
next
  case ε
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply  auto
    by (metis LTS_is_reachable.simps(2) empty_iff list.exhaust)
qed

theorem Correctness_Proof : 
fixes r v  
assumes a:"v \<noteq> {}"
shows "\<L> (reg2nfa r v) =  sem_reg r v" 
  apply auto 
  apply (simp add: Soundness_Proof assms)
  by (metis Completeness_Proof assms reg2nfa.simps)
end