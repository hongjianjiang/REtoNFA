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

primrec getType :: "'v regexp \<Rightarrow> t_regexp" where 
  "getType (LChr v) = t_LChr"|
  "getType (ESet) = t_ESet"|
  "getType \<epsilon> = t_\<epsilon>"|
  "getType Dot = t_Dot"|
  "getType (Concat r1 r2) = t_Concat"|
  "getType (Alter r1 r2) = t_Alter"|
  "getType (Star r) = t_Star"|
  (*"getType (Plus r) = t_Plus"|*)
  "getType (Ques r) = t_Ques"

primrec len_reg :: "'v regexp \<Rightarrow> nat" where
  "len_reg (LChr v) = 1"|
  "len_reg (ESet) = 1"|
  "len_reg \<epsilon> = 1"|
  "len_reg Dot = 1"|
  "len_reg (Concat r1 r2) = 1+ len_reg r1 + len_reg r2"|
  "len_reg (Alter r1 r2) = 1 + len_reg r1 + len_reg r2"|
  "len_reg (Star r) = 1 + len_reg r"|
  (*"len_reg (Plus r) = 1 + len_reg r"|*)
  "len_reg (Ques r) = 1 + len_reg r"

primrec trans2LTS :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> ('v regexp \<times> 'v set \<times> 'v regexp) set * ('v regexp * 'v regexp) set" where 
    "trans2LTS (LChr v) alp_set= ({(LChr v, {v}, \<epsilon>)}, {})"|
    "trans2LTS (ESet) alp_set= ({}, {(ESet, \<epsilon>)})"|
    "trans2LTS (\<epsilon>) alp_set = ({}, {(\<epsilon>, \<epsilon>)})"|
    "trans2LTS (Dot) alp_set = ({(Dot, alp_set, \<epsilon>)},{})"|
    "trans2LTS (Concat r1 r2) alp_set =(renameDelta1 (fst (trans2LTS r1 alp_set)) (ConcatRegexp r2) \<union> 
                                        (fst (trans2LTS r2 alp_set)),
                                        (renameDelta2 (snd (trans2LTS r1 alp_set)) (ConcatRegexp r2) \<union> 
                                        {(Concat \<epsilon> r2, r2)}  \<union> 
                                        snd (trans2LTS r2 alp_set)))"|
    "trans2LTS (Alter r1 r2) alp_set = (fst (trans2LTS r1 alp_set) \<union> 
                                        fst (trans2LTS r2 alp_set), 
                                        snd (trans2LTS r1 alp_set) \<union> 
                                        snd (trans2LTS r2 alp_set) \<union> 
                                        {(Alter r1 r2, r1),(Alter r1 r2, r2)})"|
    "trans2LTS (Star r) alp_set = (renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r)), 
                                  (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r))) \<union> 
                                  {(Star r, \<epsilon>),(Star r,Concat r (Star r)), (Concat \<epsilon> (Star r), Star r)})"|
    (*"trans2LTS (Plus r) alp_set = ((renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r))), 
                                  {(Plus r, Concat r (Star r)),  ((Concat \<epsilon> (Star r)), (Star r)),((Star r), \<epsilon>)} \<union> 
                                  (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r))))"|*)
    "trans2LTS (Ques r) alp_set = (fst (trans2LTS r alp_set), {(Ques r, \<epsilon>), (Ques r, r)} \<union> 
                                  snd (trans2LTS r alp_set))"


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
                  \<Delta> = fst (trans2LTS r a),
                  \<Delta>' = snd (trans2LTS r a),
                  \<I> ={r}, 
                  \<F> ={\<epsilon>}\<rparr> " 

definition LQ :: "('q, 'a) NFA_rec => 'q \<Rightarrow> 'a list set" where 
 "LQ 𝒜 q = {w. NFA_accept_Q 𝒜 q w}"

section "function correctness of transition from regexp expression to  nondeterministic finite automaton"

lemma " q \<notin> getPrefixFromDelta1 trans1 \<Longrightarrow> q \<notin> getPrefixFromDelta2 trans2  \<Longrightarrow> x \<noteq> [] \<Longrightarrow> q \<noteq> p \<Longrightarrow> \<forall>x. \<not> LTS_is_reachable trans1 trans2 q x p"
  apply auto 
  by (metis LTS_is_reachable.simps)

lemma [simp]:"0 < len_reg r" 
  by (induct r) auto

lemma [simp]:"finite (reg2q q v)"  by(induction q) auto

lemma AlterR1NotExists: "\<forall>q \<in> reg2q r1 v. (getType q = t_Alter \<and> len_reg q \<noteq> len_reg (Alter r1 r2)) \<or> getType q \<noteq> t_Alter"
    apply (induction r1 arbitrary:r2) 
    apply simp apply simp subgoal for r21 r22 r1 apply auto 
    by (smt (verit, del_insts) Suc_eq_plus1 add.commute add.left_commute len_reg.simps(6))
    subgoal for r11 r12 r2 apply auto 
    apply (metis (no_types, opaque_lifting) Suc_eq_plus1 add.assoc add.commute len_reg.simps(6))
    by (smt (verit) Suc_eq_plus1 add.assoc add.commute len_reg.simps(6))
    subgoal for r1 by auto
    subgoal for r2 r1 by auto
    subgoal for r2 r1 by auto
    subgoal for r2 r1 apply auto 
    by (metis (no_types, opaque_lifting) Suc_eq_plus1 add.assoc add.commute len_reg.simps(7))
    subgoal for r1 by auto
  done
  
lemma AlterR2NotExists: "\<forall>q \<in> reg2q r2 v. (getType q = t_Alter \<and> len_reg q \<noteq> len_reg (Alter r1 r2)) \<or> getType q \<noteq> t_Alter"
    apply (induction r2 arbitrary:r1) 
    apply simp apply simp subgoal for r21 r22 r1 apply auto 
      by (smt (verit, ccfv_SIG) Suc_eq_plus1 add.assoc add.commute len_reg.simps(6))
    subgoal for r21 r22 r1 apply auto 
      apply (smt (verit) Suc_eq_plus1 add.assoc add.commute len_reg.simps(5)) 
      by (metis add.assoc len_reg.simps(6) mult_1 mult_Suc_right)
    subgoal for r1 by auto
    subgoal for r2 r1 by auto
    subgoal for r2 r1 by auto
    subgoal for r2 r1 apply auto 
      by (metis (no_types, opaque_lifting) Suc_eq_plus1 add.assoc add.commute len_reg.simps(7))
    subgoal for r1 by auto
    done

lemma alterNotInTrans1: "Alter r1 r2 \<notin> (reg2q r1 v)"
  using AlterR1NotExists getType.simps(6) by blast

lemma alterNotInTrans2: "Alter r1 r2 \<notin> (reg2q r2 v)"
  using AlterR2NotExists getType.simps(6) by blast

theorem uniqueInitalState: "\<I> (reg2nfa r v) = {r}"
  apply (induct r)
  by auto

theorem uniqueFinalState:"\<F> (reg2nfa r v) = {\<epsilon>}"
  apply(induct r)
  by auto 


theorem tranl_aux:
  fixes r v 
  shows "\<forall>q \<in> \<Q> (reg2nfa r v).sem_reg q v = LQ (reg2nfa r v) q"
proof(induction r)
case ESet
  then show ?case  apply(unfold LQ_def NFA_accept_Q_def ) apply auto subgoal 
      by (meson LTS_Empty LTS_Step1 singletonI) 
    prefer 2 subgoal for x 
      by (simp add: Delta1Empty)
    subgoal for x
      by (simp add: Delta1Empty)
    done
next
  case (LChr x)
  then show ?case  
    apply(unfold LQ_def NFA_accept_Q_def ) apply auto 
    subgoal for xa 
      apply(rule LTS_is_reachable.cases)  
         apply auto 
      subgoal for w 
      proof - 
        assume "LTS_is_reachable {(LChr x, {x}, ε)} {} ε w ε" 
        then show "w = []"
          apply(rule LTS_is_reachable.cases)
            apply auto
          done
      qed
      done
    subgoal for xa          
      apply(rule LTS_is_reachable.cases)
      by auto
    done
next
  case (Concat r1 r2)
  then show ?case  apply(unfold LQ_def NFA_accept_Q_def ) apply auto prefer 3
    subgoal for q x 
      by (metis (no_types, lifting) Un_commute Un_insert_right subLTSlemma)
      prefer 3
    subgoal for q x
      sorry
    sorry
next
  case (Alter r1 r2)
  fix r1 r2 
  assume a1:"∀q∈𝒬 (reg2nfa r1 v). sem_reg q v = LQ (reg2nfa r1 v) q"   and 
         a2:"∀q∈𝒬 (reg2nfa r2 v). sem_reg q v = LQ (reg2nfa r2 v) q"
  show "∀q∈𝒬 (reg2nfa (Alter r1 r2) v). sem_reg q v = LQ (reg2nfa (Alter r1 r2) v) q" 
  proof - 
  from a1 have c1:"∀q∈𝒬 (reg2nfa r1 v). sem_reg q v = LQ (reg2nfa (Alter r1 r2) v) q" 
    apply (simp del: reg2nfa.simps)
  proof  
    fix q  
    assume a1:"∀q∈𝒬 (reg2nfa r1 v). sem_reg q v = LQ (reg2nfa r1 v) q" and a2:"q ∈ 𝒬 (reg2nfa r1 v)"
    from a1 a2 show "LQ (reg2nfa r1 v) q = LQ (reg2nfa (Alter r1 r2) v) q" 
      apply auto 
      subgoal for x 
        proof -
        assume "x ∈ LQ ⦇𝒬 = reg2q r1 v, Σ = alp_reg r1 v, Δ = fst (trans2LTS r1 v), Δ' = snd (trans2LTS r1 v), ℐ = {r1}, ℱ = {ε}⦈ q"
        then have c1:"LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) q x ε " 
          apply(unfold LQ_def NFA_accept_Q_def) by auto
        from c1 show ?thesis unfolding LQ_def NFA_accept_Q_def  apply simp
          by (metis Un_insert_right subLTSlemma)
        qed
      subgoal for x 
        proof -
          assume a1: "x ∈ LQ ⦇𝒬 = insert (Alter r1 r2) (reg2q r1 v ∪ reg2q r2 v), Σ = alp_reg r1 v ∪ alp_reg r2 v,
               Δ = fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v),
               Δ' = insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))),
               ℐ = {Alter r1 r2}, ℱ = {ε}⦈  q" and a2:"q ∈ reg2q r1 v"
          then have c1:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v)) (insert (Alter r1 r2, r1) 
                        (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)))) q x ε"
            apply(unfold LQ_def NFA_accept_Q_def) by auto
          from c1 a2 have "LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v))
                          (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)) q x ε"     
            sorry
          then show "x ∈ LQ ⦇𝒬 = reg2q r1 v, Σ = alp_reg r1 v, Δ = fst (trans2LTS r1 v), Δ' = snd (trans2LTS r1 v), ℐ = {r1}, ℱ = {ε}⦈ q"
            sorry
        qed
      done
  qed
  from a2 have c2:"∀q∈𝒬 (reg2nfa r1 v). sem_reg q v = LQ (reg2nfa (Alter r1 r2) v) q"
    apply(unfold LQ_def NFA_accept_Q_def ) apply auto 
    subgoal for q x sorry
    subgoal for q x sorry
    done
  have c3:"sem_reg (Alter r1 r2) v = LQ (reg2nfa (Alter r1 r2) v) (Alter r1 r2)" sorry
  have "q ∈ 𝒬 (reg2nfa (Alter r1 r2) v) \<Longrightarrow> q ∈ 𝒬 (reg2nfa r1  v) "
  show ?thesis using c1 c2 c3 
qed
next
  case Dot
  then show ?case   
    apply(unfold LQ_def NFA_accept_Q_def ) 
    apply auto 
    subgoal for x 
    apply(simp add:image_iff)
    apply (rule LTS_is_reachable.cases)
    apply auto
    subgoal for a w
    proof - 
      assume "LTS_is_reachable {(Dot, v, ε)} {} ε w ε" 
      then show "w = []"
        apply(rule LTS_is_reachable.cases)
          apply auto
        done
    qed
    done
    subgoal for x
    apply(rule LTS_is_reachable.cases)
    by auto
    done
next
  case (Star r)
  then show ?case sorry
next
  case (Ques r)
  then show ?case sorry
next
  case ε
  then show ?case apply (unfold LQ_def NFA_accept_Q_def) 
    apply auto 
    subgoal for x 
    proof (induction x)
      case Nil
      then show ?case by auto
    next
      case (Cons a x)
      then show ?case 
      apply auto 
      apply(rule LTS_is_reachable.cases)  
      apply auto 
      by (meson Delta1Empty list.discI)
    qed      
   done    
qed


end