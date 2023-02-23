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
    "trans2LTS (\<epsilon>) alp_set = ({}, {})"|
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


fun all_node_in_delta::"'v regexp => 'v set \<Rightarrow> 'v regexp set" where
"all_node_in_delta r v = {q|q \<sigma> p. (q, \<sigma>, p) \<in> fst (trans2LTS r v)}"

fun all_node_in_delta'::"'v regexp => 'v set \<Rightarrow> 'v regexp set" where
"all_node_in_delta' r v = {q|q p. (q, p) \<in> snd (trans2LTS r v)}"



section "function correctness of transition from regexp expression to  nondeterministic finite automaton"

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
    subgoal for r1 r2 apply auto
      by (metis Suc_eq_plus1_left add_Suc_right len_reg.simps(7))
    subgoal for r2 apply auto done
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
    subgoal for r2 r1 apply auto 
      by (metis (no_types, opaque_lifting) Suc_eq_plus1 add.assoc add.commute len_reg.simps(7))
    subgoal for r1 by auto
    done


lemma QuesNotExists: "\<forall>q \<in> reg2q r v. (getType q = t_Ques \<and> len_reg q < len_reg (Ques r)) \<or> getType q \<noteq> t_Ques"   by (induction r) auto 

lemma quesNotInQ: "Ques r \<notin> (reg2q r v)"
  using QuesNotExists using getType.simps(8) by blast

lemma alterNotInTrans1: "Alter r1 r2 \<notin> (reg2q r1 v)"
  using AlterR1NotExists getType.simps(6) by blast

lemma alterNotInTrans2: "Alter r1 r2 \<notin> (reg2q r2 v)"
  using AlterR2NotExists getType.simps(6) by blast

lemma noEndInFirst:"∀σ p. (\<epsilon>, σ, p) ∉ fst (trans2LTS r v)" apply(induction r) by auto 

lemma t1:"∀(q, σ, p) \<in> fst (trans2LTS r v). p \<in> reg2q r v \<and> q \<in> reg2q r v"  by (induct r) auto

lemma t11:"∀(q, σ, p) \<in> fst (trans2LTS r v). p \<in> reg2q r v \<and> p \<in> reg2q r v"   by (induct r) auto

lemma a2:"\<epsilon> \<in> reg2q r v"   by (induct r) auto


lemma a3:"r \<in> reg2q r v"  by (induct r) auto

lemma t2:"∀(q, p) \<in> snd (trans2LTS r v). q \<in> reg2q r v"
proof(induction r)
  case ESet
  then show ?case apply auto done
next
  case (LChr x)
  then show ?case apply auto done
next
  case (Concat r21 r22)
  then show ?case apply auto by (simp add: a2)
next
  case (Alter r21 r22)
  then show ?case apply auto done
next
  case Dot
  then show ?case apply auto done
next
  case (Star r2)
  then show ?case apply auto by (simp add: a2)
next
  case (Ques r2)
  then show ?case apply auto done
next
  case ε
  then show ?case apply auto done
qed

lemma t3:"∀(q, p) \<in> snd (trans2LTS r v). p \<in> reg2q r v"
proof(induction r)
  case ESet
  then show ?case apply auto done
next
  case (LChr x)
  then show ?case apply auto done
next
  case (Concat r1 r2)
  then show ?case apply auto 
    by (simp add: a3)
next
  case (Alter r1 r2)
  then show ?case apply auto  
     apply (simp add: a3)
    by (simp add: a3)
next
  case Dot
  then show ?case apply auto done
next
  case (Star r)
  then show ?case apply auto 
    by (simp add: a3)
next
  case (Ques r)
  then show ?case apply auto 
     apply (simp add: a2)
    by (simp add: a3)
next
  case ε
  then show ?case apply auto done
qed  

lemma t4:"n \<notin> reg2q r v \<Longrightarrow> ∀(q, p) \<in> snd (trans2LTS r v). n \<noteq> q \<and> n \<noteq> p"  using t2 t3 by blast

lemma t5:"n \<notin> reg2q r v \<Longrightarrow> ∀(q, σ, p) \<in> fst (trans2LTS r v). n \<noteq> q \<and> n \<noteq> p" using t2 t3 t1 by fastforce

lemma alterNotExitsInTrans1:"∀q σ. (q, σ, Alter r1 r2) ∉ fst (trans2LTS r1 v)" using alterNotInTrans1 t5 by fastforce

lemma alterNotExitsInTrans2:"∀q σ. (Alter r1 r2, σ, q) ∉ fst (trans2LTS r1 v)"  using alterNotInTrans1 t5 by blast

lemma alterNotExitsInTrans11:"∀q σ. (q, σ, Alter r1 r2) ∉ fst (trans2LTS r2 v)" using alterNotInTrans2 t5  by fastforce

lemma alterNotExitsInTrans12:"∀q σ. (Alter r1 r2, σ, q) ∉ fst (trans2LTS r2 v)" using alterNotInTrans2 t5  by fastforce

lemma alterNotExistsInTrans2:"∀q. (q, Alter r1 r2) ∉ snd (trans2LTS r1 v)"  using alterNotInTrans1 t4 apply auto by blast

lemma alterNotExistsInTrans22:"∀q. (Alter r1 r2, q) ∉ snd (trans2LTS r1 v)" using alterNotInTrans1 t4 apply auto by blast

lemma alterNotExistsInTrans21:"∀q. (q, Alter r1 r2) ∉ snd (trans2LTS r2 v)" using alterNotInTrans2 t4 apply auto by blast

lemma alterNotExistsInTrans23:"∀q. (Alter r1 r2, q) ∉ snd (trans2LTS r2 v)" using alterNotInTrans2 t4 apply auto by blast

lemma alterNotExitsInTrans3:"∀q σ. (q, σ, Alter r1 r2) ∉ fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v)"   using alterNotExitsInTrans1  by (simp add: alterNotExitsInTrans11)

lemma alterNotExistsInTrans4:"∀q. (q, Alter r1 r2) ∉ snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)"   apply (simp add: alterNotExistsInTrans2) by (simp add: alterNotExistsInTrans21)  

lemma QuesNotExistsInTrans1: "\<forall>(q, \<sigma>, p) \<in> fst (trans2LTS r v). q \<noteq> Ques r"  using quesNotInQ t1 by fastforce

lemma QuesNotExistsInTrans11: "\<forall>q \<sigma>. (q, \<sigma>, Ques r) \<notin> fst (trans2LTS r v) "  using quesNotInQ t1 by fastforce

lemma QuesNotExistsInTrans2: "\<forall>(q, p) \<in> snd (trans2LTS r v). q \<noteq> Ques r" using quesNotInQ t2 by blast

lemma QuesNotExistsInTrans3: "\<forall>(q, \<sigma>, p) \<in> fst (trans2LTS r v). p \<noteq> Ques r" using quesNotInQ t11 by fastforce

lemma QuesNotExistsInTrans4: "\<forall>(q, p) \<in> snd (trans2LTS r v). p \<noteq> Ques r"  using quesNotInQ t3 by fastforce

lemma QuesNotExistsInTrans5: "\<forall>p. (p, Ques r)\<notin> snd (trans2LTS r v)"  using quesNotInQ t3 by fastforce

lemma QuesNotExistsInTrans6: "\<forall>(q, \<sigma>, p) \<in> fst (trans2LTS r v). p \<noteq> Ques r \<Longrightarrow> \<forall>p \<sigma>. (p, \<sigma>, Ques r)\<notin> fst (trans2LTS r v)" apply auto done

lemma noStartInSecond:"∀p σ. (p, σ, Ques r) ∉ fst (trans2LTS r v)"   by (simp add: QuesNotExistsInTrans11)

lemma noStartInSecond1 :"∀p. (p, Ques r) ∉ snd (trans2LTS r v)" by (simp add: QuesNotExistsInTrans5)

lemma QuesNotExistsInTrans21: "\<forall>q p.(q, Ques r)\<notin>  snd (trans2LTS r v)"  by (simp add: noStartInSecond1)

lemma aux1:"\<forall>(q, \<sigma>, p) \<in> fst (trans2LTS r v). q \<noteq> \<epsilon>  "
  using noEndInFirst by force

lemma aux2:"\<forall>(q, p) \<in> snd (trans2LTS r v). q \<noteq> \<epsilon>  "
  apply(induction r) apply auto done

lemma empty_transition: "LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) ε l ε \<Longrightarrow> l = []" 
  by (simp add:empty_transtion aux1 aux2)  
 

theorem uniqueInitalState: "\<I> (reg2nfa r v) = {r}"
  apply (induct r)
  by auto

theorem uniqueFinalState:"\<F> (reg2nfa r v) = {\<epsilon>}"
  apply(induct r)
  by auto 

lemma ll1:"\<forall>(q,\<sigma>,p) \<in> fst (trans2LTS r v). q \<noteq> \<epsilon>"
  apply(induction r)
         apply auto done

lemma ll2:"\<forall>(q,p) \<in> snd (trans2LTS r v). q = \<epsilon> \<longrightarrow> p = \<epsilon>" 
  apply(induction r) apply auto done

lemma aux_lemma1 :"LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) ε l q' \<Longrightarrow> q' = \<epsilon>" 
  using ll1 ll2 apply auto apply(induction rule:LTS_is_reachable.induct) 
    apply auto 
  apply (metis (mono_tags, lifting) case_prod_conv) 
  by blast

theorem Completeness_Proof :
  fixes r v  
  assumes a:"v \<noteq> {}"
  shows " \<forall> q\<in> sem_reg r v. q\<in> \<L> (reg2nfa r v)"
proof(induction r)
  case ESet
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto
    by (simp add: LTS_Empty insertHeadofTrans2)
next
  case (LChr x)
  then show ?case apply(unfold \<L>_def NFA_accept_def) by auto 
next
  case (Concat r1 r2)
  then show ?case  apply(unfold \<L>_def NFA_accept_def) apply auto subgoal for qa p proof -
      assume a1:"∀q∈sem_reg r1 v. LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) r1 q ε" and a2:"qa ∈ sem_reg r1 v"
      from a1 a2 have c1:"LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) r1 qa ε" apply auto done
      assume a3:"∀q∈sem_reg r2 v. LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 q ε" and a4:"p ∈ sem_reg r2 v"
      from a3 a4 have c2:"LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 p ε" by auto
      from c1 have c3:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)})
     ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)})
     (Concat r1 r2) qa (Concat ε r2)" by(simp add:DeltLTSlemma1)
      from c3 have t1:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)})
     ((insert (Concat ε r2, r2) {(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)})) (Concat r1 r2) qa (Concat ε r2)" sledgehammer
        by (simp add: insertHeadofTrans2None1)
      have c4:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)})
     ((insert (Concat ε r2, r2) {(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)}))
      (Concat ε r2) [] r2" by (simp add: LTS_Empty insertHeadofTrans2)
      from t1 c4 have c5:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)})
     ((insert (Concat ε r2, r2) {(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)})) (Concat r1 r2) qa r2 "
        using joinLTSlemma by fastforce
    from c5 have c6:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v))
     (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
     (Concat r1 r2) qa r2 " 
      using subLTSlemma by fastforce 
    from c2 have c7:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v))
     (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
     r2 p ε " 
      by (simp add: Un_commute insertHeadofTrans2None1 subLTSlemma)
    from c6 c7 show ?thesis  by (simp add: joinLTSlemma)
  qed
  done
next
  case (Alter r1 r2)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto subgoal for q proof - 
      assume a1:"∀q∈sem_reg r1 v. LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) r1 q ε" and a2:"q ∈ sem_reg r1 v"
      from a1 a2 have c1:"LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) r1 q ε" by auto
      from c1 have c2:"LTS_is_reachable (fst (trans2LTS r1 v)) (insert (Alter r1 r2, r1)  (snd (trans2LTS r1 v))) (Alter r1 r2) q ε" 
        by (simp add: insertHeadofTrans2)
      from c2 show?thesis by (meson c1 insertHeadofTrans2 insertHeadofTrans2None1 subLTSlemma)
    qed
    subgoal for q proof - 
      assume a1:" ∀q∈sem_reg r2 v. LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 q ε" and a2:"q ∈ sem_reg r2 v " 
      from a1 a2 have c1:"LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 q ε" by auto
      from c1 have c2:"LTS_is_reachable (fst (trans2LTS r2 v)) (insert (Alter r1 r2, r2) (snd (trans2LTS r2 v))) (Alter r1 r2) q ε" 
        by (simp add: insertHeadofTrans2)
      from c2 show ?thesis 
        by (metis c1 insertHeadofTrans2 insertHeadofTrans2None1 subLTSlemma sup_commute)
    qed
    done
next
  case Dot
  then show ?case apply(unfold \<L>_def NFA_accept_def) by auto 
next
  case (Star r)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto  subgoal for q proof -
      assume a1:"∀q∈sem_reg r v. LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r q ε" and a2:"q ∈ star (sem_reg r v)" 
     show "LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}
     (insert (Star r, ε)
       (insert (Star r, Concat r (Star r))
         (insert (Concat ε (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)})))
     (Star r) q ε" using a2 proof(induction q)
       case zero
       then show ?case by (simp add: LTS_Empty insertHeadofTrans2)
     next
       case (step x y)
       then show ?case apply auto proof -
         assume t1:"x ∈ sem_reg r v"
         from t1 a1 have c1:"LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r x ε" by auto
         from c1 have t2:"LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}
     {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}
     (Concat r (Star r)) x (Concat ε (Star r))" by(simp add:DeltLTSlemma1)
         from t2 have t3: "LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}
     (insert (Star r, Concat r (Star r)) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)})
      (Star r) x (Concat ε (Star r))"   by (simp add: insertHeadofTrans2)
         from t3 have t4: "LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}
     (insert (Star r, ε)
       (insert (Star r, Concat r (Star r))
         (insert (Concat ε (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))) (Star r) x (Concat ε (Star r))" 
           by (smt (verit, best) insertHeadofTrans2None1 insert_commute)
         from t4 have t5:"LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}
     (insert (Star r, ε)
       (insert (Star r, Concat r (Star r))
         (insert (Concat ε (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))) (Concat ε (Star r)) [] (Star r)" 
           by (meson LTS_is_reachable.simps insert_iff)
         from t4 t5 show ?thesis by (smt (verit, ccfv_SIG) append.right_neutral joinLTSlemma local.step)
       qed
     qed
   qed       
   done
next
  case (Ques r)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto subgoal 
      by (simp add: LTS_Empty insertHeadofTrans2)
    subgoal for q proof - assume a1:"∀q∈sem_reg r v. LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r q ε" and a2:"q ∈ sem_reg r v"
      from a1 a2 have c1:"LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r q ε" by auto
      from c1 have c2:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, r) (snd (trans2LTS r v))) (Ques r) [] r" 
        by (simp add: LTS_Empty insertHeadofTrans2)
      from c1 c2 have c3:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, r) (snd (trans2LTS r v))) (Ques r) q ε" 
        by (simp add: insertHeadofTrans2)
      from c3 show ?thesis 
        by (simp add: insertHeadofTrans2None1)
    qed
    done
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
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto by (simp add: Delta1Empty)
next
  case (LChr x)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto by (smt (verit, ccfv_SIG) LTS_is_reachable.simps empty_iff old.prod.inject regexp.distinct(25) singletonD)
next
  case (Concat r1 r2)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto sorry
next
  case (Alter r1 r2)
  then show ?case subgoal  apply(unfold \<L>_def NFA_accept_def) apply auto 
      subgoal for q proof(rule ccontr) 
        assume a1:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v))
     (insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)))) (Alter r1 r2) q ε"
        from a1 have c1:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v))
     (insert (Alter r1 r2, r1) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))) (Alter r1 r2) q ε \<or> LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v))
     (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))) (Alter r1 r2) q ε"  by (smt (verit) LTS_is_reachable.simps Un_iff alterNotExistsInTrans4 alterNotExitsInTrans3 insert_commute insert_iff old.prod.inject prod.collapse removeExtraConstrans trans2LTS.simps(6))
        assume a2:"q ∉ sem_reg r2 v" and a3:"∀q. LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 q ε ⟶ q ∈ sem_reg r2 v" 
        from a2 a3 have c2:"\<not> LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 q ε" by auto
        assume a4:"q ∉ sem_reg r1 v" and a5:"∀q. LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) r1 q ε ⟶ q ∈ sem_reg r1 v"
        from a4 a5 have c3:"\<not> LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) r1 q ε" by auto
        have c4:"\<not> LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v))
     (insert (Alter r1 r2, r1) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))) (Alter r1 r2) q ε" sorry
        have c5:"\<not> LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v))
     (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))) (Alter r1 r2) q ε" sorry
        from c4 c5 c1 show "False" by auto
      qed
      done
    done
next
  case Dot
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto  by (smt (verit, best) LTS_is_reachable.simps Pair_inject empty_iff image_eqI regexp.distinct(49) singletonD)
next
  case (Star r)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto sorry
next
  case (Ques r)
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto subgoal for q  proof (rule ccontr) 
      assume a1:"q ≠ []" and a2:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, ε) (insert (Ques r, r) (snd (trans2LTS r v)))) (Ques r) q ε"
      have temp : "r \<noteq> Ques r" by auto
      from a1 a2 have c1:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, r) (snd (trans2LTS r v))) (Ques r) q ε"  by (smt (verit) LTS_is_reachable.simps QuesNotExistsInTrans11 QuesNotExistsInTrans5 Un_insert_left empty_transition insert_iff regexp.distinct(55) removeExtraConstrans snd_conv trans2LTS.simps(8))
      from c1 have c2:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, r) (snd (trans2LTS r v))) r q ε" using insertHeadofTrans2None2 apply auto  by (simp add: QuesNotExistsInTrans1 QuesNotExistsInTrans2 insertHeadofTrans2None2)
      from c2 temp have c3:"LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r q ε" by(simp add: removeExtraConstrans QuesNotExistsInTrans11 QuesNotExistsInTrans21)
      assume a3:"∀q. LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r q ε ⟶ q ∈ sem_reg r v" 
      from a3 c3 have c3:"q ∈ sem_reg r v" by auto
      assume a4:"q ∉ sem_reg r v" 
      from c3 a4 show "False" by auto
    qed
    done  
next
  case ε
  then show ?case apply(unfold \<L>_def NFA_accept_def) apply auto by (simp add: Delta1Empty)
qed

theorem Correctness_Proof : 
  fixes r v  
  assumes a:"v \<noteq> {}"
  shows "\<L> (reg2nfa r v) =  sem_reg r v" 
  apply auto 
  apply (simp add: Soundness_Proof assms)
  by (metis Completeness_Proof assms reg2nfa.simps)
(*theorem tranl_aux:
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
  then show ?case 
  proof -
    assume a1:"∀q∈𝒬 (reg2nfa r1 v). sem_reg q v = LQ (reg2nfa r1 v) q" and a2:"∀q∈𝒬 (reg2nfa r2 v). sem_reg q v = LQ (reg2nfa r2 v) q"
    from a1 a2 have c1:"∀q∈ (ConcatRegexp r2 ` reg2q r1 v). sem_reg q v = LQ (reg2nfa (Concat r1 r2) v) q" unfolding LQ_def NFA_accept_Q_def apply auto 
      subgoal for q qa p proof -
        assume b1:"LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) q qa ε"
        from b1 have e1:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)}) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)}) (Concat q r2) qa (Concat ε r2)" by(simp add:DeltLTSlemma1) 
        from e1 have e2:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)}) (insert (Concat ε r2, r2) {(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)}) (Concat q r2) qa r2" proof(induction rule:LTS_is_reachable.induct)
          case (LTS_Empty q)
          then show ?case by (simp add: LTS_is_reachable.LTS_Empty insertHeadofTrans2)
        next
          case (LTS_Step1 q q'' l q')
          then show ?case by (meson LTS_is_reachable.LTS_Step1 insertI2)
        next
          case (LTS_Step2 a σ q q'' w q')
          then show ?case by blast
        qed
        assume b2:"p ∈ sem_reg r2 v" and b3:"∀q∈reg2q r2 v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) q w ε}"
        from b2 b3 have e3:"LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 p ε" using a3 by blast
        from e3 have e4:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v)) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))) r2 p ε" by (simp add: insertHeadofTrans2None1 subLTSlemma sup_commute)
        from e2 have e5:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v)) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))) (Concat q r2) qa r2" using subLTSlemma by fastforce
        from e4 e5 show ?thesis by (simp add: joinLTSlemma)
      qed
      subgoal for q x sorry 
      done
    from a2 have c2:"∀q∈𝒬 (reg2nfa r2 v). sem_reg q v = LQ (reg2nfa (Concat r1 r2) v) q" unfolding LQ_def NFA_accept_Q_def apply auto 
      subgoal for q x by (simp add: Un_commute insertHeadofTrans2None1 subLTSlemma)
      subgoal for q x  sorry
      done
    from c1 c2 show ?thesis by auto
  qed
next
  case (Alter r1 r2) then show ?case (*unfolding LQ_def NFA_accept_Q_def apply auto 
    subgoal for x proof -
      assume a1:"∀q∈reg2q r1 v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) q w ε}" and a2:" x ∈ sem_reg r1 v"
      from a1 a2 have c1:"LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) r1 x ε" using a3 by blast
      from c1 show ?thesis by (simp add: insertHeadofTrans2 insertHeadofTrans2None1 subLTSlemma)
    qed
    subgoal for x proof -
      assume a1:"∀q∈reg2q r2 v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) q w ε}" and a2:"x ∈ sem_reg r2 v"
      from a1 a2 have c1:"LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 x ε" using a3 by blast
      from c1 show ?thesis by (metis insertHeadofTrans2 insertHeadofTrans2None1 subLTSlemma sup.commute)
    qed
    prefer 2 subgoal for q x proof - assume a1:"LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) q x ε" from a1 show ?thesis by (simp add: insertHeadofTrans2None1 subLTSlemma) qed
    prefer 3 subgoal for q x by (metis Un_commute insertHeadofTrans2None1 subLTSlemma)
      prefer 2 SUBGOAL for q x proof -
      assume a1:"q ∈ reg2q r1 v" 
      from a1 have c1:"q \<noteq> Alter r1 r2" using alterNotInTrans1 by blast
      assume a2:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v)) (insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)))) q x ε"
      from c1 a2 have c2:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v)) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)) q x ε" by (metis a3 alterNotExistsInTrans4 alterNotExitsInTrans3 alterNotInTrans2 insertE removeExtraConstrans snd_conv)
      assume a3:"∀q∈reg2q r1 v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) q w ε}"
      from a1 c2 a3 show ?thesis sorry
    qed
    prefer 2 subgoal for q x sorry
    subgoal for x sorry
    done*)
  proof -
    have "𝒬 (reg2nfa (Alter r1 r2) v) = {(Alter r1 r2)} \<union> reg2q r1 v \<union> reg2q r2 v"  by auto
    assume a1:"∀q∈𝒬 (reg2nfa r1 v). sem_reg q v = LQ (reg2nfa r1 v) q" and a2 :"∀q∈𝒬 (reg2nfa r2 v). sem_reg q v = LQ (reg2nfa r2 v) q"
    from a1 a2 have c1:"∀q∈ reg2q r1 v. sem_reg q v = LQ (reg2nfa (Alter r1 r2) v) q" unfolding LQ_def NFA_accept_Q_def apply auto apply (meson insertHeadofTrans2None1 subLTSlemma)
      subgoal for q x proof - assume a1:"q ∈ reg2q r1 v " 
        from a1 have d1:"Alter r1 r2 \<noteq> q" using alterNotInTrans1 by blast
        assume a2:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v)) (insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)))) q x ε"
        from a2 d1 have d2:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v)) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)) q x ε" by (metis a3 alterNotExistsInTrans4 alterNotExitsInTrans3 alterNotInTrans2 insertE removeExtraConstrans snd_conv)
        assume a3:"∀q∈reg2q r1 v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) q w ε}" and a4:"∀q∈reg2q r2 v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) q w ε}"
        from a3 a4 a1 d2 show ?thesis sorry
      qed
      done
    from a1 a2 have c2:"∀q∈ reg2q r2 v. sem_reg q v = LQ (reg2nfa (Alter r1 r2) v) q" unfolding LQ_def NFA_accept_Q_def apply auto apply (metis inf_sup_aci(5) insertHeadofTrans2None1 subLTSlemma)
      subgoal for q x sorry
      done 
    from a1 a2 have c3:"∀q∈ {(Alter r1 r2)}. sem_reg q v = LQ (reg2nfa (Alter r1 r2) v) q" unfolding LQ_def NFA_accept_Q_def apply auto 
      subgoal for x proof - 
        assume b1:"x ∈ sem_reg r1 v" and b2:"∀q∈reg2q r1 v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) q w ε}"
        from b1 b2 have d1:"LTS_is_reachable (fst (trans2LTS r1 v)) (snd (trans2LTS r1 v)) r1 x ε" using a3 by fastforce
        from d1 show ?thesis by (simp add: insertHeadofTrans2 insertHeadofTrans2None1 subLTSlemma)
      qed
      subgoal for x proof -
        assume b1:"∀q∈reg2q r2 v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) q w ε}" and b2:"x ∈ sem_reg r2 v"
        from b1 b2 have d1:"LTS_is_reachable (fst (trans2LTS r2 v)) (snd (trans2LTS r2 v)) r2 x ε" using a3 by fastforce
        from d1 show ?thesis by (metis Un_commute insertHeadofTrans2 insertHeadofTrans2None1 subLTSlemma)
      qed
      subgoal for x sorry
      done
    from c1 c2 c3 show ?thesis by auto
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
  then show ?case unfolding LQ_def NFA_accept_Q_def apply auto
    subgoal for x proof - assume a1:"∀q∈reg2q r v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) q w ε}" and a2:"x ∈ star (sem_reg r v)" 
      show "LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}
     (insert (Star r, ε) (insert (Star r, Concat r (Star r)) (insert (Concat ε (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))) (Star r) x ε" 
      using a2
      proof(induction x)
    case zero
    then show ?case by (simp add: LTS_Empty insertHeadofTrans2)
  next
    case (step x y)
    then show ?case apply auto 
    proof - 
        assume b1:"x ∈ sem_reg r v" and b2:"y ∈ star (sem_reg r v)" and b3:"LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} (insert (Star r, ε) (insert (Star r, Concat r (Star r)) (insert (Concat ε (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))) (Star r) y ε" 
        from b1 a1 have c1:"LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r x ε" using a3 by blast
        have c2:"LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} (insert (Star r, ε) (insert (Star r, Concat r (Star r)) (insert (Concat ε (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))) (Star r) [] ( Concat r (Star r)) " 
          by (meson LTS_Empty insertHeadofTrans2 insertHeadofTrans2None1)
        from c1 have c3:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)}) ({(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})
                      (Concat r (Star r)) x (Concat \<epsilon> (Star r))" by(simp add:DeltLTSlemma1)
        from c3 have c4:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> fst (trans2LTS r v))
                      ({(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})
                      (Concat r (Star r)) x (Concat \<epsilon> (Star r))" by (metis (no_types, lifting) subLTSlemma sup_idem)
        from c4 have c5:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> fst (trans2LTS r v)) 
                       ((insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)}))
                       (Concat r (Star r)) x (Concat \<epsilon> (Star r))" by (meson insertHeadofTrans2None1)
        from c5 have c6:"LTS_is_reachable  ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> fst (trans2LTS r v))
                      ((insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                      (Concat r (Star r)) x (Concat \<epsilon> (Star r))" by (meson insertHeadofTrans2None1)
        have c7:"LTS_is_reachable
                      ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)})
                      (insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                      (Concat r (Star r)) x (Concat \<epsilon> (Star r))" by (simp add: c3 insertHeadofTrans2None1)
        have c8:"LTS_is_reachable
                      ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)})
                      (insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                      (Star r) x (Concat \<epsilon> (Star r))" by (simp add: c3 insertHeadofTrans2 insertHeadofTrans2None1)
        have c9:"LTS_is_reachable
                      ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)})
                      (insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                      (Concat \<epsilon> (Star r)) [] (Star r)" by (simp add: LTS_Empty insertHeadofTrans2 insertHeadofTrans2None1)
        have c10:"LTS_is_reachable
                      ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)})
                      (insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                      (Star r) x (Star r)" using c8 c9 joinLTSlemma by fastforce
        thus ?thesis by (simp add: b3 joinLTSlemma) 
      qed
    qed
  qed
  subgoal for x sorry
  subgoal for x 
  proof - 
    assume a1:"LTS_is_reachable {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}
     (insert (Star r, ε) (insert (Star r, Concat r (Star r)) (insert (Concat ε (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))) ε x ε" 
    from a1 have c1:"LTS_is_reachable (fst (trans2LTS (Star r) v)) (snd (trans2LTS (Star r) v)) \<epsilon> x \<epsilon>" by auto 
    from c1 show ?thesis using empty_transition by blast
  qed
  subgoal for q qa p sorry
  subgoal for q x sorry
  done 
next
  case (Ques r)
  then show ?case unfolding LQ_def NFA_accept_Q_def apply auto
    subgoal by (simp add: LTS_Empty insertHeadofTrans2)
    subgoal for x proof -
      assume a1:"∀q∈reg2q r v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) q w ε}" and 
             a2:"x ∈ sem_reg r v"
      from a1 a2 have c1:"LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r x ε" by (simp add: a3)
      from c1 have c2:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, r) (snd (trans2LTS r v))) (Ques r) x ε" by (simp add: insertHeadofTrans2)
      from c2 show"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, ε) (insert (Ques r, r) (snd (trans2LTS r v)))) (Ques r) x ε"  by (simp add: insertHeadofTrans2None) 
    qed
      prefer 2 subgoal for q x proof -
      assume a1:"LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) q x ε"
      from a1 show "LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, ε) (insert (Ques r, r) (snd (trans2LTS r v)))) q x ε" by (simp add: insertHeadofTrans2None1)
    qed
    subgoal for x  
    proof -
      assume a2:"∀q∈reg2q r v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) q w ε}"
         and a3:"x ∉ sem_reg r v" 
         and a4:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, ε) (insert (Ques r, r) (snd (trans2LTS r v)))) (Ques r) x ε"
      show "x = []" proof (rule ccontr)
        assume a1:"x \<noteq> []"
        from  a4 a1 have c1:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, r) (snd (trans2LTS r v))) (Ques r) x ε" proof (induction rule: LTS_is_reachable.induct)
          case (LTS_Empty q)
          then show ?case apply auto done 
        next
          case (LTS_Step1 q q'' l q')
          then show ?case apply auto subgoal proof -
              assume a1:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, ε) (insert (Ques r, r) (snd (trans2LTS r v)))) ε l q'"
              from a1 have c1:"LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) ε l q'" by (metis QuesNotExistsInTrans5 insertE noStartInSecond quesNotInQ reg2nfa.a3 regexp.distinct(55) removeExtraConstrans snd_conv)
              from c1 have c2:"q' = \<epsilon>" by(simp add:aux_lemma1) 
              from c1 c2 have c3:"l= []"  by (metis empty_iff insertE local.a2 mem_Collect_eq reg2nfa.a2 sem_reg.simps(8))
              assume a2:"l \<noteq>[]"
              from a2 c3 have "False" by auto
              then show?thesis by auto
            qed
            subgoal by (metis QuesNotExistsInTrans5 insertE insertHeadofTrans2 noStartInSecond old.prod.inject removeExtraConstrans)
            subgoal by (smt (verit) LTS_is_reachable.LTS_Step1 QuesNotExistsInTrans5 insertE insertHeadofTrans2None1 noStartInSecond quesNotInQ reg2nfa.a3 removeExtraConstrans snd_conv)
            done
        next
          case (LTS_Step2 a σ q q'' w q')
          then show ?case apply auto by (metis QuesNotExistsInTrans5 insertE insertHeadofTrans2None1 noStartInSecond quesNotInQ reg2nfa.a3 removeExtraConstrans snd_conv)
        qed
        from c1 have c2:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, r) (snd (trans2LTS r v))) r x ε" using insertHeadofTrans2None2 apply auto  by (simp add: QuesNotExistsInTrans1 QuesNotExistsInTrans2 insertHeadofTrans2None2)
        have temp : "r \<noteq> Ques r" by auto
        from c2 temp have c3:"LTS_is_reachable (fst (trans2LTS r v))  (snd (trans2LTS r v)) r x ε" apply(simp add: removeExtraConstrans QuesNotExistsInTrans11 QuesNotExistsInTrans21) done
        from a2 a3 have c4:"\<not> LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) r x ε" by (simp add: reg2nfa.a3)
        from c3 c4 show "False" by auto
      qed        
    qed
    subgoal for q x proof -
      assume a1:" ∀q∈reg2q r v. sem_reg q v = {w. LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) q w ε}"
              and a2:"q ∈ reg2q r v"  and a3:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, ε) (insert (Ques r, r) (snd (trans2LTS r v)))) q x ε"
      from a2 have c1:"Ques r \<notin> reg2q r v" by (simp add: quesNotInQ)
      from c1 a2 have c2:"q \<noteq> Ques r" by auto 
      from a3 c2 have c3:"LTS_is_reachable (fst (trans2LTS r v)) (insert (Ques r, r) (snd (trans2LTS r v))) q x ε" by(simp add: removeExtraConstrans QuesNotExistsInTrans5 QuesNotExistsInTrans3 QuesNotExistsInTrans6) 
      from c2 c3 show "LTS_is_reachable (fst (trans2LTS r v)) (snd (trans2LTS r v)) q x ε"  by(simp add: removeExtraConstrans QuesNotExistsInTrans5 QuesNotExistsInTrans3 QuesNotExistsInTrans6) 
    qed
    done
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
qed*)
end