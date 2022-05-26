theory reg2nfa 
  imports AReg NFA
begin


fun ConcatState::"'v regexp \<Rightarrow> 'v regexp\<Rightarrow> 'v regexp" where
  "ConcatState r1 r2 = Concat r2 r1"

fun renameState :: "('v regexp * 'v set * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp *'v set *'v regexp) set" where 
    "renameState ss f = (\<lambda>(q,v,q'). (f q, v, f q')) ` ss"

fun renameState1 :: "('v regexp * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp  *'v regexp) set" where  
    "renameState1 ss f = (\<lambda>(q,q'). (f q, f q')) ` ss"

inductive_set Delta1_State :: " ('v regexp * 'v set * 'v regexp) set \<Rightarrow> 'v regexp \<Rightarrow> ('v regexp * 'v set * 'v regexp) set" 
  for tr :: "('v regexp * 'v set * 'v regexp) set" and r::"'v regexp" 
  where
  Node2Del1:"x \<in> tr \<Longrightarrow> x \<in> (Delta1_State tr r)" |(* a \<rightarrow> \<epsilon>*)
  StepDel1:"x \<in> Delta1_State tr r \<Longrightarrow> (Concat (fst x) (Star r), fst (snd x), Concat (snd (snd x)) (Star r)) ∈ Delta1_State tr r"


inductive_set Delta2_State :: " ('v regexp  * 'v regexp) set \<Rightarrow> 'v regexp \<Rightarrow> ('v regexp  * 'v regexp) set" 
  for tr :: "('v regexp * 'v regexp) set" and r::"'v regexp" 
  where 
  Node2Del2:"x \<in> tr \<Longrightarrow> x \<in> (Delta2_State tr r)" |
  StepDel2:"x \<in> Delta2_State tr r \<Longrightarrow> (Concat (fst x) (Star r), Concat (snd x) (Star r)) ∈ Delta2_State tr r"


inductive_set Node_State :: "'v regexp set \<Rightarrow> 'v regexp \<Rightarrow> 'v regexp set" 
  for tr :: "('v regexp) set" and r::"'v regexp" 
  where
  Node2Star:"x \<in> tr \<Longrightarrow> x \<in> (Node_State tr r)" |
  StepStar:"x \<in> Node_State tr r \<Longrightarrow> Concat x r ∈ Node_State tr r"

primrec trans2Del1 :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> (('v regexp × 'v set × 'v regexp) set * ('v regexp * 'v regexp) set)" where 
    "trans2Del1 (LChr v) alp_set= ({(LChr v,{v},\<epsilon>)},{})"|
    "trans2Del1 (ESet) alp_set= ({(ESet,{},\<epsilon>)},{})"|
    "trans2Del1 (\<epsilon>) alp_set = ({},{(\<epsilon>,\<epsilon>)})"|
    "trans2Del1 (Dot) alp_set = ({(Dot ,alp_set, \<epsilon>)},{})"|
    "trans2Del1 (Concat r1 r2) alp_set =((renameState (fst (trans2Del1 r1 alp_set)) (ConcatState r2)) \<union> (fst (trans2Del1 r2 alp_set)),
                                        {(Concat r1 r2, r1),(Concat \<epsilon> r2, r2)} \<union> renameState1 (snd (trans2Del1 r1 alp_set)) (ConcatState r2) \<union> snd (trans2Del1 r2 alp_set))"|
    "trans2Del1 (Alter r1 r2) alp_set = (fst (trans2Del1 r1 alp_set) \<union> fst (trans2Del1 r2 alp_set), 
                                        snd (trans2Del1 r1 alp_set) \<union> snd (trans2Del1 r2 alp_set) \<union> {(Alter r1 r2, r1),(Alter r1 r2, r2)})"|
    "trans2Del1 (Star r) alp_set = (Delta1_State (fst (trans2Del1 r alp_set)) r, 
                                    Delta2_State (snd (trans2Del1 r alp_set) \<union> {(Star r, \<epsilon>), (Star r, r)}) (Star r))"|
    "trans2Del1 (Plus r) alp_set = (Delta1_State ((renameState (fst (trans2Del1 r alp_set)) (ConcatState (Star r))) \<union> Delta1_State (fst (trans2Del1 r alp_set)) r) r,
                                    Delta2_State (snd (trans2Del1 r alp_set) \<union> {(Plus r, r), (Star r, \<epsilon>), (Star r, r)}) (Star r))"|
    "trans2Del1 (Ques r) alp_set = (fst (trans2Del1 r alp_set),
                                   {(Ques r,\<epsilon>), (Ques r, r)} \<union> snd (trans2Del1 r alp_set))"

primrec reg2lts :: "'v regexp \<Rightarrow> 'v set\<Rightarrow>  ((('v regexp, 'v) LTS) * ('v regexp * 'v regexp) set)" where
    "reg2lts Dot a = trans2Del1 Dot a"|
    "reg2lts (LChr p) a = trans2Del1 (LChr p) a"|
    "reg2lts (r1||r2) a = trans2Del1 (r1||r2) a"|
    "reg2lts (Star r) a = trans2Del1 (Star r) a" |
    "reg2lts (r+) a = trans2Del1 (r+) a" | 
    "reg2lts (r?) a = trans2Del1 (r?) a" |
    "reg2lts (\<epsilon>) a = trans2Del1 (\<epsilon>) a"|
    "reg2lts ESet a = trans2Del1 ESet a"|
    "reg2lts (Concat r1 r2) a = trans2Del1 (Concat r1 r2) a"

primrec reg2q :: "'v regexp \<Rightarrow> 'v set\<Rightarrow>  ('v regexp) set" where
    "reg2q Dot a = {Dot, \<epsilon>}"|
    "reg2q (LChr p) a =  {(LChr p), \<epsilon>}"|
    "reg2q (r1||r2) a = {(r1||r2),\<epsilon>} \<union> reg2q r1 a \<union> reg2q r2 a"|
    "reg2q (Star r) a = Node_State (reg2q r a) (Star r)" |
    "reg2q (r+) a =  Node_State (reg2q r a) (Star r) \<union> {r}" |
    "reg2q (r?) a = {(Ques r), \<epsilon>} \<union> reg2q r a" |
    "reg2q ESet a = {ESet, \<epsilon>}"|
    "reg2q \<epsilon> a = {\<epsilon>}"|
    "reg2q (Concat r1 r2) a = {Concat r1 r2, r1, r2, \<epsilon>, (Concat \<epsilon> r2)}"


primrec reg2nfa :: "'v regexp \<Rightarrow> 'v set\<Rightarrow> ('v regexp,'v) NFA_rec" where 
    "reg2nfa (Concat r1 r2) a= \<lparr> 
                  \<Q> = reg2q (Concat r1 r2) a,
                  \<Sigma> = alp_reg  (Concat r1 r2) a,
                  \<Delta> = fst (reg2lts  (Concat r1 r2) a),
                  \<Delta>' = snd (reg2lts  (Concat r1 r2) a),
                  \<I> ={(Concat r1 r2)}, 
                  \<F> ={\<epsilon>}\<rparr> " |
    "reg2nfa (ESet) a= \<lparr>
                  \<Q> = reg2q ESet a,
                  \<Sigma> = alp_reg (ESet) a,
                  \<Delta> = fst (reg2lts (ESet) a),
                  \<Delta>' = snd (reg2lts (ESet) a),
                  \<I> = {ESet}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (\<epsilon>) a= \<lparr>
                  \<Q> = reg2q \<epsilon> a,
                  \<Sigma> = alp_reg (\<epsilon>) a,
                  \<Delta> = fst (reg2lts (\<epsilon>) a),
                  \<Delta>' = snd (reg2lts (\<epsilon>) a),
                  \<I> = {\<epsilon>}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Dot) a= \<lparr> 
                  \<Q> = reg2q (Dot) a,
                  \<Sigma> = alp_reg (Dot) a,
                  \<Delta> = fst (reg2lts (Dot) a),
                  \<Delta>' = snd (reg2lts (Dot) a),
                  \<I> = {Dot}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (LChr v) a=  \<lparr> 
                  \<Q> = reg2q (LChr v) a,
                  \<Sigma> = alp_reg (LChr v) a,
                  \<Delta> = fst (reg2lts (LChr v) a),
                  \<Delta>' = snd (reg2lts (LChr v) a),
                  \<I> = {(LChr v)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (r1||r2) a =  \<lparr> 
                  \<Q> = reg2q (r1||r2) a,
                  \<Sigma> = alp_reg (r1||r2) a,
                  \<Delta> = fst (reg2lts (r1||r2) a),
                  \<Delta>' = snd (reg2lts (r1||r2) a),
                  \<I> = {(Alter r1 r2)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Star r) a = \<lparr> 
                  \<Q> = reg2q  (Star r) a,
                  \<Sigma> = alp_reg (Star r) a,
                  \<Delta> = fst (reg2lts (Star r) a),
                  \<Delta>' = snd (reg2lts (Star r) a),
                  \<I> = {(Star r)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (r+) a= \<lparr> 
                  \<Q> = reg2q  (r+) a,
                  \<Sigma> = alp_reg (r+) a,
                  \<Delta> = fst (reg2lts  (r+) a),
                  \<Delta>' = snd (reg2lts  (r+) a),
                  \<I> = {(Plus r)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (r?) a = \<lparr> 
                  \<Q> = reg2q  (r?) a,
                  \<Sigma> = alp_reg (r?) a,
                  \<Delta> = fst (reg2lts  (r?) a),
                  \<Delta>' = snd (reg2lts  (r?) a),
                  \<I> = {(Ques r)}, 
                  \<F> = {\<epsilon>}\<rparr> " 


lemma transEqDel : "fst (trans2Del1 r1 v) = Δ (reg2nfa r1 v)"
  apply (induct r1)
  apply auto
  done


lemma InitState:"q ∈ ℐ (reg2nfa r1 v) \<Longrightarrow> q = (r1)"
  apply (induct r1)
  by auto

lemma FinalState:"xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> xa = \<epsilon>"
  apply (induct r1)
  by auto

lemma initalSet:"ℐ (reg2nfa r1 v) = {r1}"
  apply (induct r1)
  apply auto
  done

lemma finalSet:"ℱ (reg2nfa r1 v) = {\<epsilon>}"
  apply(induct r1)
  apply auto
  done


lemma trans2Del :"fst (trans2Del1 r v) =(Δ (reg2nfa r v))"
  by (simp add: transEqDel)

theorem tranl_eq :
  fixes r v  
  shows l1: "sem_reg r v = \<L> (reg2nfa r v)"
proof(induct r)
case ESet
  then show ?case 
    apply (unfold \<L>_def NFA_accept_def)
    apply auto
    by (smt (verit, best) LTS_is_reachable.simps(1) LTS_is_reachable.simps(2) Pair_inject empty_iff list.exhaust regexp.distinct(15) singletonD)
next
    case (LChr x)
    then show ?case     
      apply( unfold \<L>_def NFA_accept_def)
      apply auto
      by (smt (z3) LTS_is_reachable.simps(1) LTS_is_reachable.simps(2) old.prod.inject regexp.distinct(29) remdups_adj.cases singletonD)
next
  case Dot
  then show ?case 
    apply (unfold \<L>_def  NFA_accept_def)
    apply auto
    subgoal for x 
      apply(induct x)
       apply auto
sledgehammer
   
next
  case (Alter r1 r2)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for x q xa
    proof -
      assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}"
      assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x}"
      assume a3:"q ∈ ℐ (reg2nfa r1 v)"
      assume a4:"xa ∈ ℱ (reg2nfa r1 v)"
      assume a5:"LTS_is_reachable (Δ (reg2nfa r1 v)) q x xa"
      then show "LTS_is_reachable (insert (Node (r1 || r2), {}, Node r1) (insert (Node (r1 || r2), {}, Node r2) (trans2Del1 r1 v ∪ trans2Del1 r2 v))) (Node (r1 || r2)) x ε"
      proof -
         have c1:"q = Node r1" 
           using InitState a3 by blast
         have c2:"xa =\<epsilon>"
           using FinalState a4 by blast
         have c3:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) x \<epsilon>"
           using a5 c1 c2 by blast
         have c4:"LTS_is_reachable (Δ (reg2nfa (Alter r1 r2) v)) (Node (Alter r1 r2)) [] (Node r1)"
           apply auto
           by (meson LTS_Empty LTS_Epi1 insertI1)
         have c5:"LTS_is_reachable (Δ (reg2nfa (Alter r1 r2) v)) (Node (Alter r1 r2)) x \<epsilon>"
           apply auto
           by (metis LTS_Epi1 Un_insert_right c3 insertI1 subLTSlemma trans2Del)
         then show "LTS_is_reachable (insert (Node (r1 || r2), {}, Node r1) (insert (Node (r1 || r2), {}, Node r2) (trans2Del1 r1 v ∪ trans2Del1 r2 v))) (Node (r1 || r2)) x ε"
           by force
       qed
     qed
     subgoal for x q xa
      proof -
      assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}"
      assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x}"
      assume a3:"q ∈ ℐ (reg2nfa r2 v)"
      assume a4:"xa ∈ ℱ (reg2nfa r2 v)"
      assume a5:"LTS_is_reachable (Δ (reg2nfa r2 v)) q x xa"
      then show "LTS_is_reachable (insert (Node (r1 || r2), {}, Node r1) (insert (Node (r1 || r2), {}, Node r2) (trans2Del1 r1 v ∪ trans2Del1 r2 v))) (Node (r1 || r2)) x ε"
      proof -
         have c1:"q = Node r2" 
           using InitState a3 by blast
         have c2:"xa =\<epsilon>"
           using FinalState a4 by blast
         have c3:"LTS_is_reachable (Δ (reg2nfa r2 v)) (Node r2) x \<epsilon>"
           using a5 c1 c2 by blast
         have c4:"LTS_is_reachable (Δ (reg2nfa (Alter r1 r2) v)) (Node (Alter r1 r2)) [] (Node r1)"
           apply auto
           by (meson LTS_Empty LTS_Epi1 insertI1)
         have c5:"LTS_is_reachable (Δ (reg2nfa (Alter r1 r2) v)) (Node (Alter r1 r2)) x \<epsilon>"
           apply auto
           by (metis LTS_Epi1 c3 inf_sup_aci(5) insertI1 insert_is_Un subLTSlemma transEqDel)
         then show "LTS_is_reachable (insert (Node (r1 || r2), {}, Node r1) (insert (Node (r1 || r2), {}, Node r2) (trans2Del1 r1 v ∪ trans2Del1 r2 v))) (Node (r1 || r2)) x ε"
           by force
       qed
     qed
     subgoal for x
     proof -
       assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}"
       assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x}"
       assume a3:"LTS_is_reachable (insert (Node (r1 || r2), {}, Node r1) (insert (Node (r1 || r2), {}, Node r2) (trans2Del1 r1 v ∪ trans2Del1 r2 v))) (Node (r1 || r2)) x ε"
       assume a4:"∀q∈ℐ (reg2nfa r2 v). ∀xa∈ℱ (reg2nfa r2 v). ¬ LTS_is_reachable (Δ (reg2nfa r2 v)) q x xa"
       show "∃q∈ℐ (reg2nfa r1 v). ∃xa∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q x xa"
       proof -
         have c1: "LTS_is_reachable  (Δ (reg2nfa (Alter r1 r2) v)) (Node (r1 || r2)) x ε"
           using a3 by force
         have c2: "LTS_is_reachable (Δ (reg2nfa (Alter r1 r2) v)) (Node (r1 || r2)) [] (Node r2)"
           by (metis LTS_Empty LTS_Epi1 Un_insert_right insertI1 insertI2 reg2lts.simps(3) reg2nfa.simps(5) simps(3) trans2Del1.simps(5))
         have c3: "LTS_is_reachable (Δ (reg2nfa (Alter r1 r2) v)) (Node (r1 || r2)) [] (Node r1)"
           by (metis LTS_Empty LTS_Epi1 Un_insert_right insertI1 reg2lts.simps(3) reg2nfa.simps(5) simps(3) trans2Del1.simps(5))
         have c4:"¬ LTS_is_reachable (Δ (reg2nfa r2 v)) (Node r2) x \<epsilon>"
           by (simp add: a4 finalSet initalSet)
         have c5:"LTS_is_reachable (Δ (reg2nfa r1 v) \<union> Δ (reg2nfa r2 v) \<union> {(Node (Alter r1 r2),{}, Node r1)} \<union>{(Node (Alter r1 r2),{}, Node r2)} ) (Node (r1||r2)) x \<epsilon>"
           by (metis Un_empty_right Un_insert_right a3 insert_commute trans2Del)
         have c6:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) x \<epsilon>"
           using c1 c2 c3 c4 c5  apply auto
           apply(erule LTS_is_reachable.induct)
           apply auto 
           subgoal for q 
             sorry
           subgoal for a q Δ' w q' q'' σ
             sorry
           done
           show c7:"∃q∈ℐ (reg2nfa r1 v). ∃xa∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q x xa"
             using c6 finalSet initalSet by blast
         qed
       qed
     done
 next
  case (Concat r1 r2)
  then show ?case 
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for a b q xa qa xb 
    proof -
    assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}"
    assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x}"
    assume a3:"q ∈ ℐ (reg2nfa r1 v)"
    assume a4:"xa ∈ ℱ (reg2nfa r1 v)"
    assume a5:"LTS_is_reachable (Δ (reg2nfa r1 v)) q a xa "
    assume a6:"qa ∈ ℐ (reg2nfa r2 v)"
    assume a7:"xb ∈ ℱ (reg2nfa r2 v)"
    assume a8:"LTS_is_reachable (Δ (reg2nfa r2 v)) qa b xb"
    from a3 have c1:"q = Node r1" 
      using InitState by blast
    from a4 have c2:"xa = \<epsilon>" 
      using FinalState by blast
    from c1 c2 a5 have c3:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) a \<epsilon>" 
      by blast
    from a6 have c4: "qa = Node r2" 
      using InitState by blast
    from a7 have c5: "xb = \<epsilon>"
      using FinalState by blast 
    from c4 c5 a8 have c6: "LTS_is_reachable (Δ (reg2nfa r2 v)) (Node r2) b \<epsilon>" 
      by blast
    from c3 c6 have c7:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (Node (Concat r1 r2)) (a @ b) ε" apply auto
    proof -
      assume b1:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) a ε"
      assume b2:"LTS_is_reachable (Δ (reg2nfa r2 v)) (Node r2) b ε"
      have e1:"LTS_is_reachable (trans2Del1 r1 v) (Node r1) a ε" 
        by (simp add: c3 transEqDel)
      have e2:"LTS_is_reachable (trans2Del1 r2 v) (Node r2) b ε"
        by (simp add: b2 transEqDel)
      from e1 e2 have e3:"LTS_is_reachable (insert (state.Pair ε (Node r2), {}, Node r2) ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)) (state.Pair (Node r1) (Node r2)) (a) (state.Pair ε (Node r2))"
         proof (induction rule: LTS_is_reachable.induct)
           case (LTS_Empty Δ q)
           then show ?case 
             by (simp add: LTS_is_reachable.LTS_Empty)
         next
           case (LTS_Step a q Δ w q')
           then show ?case apply auto 
             by (smt (verit, del_insts) LTS_is_reachable.LTS_Step UnCI Un_insert_right mem_Collect_eq)
         next
           case (LTS_Epi q Δ q')
           then show ?case apply auto 
             by (smt (verit, del_insts) LTS_Epi1 UnCI Un_insert_right mem_Collect_eq)
         next
           case (LTS_Epi1 q Δ l q')
           then show ?case apply auto 
             by (smt (verit, ccfv_threshold) LTS_is_reachable.LTS_Epi1 UnCI Un_insert_right mem_Collect_eq)
         qed
         have ee:"LTS_is_reachable  (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v))) (state.Pair (Node r1) (Node r2)) (a) (state.Pair ε (Node r2))"
           by (smt (verit, best) Collect_cong Un_insert_left e3 insert_is_Un subLTSlemma sup_commute)
      have e4:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (state.Pair (Node r1) (Node r2)) (a) (state.Pair ε (Node r2))"
         using ee by auto
      have e5:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (Node r2) b ε"
        by (metis e2 subLTSlemma sup_commute trans2Del1.simps(4) transEqDel)
      have e6:"Δ (reg2nfa (Concat r1 r2) v) = (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))"
        by auto
      have ee1:"LTS_is_reachable (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v))) (Node (Concat r1 r2)) [] (state.Pair (Node r1) (Node r2))"
        by (meson LTS_Empty LTS_Epi insertCI)
      have e7:"LTS_is_reachable ({(state.Pair ε (Node r2), {}, Node r2)} \<union> ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v}))
        (state.Pair ε (Node r2)) [] (Node r2)"
        by (meson LTS_Empty LTS_Epi UnCI singletonI)
      have e8:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (state.Pair (Node r1) (Node r2)) (a@b) ε" 
        by (metis (no_types, lifting) LTS_Epi1 e4 e5 e6 insertI1 joinLTSlemma)      
      have e9:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (Node (Concat r1 r2)) (a@b) ε"
        using e8 ee1 joinLTSlemma by fastforce
      have e10:"LTS_is_reachable
     (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))
     (Node (Concat r1 r2)) (a @ b) ε " 
        using e6 e9 by presburger
      from b1 b2 show "LTS_is_reachable
     (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))
     (Node (Concat r1 r2)) (a @ b) ε" 
        using e10 by blast
    qed
    from c7 have "LTS_is_reachable
     (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))
     (Node (Concat r1 r2)) (a @ b) ε" by auto
    then show ?thesis by auto
  qed
  subgoal for x
  proof -
    assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}"
    assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x}"
    assume a3:"LTS_is_reachable
     (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))
     (Node (Concat r1 r2)) x ε"
    show "x ∈ (λx. fst x @ snd x) `
         ({w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x} ×
          {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x})" sorry
  qed
done
next
  case (Star r)
  then show ?case apply auto 
     apply(unfold \<L>_def NFA_accept_def)
     apply auto 
     subgoal for x  sorry
     subgoal for x sorry
    done
next
  case (Plus r)
  then show ?case  
    apply(unfold \<L>_def NFA_accept_def)
    apply auto 
    subgoal for x q xa sorry
    subgoal for x sorry
    subgoal for x sorry
    done
next
  case (Ques r)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto 
    subgoal sorry
    subgoal for x q xa sorry
    subgoal for x sorry
    done
qed

end