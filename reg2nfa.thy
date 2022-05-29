theory reg2nfa 
  imports AReg NFA
begin


fun ConcatRegexp::"'v regexp \<Rightarrow> 'v regexp\<Rightarrow> 'v regexp" where
  "ConcatRegexp r1 r2 = Concat r2 r1"

fun renameDelta1 :: "('v regexp * 'v set * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp *'v set *'v regexp) set" where 
    "renameDelta1 ss f = {(f q,v, f q')| q v q' . (q, v, q')\<in> ss}"

fun renameDelta2 :: "('v regexp * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp  *'v regexp) set" where  
    "renameDelta2 ss f = {(f q, f q')| q q'.(q, q')\<in> ss}"

inductive_set Delta1_State :: " ('v regexp * 'v set * 'v regexp) set \<Rightarrow> 'v regexp \<Rightarrow> ('v regexp * 'v set * 'v regexp) set" 
  for tr :: "('v regexp * 'v set * 'v regexp) set" and r::"'v regexp" 
  where
  Node2Del1:"x \<in> tr \<Longrightarrow> x \<in> (Delta1_State tr r)" |
  StepDel1:"x \<in> Delta1_State tr r \<Longrightarrow> (Concat (fst x) (Star r), fst (snd x), Concat (snd (snd x)) (Star r)) \<in> Delta1_State tr r"


inductive_set Delta2_State :: " ('v regexp  * 'v regexp) set \<Rightarrow> 'v regexp \<Rightarrow> ('v regexp  * 'v regexp) set" 
  for tr :: "('v regexp * 'v regexp) set" and r::"'v regexp" 
  where 
  Node2Del2:"x \<in> tr \<Longrightarrow> x \<in> (Delta2_State tr r)" |
  StepDel2:"x \<in> Delta2_State tr r \<Longrightarrow> (Concat (fst x) (Star r), Concat (snd x) (Star r)) \<in> Delta2_State tr r"

inductive_set Node_State :: "'v regexp set \<Rightarrow> 'v regexp \<Rightarrow> 'v regexp set" 
  for tr :: "('v regexp) set" and r::"'v regexp" 
  where
  Node2Star:"x \<in> tr \<Longrightarrow> x \<in> (Node_State tr r)" |
  StepStar:"x \<in> Node_State tr r \<Longrightarrow> Concat x r \<in> Node_State tr r " 

  
primrec trans2Del1 :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> (('v regexp \<times> 'v set \<times> 'v regexp) set * ('v regexp * 'v regexp) set)" where 
    "trans2Del1 (LChr v) alp_set= ({(LChr v,{v},\<epsilon>)},{})"|
    "trans2Del1 (ESet) alp_set= ({(ESet,{},\<epsilon>)},{})"|
    "trans2Del1 (\<epsilon>) alp_set = ({},{(\<epsilon>,\<epsilon>)})"|
    "trans2Del1 (Dot) alp_set = ({(Dot ,alp_set, \<epsilon>)},{})"|
    "trans2Del1 (Concat r1 r2) alp_set =(renameDelta1 (fst (trans2Del1 r1 alp_set)) (ConcatRegexp r2) \<union> (fst (trans2Del1 r2 alp_set)),
                                        (renameDelta2 (snd (trans2Del1 r1 alp_set)) (ConcatRegexp r2) \<union> {(Concat \<epsilon> r2, r2)}  \<union> snd (trans2Del1 r2 alp_set)))"|
    "trans2Del1 (Alter r1 r2) alp_set = (fst (trans2Del1 r1 alp_set) \<union> fst (trans2Del1 r2 alp_set), 
                                        snd (trans2Del1 r1 alp_set) \<union> snd (trans2Del1 r2 alp_set) \<union> {(Alter r1 r2, r1),(Alter r1 r2, r2)})"|
    "trans2Del1 (Star r) alp_set = (Delta1_State (fst (trans2Del1 r alp_set)) r, 
                                   (Delta2_State (snd (trans2Del1 r alp_set) \<union> {(Star r, r)}) (Star r)) \<union> {(Star r, \<epsilon>)})"|
    "trans2Del1 (Plus r) alp_set = (Delta1_State ((renameDelta1 (fst (trans2Del1 r alp_set)) (ConcatRegexp (Star r))) \<union> Delta1_State (fst (trans2Del1 r alp_set)) r) r,
                                    Delta2_State (renameDelta2 (snd (trans2Del1 r alp_set)) (ConcatRegexp (Star r)) \<union> snd (trans2Del1 r alp_set) \<union> {(Plus r, (Concat r (Star r))), (Concat r (Star r), r),  (Star r, r)}) (Star r) \<union> {(Star r, \<epsilon>)})"|
    "trans2Del1 (Ques r) alp_set = (fst (trans2Del1 r alp_set),
                                   {(Ques r,\<epsilon>), (Ques r, r)} \<union> snd (trans2Del1 r alp_set))"


value "trans2Del1 (Concat (LChr a) (LChr b)) {v}"

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


lemma transEqDel : "fst (trans2Del1 r1 v) = \<Delta> (reg2nfa r1 v)"
  apply (induct r1)
  apply auto
  done


lemma InitState:"q \<in> \<I> (reg2nfa r1 v) \<Longrightarrow> q = (r1)"
  apply (induct r1)
  by auto

lemma FinalState:"xa \<in> \<F> (reg2nfa r1 v) \<Longrightarrow> xa = \<epsilon>"
  apply (induct r1)
  by auto

lemma initalSet:"\<I> (reg2nfa r1 v) = {r1}"
  apply (induct r1)
  apply auto
  done

lemma finalSet:"\<F> (reg2nfa r1 v) = {\<epsilon>}"
  apply(induct r1)
  apply auto
  done

lemma trans2Del :"fst (trans2Del1 r v) =(\<Delta> (reg2nfa r v))"
  by (simp add: transEqDel)


theorem tranl_eq :
  fixes r v  
  shows l1: "sem_reg r v = \<L> (reg2nfa r v)"
proof(induct r)
case ESet
  then show ?case 
    apply (unfold \<L>_def NFA_accept_def)
    apply auto
    apply(rule LTS_is_reachable.cases)
    by auto
next
    case (LChr x)
    then show ?case     
      apply( unfold \<L>_def NFA_accept_def)
      apply auto
      apply(rule LTS_is_reachable.cases)
      apply auto
      subgoal for w
      proof -
        assume a1:" LTS_is_reachable ({(LChr x, {x}, ε)}, {}) ε w ε"
        from a1 have "w = []" 
          apply(rule LTS_is_reachable.cases)
          by auto
        then show "w=[]" .
      qed 
      done
    next
  case Dot
  then show ?case 
    apply (unfold \<L>_def  NFA_accept_def)
    apply auto
    subgoal for x 
      apply(simp add:image_iff)
      apply(rule LTS_is_reachable.cases)
         apply auto
      subgoal for a w
      proof -
        assume a1:"LTS_is_reachable ({(Dot, v, ε)}, {}) ε w ε"
        from a1 have "w=[]"       apply(rule LTS_is_reachable.cases)
          by auto
        then show "w=[]" .
      qed
      done
    done    
  next
  case (Alter r1 r2)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for x q xa
    proof -
      assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) q w x}"
      assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) q w x}"
      assume a3:"q \<in> \<I> (reg2nfa r1 v)"
      assume a4:"xa \<in> \<F> (reg2nfa r1 v)"
      assume a5:"LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) q x xa"
      then show "∃q''. (q'' = r1 ∨ q'' = r2 ∨ (r1 || r2, q'') ∈ snd (trans2Del1 r1 v) ∨ (r1 || r2, q'') ∈ snd (trans2Del1 r2 v)) ∧
          LTS_is_reachable (fst (trans2Del1 r1 v) ∪ fst (trans2Del1 r2 v), insert (r1 || r2, r1) (insert (r1 || r2, r2) (snd (trans2Del1 r1 v) ∪ snd (trans2Del1 r2 v)))) q'' x ε"
      proof -
         have c1:"q = r1" 
           using InitState a3 by auto
         have c2:"xa =\<epsilon>"
           using FinalState a4 by blast
         have c3:"LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) r1 x \<epsilon>"
           using a5 c1 c2 by auto
         have c4:"LTS_is_reachable (fst (trans2Del1 r1 v), Δ' (reg2nfa r1 v)) r1 x \<epsilon>"
           using c3 
           by (induct r1) auto
        have c5: "LTS_is_reachable (fst (trans2Del1 r1 v),snd (trans2Del1 r1 v)) r1 x \<epsilon>"
           using c4 apply (induct r1)
           by auto
         have c6:"LTS_is_reachable (fst (trans2Del1 r1 v) ∪ fst (trans2Del1 r2 v), insert (r1 || r2, r1) (insert (r1 || r2, r2) (snd (trans2Del1 r1 v) ∪ snd (trans2Del1 r2 v)))) r1 x ε"
           using c5 
           by (metis Un_insert_right prod.collapse subLTSlemma)
         then show "∃q''. (q'' = r1 ∨ q'' = r2 ∨ (r1 || r2, q'') ∈ snd (trans2Del1 r1 v) ∨ (r1 || r2, q'') ∈ snd (trans2Del1 r2 v)) ∧
          LTS_is_reachable (fst (trans2Del1 r1 v) ∪ fst (trans2Del1 r2 v), insert (r1 || r2, r1) (insert (r1 || r2, r2) (snd (trans2Del1 r1 v) ∪ snd (trans2Del1 r2 v)))) q'' x ε" by auto
       qed
     qed
     subgoal for x q xa
      proof -
      assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) q w x}"
      assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) q w x}"
      assume a3:"q \<in> \<I> (reg2nfa r2 v)"
      assume a4:"xa \<in> \<F> (reg2nfa r2 v)"
      assume a5:"LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) q x xa"
      then show " ∃q''. (q'' = r1 ∨ q'' = r2 ∨ (r1 || r2, q'') ∈ snd (trans2Del1 r1 v) ∨ (r1 || r2, q'') ∈ snd (trans2Del1 r2 v)) ∧
          LTS_is_reachable (fst (trans2Del1 r1 v) ∪ fst (trans2Del1 r2 v), insert (r1 || r2, r1) (insert (r1 || r2, r2) (snd (trans2Del1 r1 v) ∪ snd (trans2Del1 r2 v)))) q'' x ε"
      proof -
         have c1:"q = r2" 
           using InitState a3 by blast
         have c2:"xa =ε"
           using FinalState a4 by blast
         have c3:"LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) r2 x ε"
           using a5 c1 c2 by auto
         have c4:"LTS_is_reachable (fst (trans2Del1 r2 v), Δ' (reg2nfa r2 v)) r2 x ε"
           using c3 
           by (induct r2) auto
        have c5: "LTS_is_reachable (fst (trans2Del1 r2 v),snd (trans2Del1 r2 v)) r2 x ε"
           using c4 apply (induct r2)
           by auto
        have c6:"LTS_is_reachable (fst (trans2Del1 r1 v) ∪ fst (trans2Del1 r2 v), insert (r1 || r2, r1) (insert (r1 || r2, r2) (snd (trans2Del1 r1 v) ∪ snd (trans2Del1 r2 v)))) r2 x ε"
          using c5 
          by (smt (z3) Un_insert_left subLTSlemma sup_commute surjective_pairing)
         then show " ∃q''. (q'' = r1 ∨ q'' = r2 ∨ (r1 || r2, q'') ∈ snd (trans2Del1 r1 v) ∨ (r1 || r2, q'') ∈ snd (trans2Del1 r2 v)) ∧
          LTS_is_reachable (fst (trans2Del1 r1 v) ∪ fst (trans2Del1 r2 v), insert (r1 || r2, r1) (insert (r1 || r2, r2) (snd (trans2Del1 r1 v) ∪ snd (trans2Del1 r2 v)))) q'' x ε" by auto
       qed
     qed
     subgoal for x
       sorry
     done
 next
  case (Concat r1 r2)
  then show ?case 
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for a b q xa qa xb 
    proof -
    assume a1:"sem_reg r1 v ={w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) q w x}"
    assume a2:"sem_reg r2 v ={w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) q w x}"
    assume a3:"q \<in> \<I> (reg2nfa r1 v)"
    assume a4:"xa \<in> \<F> (reg2nfa r1 v)"
    assume a5:"LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) q a xa"
    assume a6:"qa \<in> \<I> (reg2nfa r2 v)"
    assume a7:"xb \<in> \<F> (reg2nfa r2 v)"
    assume a8:"LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) qa b xb"
    from a3 have c1:"q = r1" 
      using InitState by blast
    from a4 have c2:"xa = ε" 
      using FinalState by blast
    from c1 c2 a5 have c3:"LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) r1 a ε" 
      by auto
    from a6 have c4: "qa = r2" 
      using InitState by blast
    from a7 have c5: "xb = ε"
      using FinalState by blast 
    from c4 c5 a8 have c6: "LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) r2 b ε" 
      by auto
    from c3 c6 have c7:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v), Δ' (reg2nfa (Concat r1 r2) v))  (Concat r1 r2) (a @ b) ε" 
      proof -
      assume b1:"LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) r1 a ε"
      assume b2:"LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) r2 b ε"
      have e1:"LTS_is_reachable (fst (trans2Del1 r1 v), snd (trans2Del1 r1 v)) r1 a ε" 
        using b1 by (induct r1)  auto
      have e2:"LTS_is_reachable (fst (trans2Del1 r2 v), snd (trans2Del1 r2 v)) r2 b ε" 
        using b2 by (induct r2)  auto
      from b1 have e3:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v), Δ' (reg2nfa (Concat r1 r2) v)) (Concat r1 r2) a r2"
        apply simp
        proof - 
          assume a1:"LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) r1 a ε"
          have c1:"LTS_is_reachable (fst (trans2Del1 r1 v), snd (trans2Del1 r1 v)) r1 a ε"
            using a1 by (induct r1) auto
          have c2:"LTS_is_reachable (fst (trans2Del1 r1 v) ∪ fst (trans2Del1 r2 v),snd (trans2Del1 r1 v) \<union> snd (trans2Del1 r2 v)) r1 a   ε"
            using c1 by auto
          have c3:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2Del1 r1 v)} ∪ fst (trans2Del1 r2 v),
            insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2Del1 r1 v)} ∪ snd (trans2Del1 r2 v)))
           (Concat r1 r2) a (Concat ε r2)"
            using c1 apply simp    
            apply (induction rule: LTS_is_reachable.induct)
            by auto+
           have c4:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2Del1 r1 v)} ∪ fst (trans2Del1 r2 v),
            insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2Del1 r1 v)} ∪ snd (trans2Del1 r2 v)))
           (Concat ε r2) [] r2"
             using c3 by auto 
           have c5:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2Del1 r1 v)} ∪ fst (trans2Del1 r2 v),
            insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2Del1 r1 v)} ∪ snd (trans2Del1 r2 v)))
           (Concat r1 r2) a r2"
             using c3 c4 
             by (induction rule: LTS_is_reachable.induct) auto
            then show "LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2Del1 r1 v)} ∪ fst (trans2Del1 r2 v),
          insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2Del1 r1 v)} ∪ snd (trans2Del1 r2 v)))
         (Concat r1 r2) a  r2"  
              by blast
          qed
      have e4:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v), Δ' (reg2nfa (Concat r1 r2) v)) r2 b ε"
        using e2 apply simp
        by (smt (z3) Un_commute Un_insert_right subLTSlemma)
      show " LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v), Δ' (reg2nfa (Concat r1 r2) v)) (Concat r1 r2) (a @ b) ε" 
        by (meson e3 e4 joinLTSlemma)
    qed
    show "∃q''. (r1 = ε ∧ q'' = r2 ∨ (∃q'. q'' = Concat q' r2 ∧ (r1, q') ∈ snd (trans2Del1 r1 v)) ∨ (Concat r1 r2, q'') ∈ snd (trans2Del1 r2 v)) ∧
          LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2Del1 r1 v)} ∪ fst (trans2Del1 r2 v),
            insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2Del1 r1 v)} ∪ snd (trans2Del1 r2 v)))
           q'' (a @ b) ε"
      using c7 apply auto
      
      subgoal for x
  proof -
    assume a1:"sem_reg r1 v = {w. \<exists>q\<in>\<I> (reg2nfa r1 v). \<exists>x\<in>\<F> (reg2nfa r1 v). LTS_is_reachable (\<Delta> (reg2nfa r1 v)) q w x}"
    assume a2:"sem_reg r2 v = {w. \<exists>q\<in>\<I> (reg2nfa r2 v). \<exists>x\<in>\<F> (reg2nfa r2 v). LTS_is_reachable (\<Delta> (reg2nfa r2 v)) q w x}"
    assume a3:"LTS_is_reachable
     (insert (state.Pair \<epsilon> (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) \<in> trans2Del1 r1 v} \<union> trans2Del1 r2 v)))
     (Node (Concat r1 r2)) x \<epsilon>"
    show "x \<in> (\<lambda>x. fst x @ snd x) `
         ({w. \<exists>q\<in>\<I> (reg2nfa r1 v). \<exists>x\<in>\<F> (reg2nfa r1 v). LTS_is_reachable (\<Delta> (reg2nfa r1 v)) q w x} \<times>
          {w. \<exists>q\<in>\<I> (reg2nfa r2 v). \<exists>x\<in>\<F> (reg2nfa r2 v). LTS_is_reachable (\<Delta> (reg2nfa r2 v)) q w x})" sorry
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