theory reg2nfa 
  imports AReg NFA
begin

section "definition of nondeterministic finite automaton"


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


 
primrec trans2LTS :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> (('v regexp \<times> 'v set \<times> 'v regexp) set * ('v regexp * 'v regexp) set)" where 
    "trans2LTS (LChr v) alp_set= ({(LChr v,{v},\<epsilon>)},{})"|
    "trans2LTS (ESet) alp_set= ({(ESet,{},\<epsilon>)},{})"|
    "trans2LTS (\<epsilon>) alp_set = ({(\<epsilon>,{},\<epsilon>)},{})"|
    "trans2LTS (Dot) alp_set = ({(Dot ,alp_set, \<epsilon>)},{})"|
    "trans2LTS (Concat r1 r2) alp_set =(renameDelta1 (fst (trans2LTS r1 alp_set)) (ConcatRegexp r2) \<union> (fst (trans2LTS r2 alp_set)),
                                        (renameDelta2 (snd (trans2LTS r1 alp_set)) (ConcatRegexp r2) \<union> {(Concat r1 r2, Concat r1 r2),(Concat \<epsilon> r2, r2)}  \<union> snd (trans2LTS r2 alp_set)))"|
    "trans2LTS (Alter r1 r2) alp_set = (fst (trans2LTS r1 alp_set) \<union> fst (trans2LTS r2 alp_set), 
                                        snd (trans2LTS r1 alp_set) \<union> snd (trans2LTS r2 alp_set) \<union> {(Alter r1 r2, r1),(Alter r1 r2, r2)})"|
    "trans2LTS (Star r) alp_set = (Delta1_State (fst (trans2LTS r alp_set)) r, 
                                   (Delta2_State (snd (trans2LTS r alp_set) \<union> {(Star r, r)}) r) \<union> {(Star r, \<epsilon>),(Star r, Star r)})"|
    "trans2LTS (Plus r) alp_set = (Delta1_State ((renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r))) \<union> Delta1_State (fst (trans2LTS r alp_set)) r) r,
                                    Delta2_State (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r)) \<union> snd (trans2LTS r alp_set) \<union> {(Plus r, (Concat r (Star r))), (Concat r (Star r), r),  (Star r, r)}) r \<union> {(Star r, \<epsilon>)})"|
    "trans2LTS (Ques r) alp_set = (fst (trans2LTS r alp_set),
                                   {(Ques r,\<epsilon>), (Ques r, r)} \<union> snd (trans2LTS r alp_set))"



value "trans2LTS (Alter Dot (LChr r)) {v}"
value "trans2LTS (Concat Dot (LChr r)) {v}"
value "trans2LTS (Star (Concat Dot (LChr r))) {v}"
value "trans2LTS (Ques (Concat Dot (LChr r))) {v}"
value "trans2LTS (Plus (Concat Dot (LChr r))) {v}"


primrec reg2q :: "'v regexp \<Rightarrow> 'v set\<Rightarrow>  ('v regexp) set" where
    "reg2q Dot a = {Dot, \<epsilon>}"|
    "reg2q (LChr p) a =  {(LChr p), \<epsilon>}"|
    "reg2q (Alter r1 r2) a = {(Alter r1 r2),\<epsilon>} \<union> reg2q r1 a \<union> reg2q r2 a"|
    "reg2q (Star r) a = Node_State (reg2q r a) (Star r)" |
    "reg2q (Plus r) a =  Node_State (reg2q r a) (Star r) \<union> {r}" |
    "reg2q (Ques r) a = {(Ques r), \<epsilon>} \<union> reg2q r a" |
    "reg2q ESet a = {ESet, \<epsilon>}"|
    "reg2q \<epsilon> a = {\<epsilon>}"|
    "reg2q (Concat r1 r2) a = {Concat r1 r2, r2, \<epsilon>, (Concat \<epsilon> r2)}"


primrec reg2nfa :: "'v regexp \<Rightarrow> 'v set\<Rightarrow> ('v regexp,'v) NFA_rec" where 
    "reg2nfa (Concat r1 r2) a= \<lparr> 
                  \<Q> = reg2q (Concat r1 r2) a,
                  \<Sigma> = alp_reg  (Concat r1 r2) a,
                  \<Delta> = fst (trans2LTS  (Concat r1 r2) a),
                  \<Delta>' = snd (trans2LTS  (Concat r1 r2) a),
                  \<I> ={(Concat r1 r2)}, 
                  \<F> ={\<epsilon>}\<rparr> " |
    "reg2nfa (ESet) a= \<lparr>
                  \<Q> = reg2q ESet a,
                  \<Sigma> = alp_reg (ESet) a,
                  \<Delta> = fst (trans2LTS (ESet) a),
                  \<Delta>' = snd (trans2LTS (ESet) a),
                  \<I> = {ESet}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (\<epsilon>) a= \<lparr>
                  \<Q> = reg2q \<epsilon> a,
                  \<Sigma> = alp_reg (\<epsilon>) a,
                  \<Delta> = fst (trans2LTS (\<epsilon>) a),
                  \<Delta>' = snd (trans2LTS (\<epsilon>) a),
                  \<I> = {\<epsilon>}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Dot) a= \<lparr> 
                  \<Q> = reg2q (Dot) a,
                  \<Sigma> = alp_reg (Dot) a,
                  \<Delta> = fst (trans2LTS (Dot) a),
                  \<Delta>' = snd (trans2LTS (Dot) a),
                  \<I> = {Dot}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (LChr v) a=  \<lparr> 
                  \<Q> = reg2q (LChr v) a,
                  \<Sigma> = alp_reg (LChr v) a,
                  \<Delta> = fst (trans2LTS (LChr v) a),
                  \<Delta>' = snd (trans2LTS (LChr v) a),
                  \<I> = {(LChr v)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Alter r1 r2) a =  \<lparr> 
                  \<Q> = reg2q (Alter r1 r2) a,
                  \<Sigma> = alp_reg (Alter r1 r2) a,
                  \<Delta> = fst (trans2LTS (Alter r1 r2) a),
                  \<Delta>' = snd (trans2LTS (Alter r1 r2) a),
                  \<I> = {(Alter r1 r2)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Star r) a = \<lparr> 
                  \<Q> = reg2q  (Star r) a,
                  \<Sigma> = alp_reg (Star r) a,
                  \<Delta> = fst (trans2LTS (Star r) a),
                  \<Delta>' = snd (trans2LTS (Star r) a),
                  \<I> = {(Star r)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Plus r) a= \<lparr> 
                  \<Q> = reg2q  (Plus r) a,
                  \<Sigma> = alp_reg (Plus r) a,
                  \<Delta> = fst (trans2LTS  (Plus r) a),
                  \<Delta>' = snd (trans2LTS  (Plus r) a),
                  \<I> = {(Plus r)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Ques r) a = \<lparr> 
                  \<Q> = reg2q  (Ques r) a,
                  \<Sigma> = alp_reg (Ques r) a,
                  \<Delta> = fst (trans2LTS  (Ques r) a),
                  \<Delta>' = snd (trans2LTS  (Ques r) a),
                  \<I> = {(Ques r)}, 
                  \<F> = {\<epsilon>}\<rparr> " 

section "function correctness of transition from regexp expression to  nondeterministic finite automaton"

lemma transEqDel : "fst (trans2LTS r1 v) = \<Delta> (reg2nfa r1 v)"
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

lemma trans2Del :"fst (trans2LTS r v) =(\<Delta> (reg2nfa r v))"
  by (simp add: transEqDel)


lemma ll:"LTS_is_reachable ({}, {(\<epsilon>, \<epsilon>)}) \<epsilon> [] \<epsilon>"
  apply auto
  done


theorem tranl_eq :
  fixes r v  
  shows l1: "sem_reg r v = \<L> (reg2nfa r v)"
proof(induct r)
case ESet
  then show ?case 
    apply (unfold \<L>_def NFA_accept_def)
    apply auto
    by (rule LTS_is_reachable.cases) auto
next
    case (LChr x)
    then show ?case     
      apply( unfold \<L>_def NFA_accept_def)
      apply auto
      apply(rule LTS_is_reachable.cases)
      apply auto
      subgoal for w
      proof -
        assume a1:" LTS_is_reachable ({(LChr x, {x}, \<epsilon>)}, {}) \<epsilon> w \<epsilon>"
        from a1 have "w = []" 
          by(rule LTS_is_reachable.cases)auto
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
        assume a1:"LTS_is_reachable ({(Dot, v, \<epsilon>)}, {}) \<epsilon> w \<epsilon>"
        from a1 have "w=[]"       
          by (rule LTS_is_reachable.cases) auto
        then show "w=[]" .
      qed
      done
    done    
next
  case \<epsilon>
  then show ?case     
    apply (unfold \<L>_def  NFA_accept_def)
    apply auto
    subgoal for x
      apply(rule LTS_is_reachable.cases)
      by auto
    done
next
  case (Alter r1 r2)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for x q xa
    proof -
      assume a1:"sem_reg r1 v = {w. \<exists>q\<in>\<I> (reg2nfa r1 v). \<exists>x\<in>\<F> (reg2nfa r1 v). LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) q w x}"
      assume a2:"sem_reg r2 v = {w. \<exists>q\<in>\<I> (reg2nfa r2 v). \<exists>x\<in>\<F> (reg2nfa r2 v). LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) q w x}"
      assume a3:"q \<in> \<I> (reg2nfa r1 v)"
      assume a4:"xa \<in> \<F> (reg2nfa r1 v)"
      assume a5:"LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) q x xa"
      then show "\<exists>q''. (q'' = r1 \<or> q'' = r2 \<or> (Alter r1 r2, q'') \<in> snd (trans2LTS r1 v) \<or> (Alter r1 r2, q'') \<in> snd (trans2LTS r2 v)) \<and>
          LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) q'' x \<epsilon>"
      proof -
         have c1:"q = r1" 
           using InitState a3 by auto
         have c2:"xa =\<epsilon>"
           using FinalState a4 by blast
         have c3:"LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) r1 x \<epsilon>"
           using a5 c1 c2 by auto
         have c4:"LTS_is_reachable (fst (trans2LTS r1 v), \<Delta>' (reg2nfa r1 v)) r1 x \<epsilon>"
           using c3 
           by (induct r1) auto
        have c5: "LTS_is_reachable (fst (trans2LTS r1 v),snd (trans2LTS r1 v)) r1 x \<epsilon>"
           using c4 apply (induct r1)
           by auto
         have c6:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) r1 x \<epsilon>"
           using c5 
           by (metis Un_insert_right prod.collapse subLTSlemma)
         then show "\<exists>q''. (q'' = r1 \<or> q'' = r2 \<or> (Alter r1 r2, q'') \<in> snd (trans2LTS r1 v) \<or> (Alter r1 r2, q'') \<in> snd (trans2LTS r2 v)) \<and>
          LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) q'' x \<epsilon>" by auto
       qed
     qed
     subgoal for x q xa
      proof -
      assume a1:"sem_reg r1 v = {w. \<exists>q\<in>\<I> (reg2nfa r1 v). \<exists>x\<in>\<F> (reg2nfa r1 v). LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) q w x}"
      assume a2:"sem_reg r2 v = {w. \<exists>q\<in>\<I> (reg2nfa r2 v). \<exists>x\<in>\<F> (reg2nfa r2 v). LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) q w x}"
      assume a3:"q \<in> \<I> (reg2nfa r2 v)"
      assume a4:"xa \<in> \<F> (reg2nfa r2 v)"
      assume a5:"LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) q x xa"
      then show " \<exists>q''. (q'' = r1 \<or> q'' = r2 \<or> (Alter r1 r2, q'') \<in> snd (trans2LTS r1 v) \<or> (Alter r1 r2, q'') \<in> snd (trans2LTS r2 v)) \<and>
          LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) q'' x \<epsilon>"
      proof -
         have c1:"q = r2" 
           using InitState a3 by blast
         have c2:"xa =\<epsilon>"
           using FinalState a4 by blast
         have c3:"LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) r2 x \<epsilon>"
           using a5 c1 c2 by auto
         have c4:"LTS_is_reachable (fst (trans2LTS r2 v), \<Delta>' (reg2nfa r2 v)) r2 x \<epsilon>"
           using c3 
           by (induct r2) auto
        have c5: "LTS_is_reachable (fst (trans2LTS r2 v),snd (trans2LTS r2 v)) r2 x \<epsilon>"
           using c4 apply (induct r2)
           by auto
        have c6:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) r2 x \<epsilon>"
          using c5 
          by (smt (z3) Un_insert_left subLTSlemma sup_commute surjective_pairing)
         then show " \<exists>q''. (q'' = r1 \<or> q'' = r2 \<or> (Alter r1 r2, q'') \<in> snd (trans2LTS r1 v) \<or> (Alter r1 r2, q'') \<in> snd (trans2LTS r2 v)) \<and>
          LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) q'' x \<epsilon>" by auto
       qed
     qed
     subgoal for x
     proof -
       assume a1:"sem_reg r1 v = {w. \<exists>q\<in>\<I> (reg2nfa r1 v). \<exists>x\<in>\<F> (reg2nfa r1 v). LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) q w x}" 
       assume a2:"sem_reg r2 v = {w. \<exists>q\<in>\<I> (reg2nfa r2 v). \<exists>x\<in>\<F> (reg2nfa r2 v). LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) q w x}"
       assume a3:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) x \<epsilon>"
       assume a4:"\<forall>q\<in>\<I> (reg2nfa r2 v). \<forall>xa\<in>\<F> (reg2nfa r2 v). \<not> LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) q x xa"
       show "\<exists>q\<in>\<I> (reg2nfa r1 v). \<exists>xa\<in>\<F> (reg2nfa r1 v). LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) q x xa" 
       proof -
         have c1:" \<not> LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) r2 x \<epsilon>" using a4 
           using finalSet
           by (simp add: finalSet initalSet)
        have c2:" \<not> LTS_is_reachable (fst (trans2LTS r2 v), (snd (trans2LTS r2 v))) r2 x \<epsilon>" using c1 
          by (induct r2) auto
        have c3:" \<not> LTS_is_reachable (fst (trans2LTS r2 v), insert (Alter r1 r2, r2) (snd (trans2LTS r2 v))) (Alter r1 r2) x \<epsilon>" using c2
          apply simp
          apply(rule LTS_is_reachable.induct)
          apply auto
          sorry
         have c4:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) [] r1"
           by auto
         have c5:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) [] r2"
           by auto
         then show ?thesis sorry
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
    assume a1:"sem_reg r1 v ={w. \<exists>q\<in>\<I> (reg2nfa r1 v). \<exists>x\<in>\<F> (reg2nfa r1 v). LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) q w x}"
    assume a2:"sem_reg r2 v ={w. \<exists>q\<in>\<I> (reg2nfa r2 v). \<exists>x\<in>\<F> (reg2nfa r2 v). LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) q w x}"
    assume a3:"q \<in> \<I> (reg2nfa r1 v)"
    assume a4:"qa \<in> \<F> (reg2nfa r1 v)"
    assume a5:"LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) q a qa"
    assume a6:"xa \<in> \<I> (reg2nfa r2 v)"
    assume a7:"xb \<in> \<F> (reg2nfa r2 v)"
    assume a8:"LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) xa b xb"
    from a3 have c1:"q = r1" 
      using InitState by blast
    from a4 have c2:"qa = \<epsilon>" 
      using FinalState by blast
    from c1 c2 a5 have c3:"LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) r1 a \<epsilon>" 
      by auto
    from a6 have c4: "xa = r2" 
      using InitState by blast
    from a7 have c5: "xb = \<epsilon>"
      using FinalState by blast 
    from c4 c5 a8 have c6: "LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) r2 b \<epsilon>" 
      by auto
    from c3 c6 have c7:"LTS_is_reachable (\<Delta> (reg2nfa (Concat r1 r2) v), \<Delta>' (reg2nfa (Concat r1 r2) v))  (Concat r1 r2) (a @ b) \<epsilon>" 
      proof -
      assume b1:"LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) r1 a \<epsilon>"
      assume b2:"LTS_is_reachable (\<Delta> (reg2nfa r2 v), \<Delta>' (reg2nfa r2 v)) r2 b \<epsilon>"
      have e1:"LTS_is_reachable (fst (trans2LTS r1 v), snd (trans2LTS r1 v)) r1 a \<epsilon>" 
        using b1 by (induct r1)  auto
      have e2:"LTS_is_reachable (fst (trans2LTS r2 v), snd (trans2LTS r2 v)) r2 b \<epsilon>" 
        using b2 by (induct r2)  auto
      from b1 have e3:"LTS_is_reachable (\<Delta> (reg2nfa (Concat r1 r2) v), \<Delta>' (reg2nfa (Concat r1 r2) v)) (Concat r1 r2) a r2"
        apply simp
        proof - 
          assume a1:"LTS_is_reachable (\<Delta> (reg2nfa r1 v), \<Delta>' (reg2nfa r1 v)) r1 a \<epsilon>"
          have c1:"LTS_is_reachable (fst (trans2LTS r1 v), snd (trans2LTS r1 v)) r1 a \<epsilon>"
            using a1 by (induct r1) auto
          have c2:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v),snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)) r1 a   \<epsilon>"
            using c1 by auto
          have c3:"LTS_is_reachable
          ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
       (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
           (Concat r1 r2) a (Concat \<epsilon> r2)"
            using c1 
            apply simp    
            apply (induction rule: LTS_is_reachable.induct)
            apply auto
            apply blast
            by auto
          have c33: "LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
                    insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
                    (Concat r1 r2) a (Concat \<epsilon> r2)"
            using c3 apply auto
            by (metis (no_types, lifting) Un_commute boolean_algebra_cancel.sup0 fst_eqD insert_def snd_eqD subLTSlemma)
           have c4:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)} \<union> fst (trans2LTS r2 v),
                   insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
                   (Concat \<epsilon> r2) [] r2"
             using c33 by auto 
           have c5:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)} \<union> fst (trans2LTS r2 v),
                   insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
                   (Concat r1 r2) a r2"
             using c33 c4 
             by (induction rule: LTS_is_reachable.induct) auto
            then show "LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)} \<union> fst (trans2LTS r2 v),
                    insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
                    (Concat r1 r2) a  r2"  
              by blast
          qed
      have e4:"LTS_is_reachable (\<Delta> (reg2nfa (Concat r1 r2) v), \<Delta>' (reg2nfa (Concat r1 r2) v)) r2 b \<epsilon>"
        using e2 apply simp by (smt (z3) Un_commute Un_insert_right subLTSlemma)
      show " LTS_is_reachable (\<Delta> (reg2nfa (Concat r1 r2) v), \<Delta>' (reg2nfa (Concat r1 r2) v)) (Concat r1 r2) (a @ b) \<epsilon>" 
        by (meson e3 e4 joinLTSlemma)
    qed
    have e1:"LTS_is_reachable (\<Delta> (reg2nfa \<epsilon> v), \<Delta>' (reg2nfa \<epsilon> v)) \<epsilon> [] \<epsilon>"
      by auto
    have e2:"LTS_is_reachable (fst (trans2LTS r2 v), snd (trans2LTS r2 v))  r2 b \<epsilon>"
      using c6 by (induct r2) auto
    have e3:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)} \<union> fst (trans2LTS r2 v),
           ({(Concat q r2, Concat q' r2) |q q'. (q, q') \<in> snd (trans2LTS r1 v)} \<union> snd (trans2LTS r2 v)))
           r2 b \<epsilon>"
      using e2 by (simp add: sup.commute)
    have e4:"LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS \<epsilon> v)} \<union> fst (trans2LTS r2 v),
             insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
             r2 ([]@b) \<epsilon>"
      using e3 by (metis (no_types, lifting) Un_commute Un_insert_right append_self_conv2 e2 prod.collapse subLTSlemma)
    show "∃q''. (q'' = Concat r1 r2 ∨ r1 = ε ∧ q'' = r2 ∨ (∃q'. q'' = Concat q' r2 ∧ (r1, q') ∈ snd (trans2LTS r1 v)) ∨ (Concat r1 r2, q'') ∈ snd (trans2LTS r2 v)) ∧
          LTS_is_reachable ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
          insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
          q'' (a @ b) ε"
      using c7 by auto 
  qed
  subgoal for x 
  proof -
    assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) q w x}"
    assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) q w x}"
    assume a3:"LTS_is_reachable
     ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
      insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
     (Concat r1 r2) x ε"
    show "∃q p. x = q @ p ∧
          (∃qa∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) qa q x) ∧
          (∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) q p x)"
    proof -
      have c1: "LTS_is_reachable (trans2LTS (Concat r1 r2) v) (Concat r1 r2) x ε"
        using a3 by auto
      have "∃q p. x = q @ p ∧
          (LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) r1 q ε) ∧
          (LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) r2 p ε)" 
        using c1 apply auto
           
        sorry
      then show "∃q p. x = q @ p ∧
          (∃qa∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v), Δ' (reg2nfa r1 v)) qa q x) ∧
          (∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v), Δ' (reg2nfa r2 v)) q p x)"
        by (simp add: finalSet initalSet)
    qed
  qed
  done
next
  case (Star r)
  then show ?case apply auto 
     apply(unfold \<L>_def NFA_accept_def)
     apply auto 
    subgoal for x 
    proof -
      assume a1:"sem_reg r v = {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      assume a2:"x \<in> star {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      show "∃q''. (q'' = ε ∨ q'' = Star r ∨ (Star r, q'') ∈ Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r) ∧
          LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) q'' x ε"   
      proof -
        from a2 have 3:"LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) x ε"
          apply auto
          apply(induction rule:star.induct)
          subgoal 
          proof -
            have "LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r)) (Star r) [] ε" 
              by auto
            show "∃q''. (q'' = ε ∨ q'' = Star r ∨ (Star r, q'') ∈ Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r) ∧
          LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) q'' [] ε"
              by auto
          qed
          subgoal for x y
          proof -
            assume 1:" x ∈ {w. ∃q∈ℐ (reg2nfa r v). Bex (ℱ (reg2nfa r v)) (LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) q w)} ∧
                      y ∈ star {w. ∃q∈ℐ (reg2nfa r v). Bex (ℱ (reg2nfa r v)) (LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) q w)} ∧
                      (∃q''. (q'' = ε ∨ q'' = Star r ∨ (Star r, q'') ∈ Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r) ∧
                      LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) q'' y
                      ε) "
            show " ∃q''. (q'' = ε ∨ q'' = Star r ∨ (Star r, q'') ∈ Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r) ∧
                    LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) q''
                     (x @ y) ε"
            proof -
              from 1 have 2:" ∃q∈ℐ (reg2nfa r v). ∃xa∈ℱ (reg2nfa r v). LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) q x xa ∧
                             y ∈ star {w. ∃q∈ℐ (reg2nfa r v). Bex (ℱ (reg2nfa r v)) (LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) q w)} ∧
                             LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) y ε"
                by auto
              from 2 have 3:"∃xa∈ℱ (reg2nfa r v). LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) r x xa ∧
                             y ∈ star {w. ∃q∈ℐ (reg2nfa r v). Bex (ℱ (reg2nfa r v)) (LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) q w)} ∧
                             LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) y ε"
                using InitState by blast
              from 3 have 4:"LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) r x ε ∧
                             y ∈ star {w. ∃q∈ℐ (reg2nfa r v). Bex (ℱ (reg2nfa r v)) (LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) q w)} ∧
                             LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) y ε"
                by (metis FinalState)   
              from 4 have 5:"LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) r x ε ∧
                             y ∈ star {w. ∃q∈ℐ (reg2nfa r v). ∃x∈ℱ (reg2nfa r v). LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) q w x}  ∧
                             LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) y ε"
                by auto
              have 6:"LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) r x ε ∧
                             y ∈ star {w.  ∃x∈ℱ (reg2nfa r v). LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) r w x}  ∧
                             LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) y ε"
                using 5 apply auto 
                by (smt (verit) "2" Collect_cong InitState)
              have 7:"LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) r x ε ∧
                             y ∈ star {w. LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) r w ε}  ∧
                             LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) y ε"
                using 6 apply auto
                by (smt (verit) "3" Collect_cong FinalState)
              have "LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) (x @ y) ε"
                using 7
                apply auto
                apply (induction rule:LTS_is_reachable.induct)
                sorry

              show "∃q''. (q'' = ε ∨ q'' = Star r ∨ (Star r, q'') ∈ Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r) ∧
          LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) q'' (x @ y) ε" sorry
            qed
          qed
          done
        show "∃q''. (q'' = ε ∨ q'' = Star r ∨ (Star r, q'') ∈ Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r) ∧
          LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) q'' x ε" sorry
      qed
    qed
    subgoal for x 
    proof - 
      assume a1:"sem_reg r v = {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      assume a2:"LTS_is_reachable (Delta1_State (fst (trans2LTS r v)) r, insert (Star r, ε) (insert (Star r, Star r) (Delta2_State (insert (Star r, r) (snd (trans2LTS r v))) r))) (Star r) x ε"
      show "x ∈ star {w. ∃q∈ℐ (reg2nfa r v). ∃x∈ℱ (reg2nfa r v). LTS_is_reachable (Δ (reg2nfa r v), Δ' (reg2nfa r v)) q w x}"
        sorry
    qed
    done
next
  case (Plus r)
  then show ?case  
    apply(unfold \<L>_def NFA_accept_def)
    apply auto 
    subgoal for x q xa 
    proof -
      assume a1:"sem_reg r v = {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      assume a2:"q \<in> \<I> (reg2nfa r v)"
      assume a3:"xa \<in> \<F> (reg2nfa r v)"
      assume a4:"LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q x xa"
      show " \<exists>q''. ( Plus r, q'')
          \<in> Delta2_State
              (insert ( Plus r, Concat r (Star r))
                (insert (Concat r (Star r), r) (insert (Star r, r) ({(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)} \<union> snd (trans2LTS r v)))))
              (Star r) \<and>
          LTS_is_reachable
           (Delta1_State ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> Delta1_State (fst (trans2LTS r v)) r) r,
            insert (Star r, \<epsilon>)
             (Delta2_State
               (insert ( Plus r, Concat r (Star r))
                 (insert (Concat r (Star r), r) (insert (Star r, r) ({(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)} \<union> snd (trans2LTS r v)))))
               (Star r)))
           q'' x \<epsilon>" 
        sorry 
    qed
    subgoal for x 
    proof -
      assume a1:"sem_reg r v = {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      assume a2:"x \<in> star {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      show "\<exists>q''. ( Plus r, q'')
            \<in> Delta2_State
                (insert ( Plus r, Concat r (Star r))
                  (insert (Concat r (Star r), r) (insert (Star r, r) ({(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)} \<union> snd (trans2LTS r v)))))
                (Star r) \<and>
            LTS_is_reachable
             (Delta1_State ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> Delta1_State (fst (trans2LTS r v)) r) r,
              insert (Star r, \<epsilon>)
               (Delta2_State
                 (insert ( Plus r, Concat r (Star r))
                   (insert (Concat r (Star r), r) (insert (Star r, r) ({(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)} \<union> snd (trans2LTS r v)))))
                 (Star r)))
             q'' x \<epsilon>"
        sorry
    qed
    subgoal for x 
    proof -
      assume a1:"sem_reg r v = {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      assume a2:"x \<notin> star {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      assume a3:"LTS_is_reachable
     (Delta1_State ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> Delta1_State (fst (trans2LTS r v)) r) r,
      insert (Star r, \<epsilon>)
       (Delta2_State
         (insert ( Plus r, Concat r (Star r))
           (insert (Concat r (Star r), r) (insert (Star r, r) ({(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)} \<union> snd (trans2LTS r v)))))
         (Star r)))
      (Plus r) x \<epsilon>"
      show "    \<exists>q\<in>\<I> (reg2nfa r v). \<exists>xa\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q x xa"
        sorry
    qed
    done
next
  case (Ques r)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto 
    subgoal for x q xa 
    proof -
      assume a1:"sem_reg r v = {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      assume a2:"sem_reg r v = {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}"
      assume a3:"q \<in> \<I> (reg2nfa r v)"
      assume a4:" xa \<in> \<F> (reg2nfa r v)"
      assume a5:"LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q x xa"
      show "\<exists>q''. (q'' = \<epsilon> \<or> q'' = r \<or> ((Ques r), q'') \<in> snd (trans2LTS r v)) \<and> LTS_is_reachable (fst (trans2LTS r v), insert ((Ques r), \<epsilon>) (insert ((Ques r), r) (snd (trans2LTS r v)))) q'' x \<epsilon>"
     sorry
    qed
    subgoal for x 
    proof -
      assume a1:"sem_reg r v = {w. \<exists>q\<in>\<I> (reg2nfa r v). \<exists>x\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q w x}" 
      assume a2:"LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, \<epsilon>) (insert (Ques r, r) (snd (trans2LTS r v)))) (Ques r) x \<epsilon>"
      assume a3:"x \<noteq> []" 
      show "\<exists>q\<in>\<I> (reg2nfa r v). \<exists>xa\<in>\<F> (reg2nfa r v). LTS_is_reachable (\<Delta> (reg2nfa r v), \<Delta>' (reg2nfa r v)) q x xa "
        sorry
    qed
    done
qed

end