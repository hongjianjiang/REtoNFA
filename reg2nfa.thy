theory reg2nfa 
  imports AReg NFA
begin

section "definition of nondeterministic finite automaton"


fun ConcatRegexp::"'v regexp \<Rightarrow> 'v regexp\<Rightarrow> 'v regexp" where
  "ConcatRegexp r1 r2 = Concat r2 r1"

fun ConcatRegexp2::"'v regexp \<Rightarrow> 'v regexp\<Rightarrow> 'v regexp" where
  "ConcatRegexp2 r1 r2 = Concat (Concat r2 r1) r1"

fun renameDelta1 :: "('v regexp * 'v set * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp *'v set *'v regexp) set" where 
    "renameDelta1 ss f = {(f q,v, f q')| q v q' . (q, v, q')\<in> ss}"

fun renameDelta2 :: "('v regexp * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp  *'v regexp) set" where  
    "renameDelta2 ss f = {(f q, f q')| q q'.(q, q')\<in> ss}"

primrec trans2LTS :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> (('v regexp \<times> 'v set \<times> 'v regexp) set * ('v regexp * 'v regexp) set)" where 
    "trans2LTS (LChr v) alp_set= ({(LChr v,{v},\<epsilon>)},{})"|
    "trans2LTS (ESet) alp_set= ({(ESet,{},\<epsilon>)},{})"|
    "trans2LTS (\<epsilon>) alp_set = ({(\<epsilon>,{},\<epsilon>)},{})"|
    "trans2LTS (Dot) alp_set = ({(Dot ,alp_set, \<epsilon>)},{})"|
    "trans2LTS (Concat r1 r2) alp_set =(renameDelta1 (fst (trans2LTS r1 alp_set)) (ConcatRegexp r2) \<union> (fst (trans2LTS r2 alp_set)),
                                        (renameDelta2 (snd (trans2LTS r1 alp_set)) (ConcatRegexp r2) \<union> {(Concat \<epsilon> r2, r2)}  \<union> snd (trans2LTS r2 alp_set)))"|
    "trans2LTS (Alter r1 r2) alp_set = (fst (trans2LTS r1 alp_set) \<union> fst (trans2LTS r2 alp_set), 
                                        snd (trans2LTS r1 alp_set) \<union> snd (trans2LTS r2 alp_set) \<union> {(Alter r1 r2, r1),(Alter r1 r2, r2)})"|
    "trans2LTS (Star r) alp_set = (renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r)), 
                                   (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r))) \<union> {(Star r, \<epsilon>),(Star r,Concat r (Star r)),(Concat \<epsilon> (Star r), Star r)})"|
    "trans2LTS (Plus r) alp_set = ((renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp2 (Star r))) \<union> (renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r))), 
                                   {(Plus r, Concat (Concat r (Star r)) (Star r)),(Concat (Concat \<epsilon> (Star r)) (Star r),Concat (Star r) (Star r)),(Concat (Star r) (Star r), \<epsilon>),(Concat (Star r) (Star r), Concat r (Star r)),(Concat \<epsilon> (Star r), Concat (Star r) (Star r))}
                                    \<union>(renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp2 (Star r))) \<union> (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r))))"|
    "trans2LTS (Ques r) alp_set = (fst (trans2LTS r alp_set),
                                   {(Ques r,\<epsilon>), (Ques r, r)} \<union> snd (trans2LTS r alp_set))"


primrec reg2q :: "'v regexp \<Rightarrow> 'v set\<Rightarrow>  ('v regexp) set" where
    "reg2q Dot a = {Dot, \<epsilon>}"|
    "reg2q (LChr p) a =  {(LChr p), \<epsilon>}"|
    "reg2q (Alter r1 r2) a = {(Alter r1 r2),\<epsilon>} \<union> reg2q r1 a \<union> reg2q r2 a"|
    "reg2q (Star r) a = {\<epsilon>, Star r} \<union> reg2q r a \<union> (\<lambda>x. ConcatRegexp x (Star r)) ` (reg2q r a)" |
    "reg2q (Plus r) a =  {Plus r, \<epsilon>} \<union> {Concat r (Star r), (Concat \<epsilon> (Star r))} \<union> {Star r} \<union> reg2q r a \<union> (\<lambda>x. ConcatRegexp x (Star r)) ` (reg2q r a)" |
    "reg2q (Ques r) a = {(Ques r), \<epsilon>} \<union> reg2q r a" |
    "reg2q ESet a = {ESet, \<epsilon>}"|
    "reg2q \<epsilon> a = {\<epsilon>}"|
    "reg2q (Concat r1 r2) a = {Concat r1 r2, r2, \<epsilon>, (Concat \<epsilon> r2)}"

fun reg2nfa :: "'v regexp \<Rightarrow> 'v set\<Rightarrow> ('v regexp,'v) NFA_rec" where 
    "reg2nfa r a= \<lparr>  \<Q> = reg2q r a,
                  \<Sigma> = alp_reg  r a,
                  \<Delta> = fst (trans2LTS  r a),
                  \<Delta>' = snd (trans2LTS  r a),
                  \<I> ={r}, 
                  \<F> ={\<epsilon>}\<rparr> " 

section "function correctness of transition from regexp expression to  nondeterministic finite automaton"

theorem uniqueInitalState:"\<I> (reg2nfa r v) = {r}"
  apply (induct r)
  by auto

lemma " ((r1, r1) ∈ snd (trans2LTS r1 v) ⟹ False) ⟹
    ((r2, r2) ∈ snd (trans2LTS r2 v) ⟹ False) ⟹ (Concat r1 r2, Concat r1 r2) ∈ snd (trans2LTS (Concat r1 r2) v) ⟹ False"
  sorry

theorem uniqueFinalState:"\<F> (reg2nfa r v) = {\<epsilon>}"
  apply(induct r)
  by auto

lemma "(r, r) ∈ snd (trans2LTS r v) \<Longrightarrow> False"
  apply(induction r)
  subgoal 
    by auto
  subgoal for x
    by auto
  subgoal for r1 r2  apply  auto sorry
  subgoal for r1 r2 apply simp sorry
  subgoal by auto
  subgoal for r by auto
  subgoal for r by auto
  subgoal for r apply auto sorry
  subgoal by auto
done

lemma "¬ LTS_is_reachable (trans2LTS r2 v) r2 x ε \<Longrightarrow>  LTS_is_reachable (fst (trans2LTS r2 v), (insert (Alter r1 r2, r2) (snd (trans2LTS r2 v)))) (Alter r1 r2) [] r2\<Longrightarrow>
  ¬ LTS_is_reachable (fst (trans2LTS r2 v), (insert (Alter r1 r2, r2) (snd (trans2LTS r2 v)))) (Alter r1 r2) x ε"
  sorry

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
    by(rule LTS_is_reachable.cases) auto
  done
next
  case (Alter r1 r2)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for x
    proof -
      assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w \<epsilon>}"
      assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w \<epsilon>}"
      assume a3:"LTS_is_reachable (trans2LTS r1 v) r1 x \<epsilon>"
      then show "LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) x \<epsilon>"
     proof -
        have c1:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) [] r1" 
          by (metis LTS_Empty LTS_Step1 insertI1 snd_conv)
        from a3 have c2:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) r1 x \<epsilon>"
          by (metis Un_insert_right subLTSlemma)
        from c1 c2 have "LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) x \<epsilon>"
          by (metis LTS_Step1 insertI1 snd_eqD)
        then show ?thesis by auto
      qed
    qed
     subgoal for x
      proof -
      assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w \<epsilon>} "
      assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w \<epsilon>}"
      assume a3:"LTS_is_reachable (trans2LTS r2 v) r2 x \<epsilon>"
      then show "LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) x \<epsilon>"
      proof -
        have c1:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) [] r2" 
          by (metis LTS_Empty LTS_Step1 insertI1 insertI2 snd_eqD)
        have c2:"LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) r2 x \<epsilon>"
          using a3 
          by (smt (z3) Un_commute Un_insert_right subLTSlemma)
        have "LTS_is_reachable (fst (trans2LTS r1 v) \<union> fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) \<union> snd (trans2LTS r2 v)))) (Alter r1 r2) x \<epsilon>"
          using c1 c2 
          by (metis LTS_Step1 insertI1 insertI2 snd_eqD)
        then show ?thesis by auto
       qed
     qed
     subgoal for x
     proof -
       assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w ε}"
       assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w ε}"
       assume a3:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)))) (Alter r1 r2) x ε"
       assume a4:"¬ LTS_is_reachable (trans2LTS r2 v) r2 x ε" 
       show "LTS_is_reachable (trans2LTS r1 v) r1 x ε"
         sorry
     qed
   done
 next
  case (Concat r1 r2)
  then show ?case 
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for q p
    proof -
    assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w \<epsilon>}"
    assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w \<epsilon>}"
    assume a3:"LTS_is_reachable (trans2LTS r1 v) r1 q \<epsilon>"
    assume a4:"LTS_is_reachable (trans2LTS r2 v) r2 p \<epsilon>"
    show "LTS_is_reachable
     ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
      insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
     (Concat r1 r2) (q @ p) ε"
    proof-
      have c1:"LTS_is_reachable
     ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)},({(Concat q r2, Concat q' r2) |q q'. (q, q') \<in> snd (trans2LTS r1 v)})) (Concat r1 r2) q (Concat \<epsilon> r2)"
        using a3   
        apply (induction rule: LTS_is_reachable.induct)  
        apply auto
        apply (metis (mono_tags, lifting) CollectI LTS_Step1 snd_conv)
        by blast
      then have c2:"LTS_is_reachable
     ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)},
      insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
             (Concat r1 r2) q (Concat \<epsilon> r2)"
        apply (induction rule: LTS_is_reachable.cases)
          subgoal for lts qa
            by auto
          subgoal for qa lts l q'
            apply auto
            by (smt (z3) Un_commute c1 fst_conv insert_def snd_conv subLTSlemma sup_idem)
          subgoal for a qa lts w q'
            apply auto 
            by (smt (z3) Un_commute Un_insert_left fst_conv snd_conv subLTSlemma sup_idem)
        done
      then have c3:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)} \<union> fst (trans2LTS r2 v),
            insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
            (Concat r1 r2) q (Concat \<epsilon> r2)"
        by (metis (no_types, lifting) Un_insert_right c1 fst_eqD snd_conv subLTSlemma)
        have c4:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)} \<union> fst (trans2LTS r2 v),
            insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
          (Concat \<epsilon> r2) [] r2"
        by (smt (z3) LTS_Empty LTS_Step1 insertI1 insert_commute snd_conv)
        have c5:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)} \<union> fst (trans2LTS r2 v),
            insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
         r2 p \<epsilon>"
        using a4 
        by (smt (z3) insert_def subLTSlemma sup.commute sup_left_commute)
      have "LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') \<in> fst (trans2LTS r1 v)} \<union> fst (trans2LTS r2 v),
            insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
           (Concat r1 r2) (q @ p) \<epsilon>" using c3 c4 c5 
        by (smt (z3) append.right_neutral joinLTSlemma)
      thus ?thesis by auto
    qed
  qed
  subgoal for x 
  proof -
    assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w \<epsilon>}"
    assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w \<epsilon>}"
    assume a3:"LTS_is_reachable
     ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
      insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))
     (Concat r1 r2) x ε"
    show  "\<exists>q p. x = q @ p \<and> LTS_is_reachable (trans2LTS r1 v) r1 q \<epsilon> \<and> LTS_is_reachable (trans2LTS r2 v) r2 p \<epsilon>"
      sorry
qed
  done
next
  case (Plus r)
  then show ?case  
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for q p
    proof -
      assume a1:"sem_reg r v = {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
      assume a2:"LTS_is_reachable (trans2LTS r v) r q \<epsilon>"
      assume a3:"p \<in> star {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
      show "LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
            {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))  (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r))
            (insert (Concat ε (Star r), Concat (Star r) (Star r)) ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪
            {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
            (Plus r) (q @ p) ε"
      proof -
          have c1:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                  {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))  (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r))
                  (insert (Concat ε (Star r), Concat (Star r) (Star r)) ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪
                  {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                 (Plus r) [] (Concat (Concat r (Star r)) (Star r))"
            by (simp add: LTS_Empty LTS_Step1)
          have e1:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)},{(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)})
                  (Concat (Concat r (Star r)) (Star r)) q (Concat (Concat \<epsilon> (Star r)) (Star r))"
            using a2 by (rule DeltLTSlemma1)
          have c2:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                  {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))  (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r))
                  (insert (Concat ε (Star r), Concat (Star r) (Star r)) ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪
                  {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                  (Concat (Concat r (Star r)) (Star r)) q (Concat (Concat \<epsilon> (Star r)) (Star r))"
            using e1   by (metis (no_types, lifting) Un_insert_right fst_eqD snd_eqD subLTSlemma)
          have 1:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                  {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r)) (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r))
                  (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r)) ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪
                  {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                  (Plus r) q (Concat (Concat \<epsilon> (Star r)) (Star r))"
            using c1 c2 joinLTSlemma by fastforce
          have c3:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                  {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r)) (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r))
                  (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r)) ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪
                  {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                  (Concat (Concat \<epsilon> (Star r)) (Star r)) []  (Concat (Star r) (Star r))" 
            by (smt (z3) LTS_Empty LTS_Step1 insertI1 insert_commute snd_conv)
          have 2:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                  {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r)) (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r))
                  (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r)) ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪
                  {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                  (Plus r) q  (Concat (Star r) (Star r))" using 1 c3 joinLTSlemma by fastforce
          have 3:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                    {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r)) (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r))
                    (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r)) ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪
                    {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                   (Concat (Star r) (Star r)) p \<epsilon>"
                using a3 proof(induction p)
                  case zero
                  then show ?case 
                    by (smt (z3) LTS_Empty LTS_Step1 insertI1 insert_commute snd_conv)
                next
                  case (step x y)
                  then show ?case apply auto proof -
                    assume a1:"LTS_is_reachable (trans2LTS r v) r x \<epsilon>"
                    assume a2:"y \<in> star {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
                    assume a3:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                              {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))
                              (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r))
                              ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪ {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                              (Concat (Star r) (Star r)) y ε"
                    have e1:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)}, 
                          {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)}) (Concat r (Star r)) x (Concat \<epsilon> (Star r))"
                      using a1 by(simp add:DeltLTSlemma1)
                    have e2:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                              {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))
                              (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r))
                              ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪ {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                              (Concat (Star r) (Star r)) [] (Concat r (Star r))"
                      by (smt (z3) LTS_Empty LTS_Step1 insertCI snd_conv)
                   have c1:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                              {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))
                              (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r))
                              ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪ {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                             (Concat r (Star r)) x (Concat \<epsilon> (Star r))"
                     using e1   by (smt (z3) Un_left_commute fst_conv inf_sup_aci(5) insert_def snd_conv subLTSlemma)
                    have e3:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                              {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))
                              (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r))
                              ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪ {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                              (Concat (Star r) (Star r)) x (Concat \<epsilon> (Star r))"
                      using e2 c1 joinLTSlemma by fastforce
                    have c2:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                              {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))
                              (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r))
                              ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪ {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                              (Concat \<epsilon> (Star r)) [] (Concat (Star r) (Star r))"
                      by (smt (z3) LTS_Empty LTS_Step1 insertCI snd_conv)
                    have e4:"LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
                              {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r))
                              (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r)) (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r))
                              ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪ {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
                              (Concat (Star r) (Star r)) x (Concat (Star r) (Star r))"using e3 c2 joinLTSlemma by fastforce
                    thus ?thesis using e4 a3 joinLTSlemma by fastforce
                  qed
                qed
              thus ?thesis using 2 3 joinLTSlemma by fastforce
        qed
     qed
    subgoal for x 
    proof -
      assume "sem_reg r v = {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
      assume "LTS_is_reachable ({(Concat (Concat q (Star r)) (Star r), va, Concat (Concat q' (Star r)) (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)} ∪
              {(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') ∈ fst (trans2LTS r v)}, insert (Plus r, Concat (Concat r (Star r)) (Star r)) (insert (Concat (Concat ε (Star r)) (Star r), Concat (Star r) (Star r))
              (insert (Concat (Star r) (Star r), ε) (insert (Concat (Star r) (Star r), Concat r (Star r)) (insert (Concat ε (Star r), Concat (Star r) (Star r)) ({(Concat (Concat q (Star r)) (Star r), Concat (Concat q' (Star r)) (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)} ∪
              {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') ∈ snd (trans2LTS r v)}))))))
              (Plus r) x ε"
      show "\<exists>q p. x = q @ p \<and> LTS_is_reachable (trans2LTS r v) r q \<epsilon> \<and> p \<in> star {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"  
        sorry 
    qed
    done
next
  case (Star r)
  then show ?case 
     apply(unfold \<L>_def NFA_accept_def)
     apply auto 
    subgoal for x 
    proof -
      assume a1:"sem_reg r v = {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
      assume a2:"x \<in> star {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
      show "LTS_is_reachable
     ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)},
      insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
     (Star r) x \<epsilon>" 
        using a2 proof (induction x)
        case zero
        then show ?case
          by (metis (no_types, lifting) LTS_Empty LTS_Step1 insertI1 snd_conv)
      next
        case (step x y)
        then show ?case apply auto 
        proof -
          assume a1:"LTS_is_reachable (trans2LTS r v) r x \<epsilon>"
          assume a2:"y \<in> star {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
          assume a3:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)},
                    insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                   (Star r) y \<epsilon>"
          show "LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)},
                    insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                   (Star r) (x @ y) \<epsilon>"
          proof -
            have c1:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)},
                    insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                    (Star r) [] (Concat r (Star r))"
              by (smt (z3) LTS_Empty LTS_Step1 insert_iff snd_conv)
            have c2:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} , {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})
                    (Concat r (Star r)) x (Concat \<epsilon> (Star r))"
              using a1 by(simp add:DeltLTSlemma1)
            have c4:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> fst (trans2LTS r v),
                    {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})
                    (Concat r (Star r)) x (Concat \<epsilon> (Star r))"
              using c2 by (smt (verit, best) Collect_cong Collect_disj_eq fst_eqD snd_eqD subLTSlemma)
            have c5:"LTS_is_reachable ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> fst (trans2LTS r v),
                     (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)}))
                     (Concat r (Star r)) x (Concat \<epsilon> (Star r))"
              using c4 
              by (smt (verit, best) Collect_cong Collect_disj_eq Un_insert_right c2 fst_eqD snd_eqD subLTSlemma)
            have c6:"LTS_is_reachable  ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)} \<union> fst (trans2LTS r v),
                    (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                    (Concat r (Star r)) x (Concat \<epsilon> (Star r))"
              using c5 by (metis (no_types, lifting) Pair_inject Un_absorb Un_insert_right prod.collapse subLTSlemma)
            have c7:"LTS_is_reachable
                    ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)},
                    insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                    (Concat r (Star r)) x (Concat \<epsilon> (Star r))"
              by (metis (no_types, lifting) Un_insert_right c2 fst_conv snd_conv subLTSlemma sup.idem)
            have c8:"LTS_is_reachable
                    ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)},
                    insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                    (Star r) x (Concat \<epsilon> (Star r))"
              using c1 c7 by (smt (z3) LTS_Step1 insertI1 insert_commute snd_conv)
            have c9:"LTS_is_reachable
                    ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)},
                    insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                    (Concat \<epsilon> (Star r)) [] (Star r)"
              by (metis (no_types, lifting) LTS_Empty LTS_Step1 insertCI snd_conv)
            have c10:"LTS_is_reachable
                    ({(Concat q (Star r), va, Concat q' (Star r)) |q va q'. (q, va, q') \<in> fst (trans2LTS r v)},
                    insert (Star r, \<epsilon>) (insert (Star r, Concat r (Star r)) (insert (Concat \<epsilon> (Star r), Star r) {(Concat q (Star r), Concat q' (Star r)) |q q'. (q, q') \<in> snd (trans2LTS r v)})))
                    (Star r) x (Star r)"
              using c8 c9 joinLTSlemma by fastforce              
            thus ?thesis using a3 c10 joinLTSlemma 
              by force 
          qed
        qed
      qed
    qed
    subgoal for x sorry
    done
next
  case (Ques r)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto 
    subgoal 
    proof -
      assume "sem_reg r v = {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
      show "LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, \<epsilon>) (insert (Ques r, r) (snd (trans2LTS r v)))) (Ques r) [] \<epsilon>"
        by (metis LTS_Empty LTS_Step1 insertI1 snd_conv)
    qed
    subgoal for x
    proof -
      assume a1:"sem_reg r v = {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
      assume a2:"LTS_is_reachable (trans2LTS r v) r x \<epsilon>"
      show "LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, \<epsilon>) (insert (Ques r, r) (snd (trans2LTS r v)))) (Ques r) x \<epsilon>"
      proof -
        from a2 have c1:"LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, \<epsilon>) (insert (Ques r, r) (snd (trans2LTS r v)))) r x \<epsilon>"
          apply(induction rule:LTS_is_reachable.induct)
          subgoal 
            by auto
          subgoal for q lts l q'
            apply auto
            by (smt (verit, best) LTS_Step1 Un_insert_right subLTSlemma sup_idem)
          subgoal for a q lts w q'
            apply auto
            by (metis Un_insert_right boolean_algebra_cancel.sup0 subLTSlemma)
          done
        have "LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, \<epsilon>) (insert (Ques r, r) (snd (trans2LTS r v)))) (Ques r) x \<epsilon>"
          using c1
          by (smt (verit, best) LTS_Step1 insertI1 insert_commute snd_conv)
        thus ?thesis by auto
      qed
    qed
    subgoal for x
    proof -
      assume a1:"sem_reg r v = {w. LTS_is_reachable (trans2LTS r v) r w \<epsilon>}"
      assume a2:"LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, \<epsilon>) (insert (Ques r, r) (snd (trans2LTS r v)))) (Ques r) x \<epsilon>"
      assume a3:"x \<noteq> []" 
      show "LTS_is_reachable (trans2LTS r v) r x \<epsilon>"
        sorry
    qed
    done
qed
end