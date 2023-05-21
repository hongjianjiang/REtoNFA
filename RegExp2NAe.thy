(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "From regular expressions to nondeterministic automata with epsilon"

theory RegExp2NAe
imports Regular_Exp NAe
begin

type_synonym 'a bitsNAe = "('a,nat list)nae"

fun mapLR ::"nat list set \<Rightarrow> nat list set \<Rightarrow> nat list set" where 
"mapLR A B = {[length a] @ a @ b|a b. a \<in> A \<and> b \<in> B}"

fun transform::"'a \<Rightarrow> 'a option" where
"transform a = Some a"

definition
"atom"  :: "'a \<Rightarrow> 'a option set \<Rightarrow>'a bitsNAe" where
"atom a vs= ([2], vs,
            \<lambda>b s. if s=[2] \<and> b=Some a then {[3]} else {},
            \<lambda>s. s=[3])"

definition
 epsilon :: "'a option set \<Rightarrow>'a bitsNAe" where
"epsilon vs= ([], vs, \<lambda>a s. {}, \<lambda>s. s=[])"

definition 
  dot ::  "'a option set \<Rightarrow> 'a bitsNAe" where
"dot vs=([2], vs,
            \<lambda>b s. if s=[2] \<and> b \<in> vs \<and> b \<noteq> None then {[3]} else {},
            \<lambda>s. s=[3])"

definition
 or :: "'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"or = (\<lambda>(ql,vl,dl,fl)(qr,vr,dr,fr).
   ([],vl\<union>vr,
    \<lambda>a s. case s of
            [] \<Rightarrow> if a=None then {2#ql,3#qr} else {}
          | left#s \<Rightarrow> if left = 2 then 2 ## dl a s
                              else 3 ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> if left = 2 then fl s else fr s))"

definition
 conc :: "'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"conc = (\<lambda>(ql,vl,dl,fl)(qr,vr,dr,fr).
   (2#ql, vl\<union>vr,
    \<lambda>a s. case s of
            [] \<Rightarrow> {}
          | left#s \<Rightarrow> if left = 2 then (2 ## dl a s) \<union>
                                   (if fl s \<and> a=None then {3#qr} else {})
                              else 3 ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> left = 3 \<and> fr s))"

definition
 star :: "'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"star = (\<lambda>(q,v,d,f).
   ([],v,
    \<lambda>a s. case s of
            [] \<Rightarrow> if a=None then {2#q} else {}
          | left#s \<Rightarrow> if left = 2 then (2 ## d a s) \<union>
                                   (if f s \<and> a=None then {2#q} else {})
                              else {},
    \<lambda>s. case s of [] \<Rightarrow> True | left#s \<Rightarrow> left = 2 \<and> f s))"

definition
  inter :: " 'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"inter= (\<lambda>(ql,vl1,dl,fl)(qr,vl2,dr,fr).
   ([length ql] @ ql @ qr,vl1 \<inter> vl2,
    \<lambda>a s. mapLR (dl a (take (hd s) (tl s))) (dr a (drop (hd s) (tl s))),
    \<lambda>s. case s of [] \<Rightarrow> False | left # s \<Rightarrow> fl (take left s) \<and> fr (drop  left  s)))"

definition
timesN :: "'a bitsNAe \<Rightarrow> nat\<Rightarrow>'a bitsNAe" where
  "timesN = (\<lambda>(q,vs,d,f) n. (1#q, vs, \<lambda>a s. ((hd s) ## d a (tl s)) \<union> (if f (tl s) then (hd s + 1) ## d a q else {}), 
  \<lambda>s. (hd s) = n \<and> f (tl s)))"


primrec rexp2nae :: "'a rexp \<Rightarrow> 'a option set \<Rightarrow> 'a bitsNAe" where
"rexp2nae Zero   vs    = ([], vs, \<lambda>a s. {}, \<lambda>s. False)" |
"rexp2nae One    vs    = epsilon vs" |
"rexp2nae(Atom a)  vs    = atom a vs" |
"rexp2nae(Alter r s) vs  = or (rexp2nae r vs) (rexp2nae s vs)" |
"rexp2nae(Times r s) vs = conc (rexp2nae r vs) (rexp2nae s vs)" |
"rexp2nae(Star r)  vs  = star (rexp2nae r vs)"|
"rexp2nae(Dot) vs = dot vs"|
"rexp2nae(Ques r) vs = or (rexp2nae r vs) (epsilon vs)"|
"rexp2nae(Plus r) vs = conc (rexp2nae r vs) (star (rexp2nae r vs))" |
"rexp2nae(Inter r s) vs = inter (rexp2nae r vs) (rexp2nae s vs)"|
"rexp2nae(Multi r m) vs = timesN (rexp2nae r vs) m"

declare split_paired_all[simp]

(******************************************************)
(*                     epsilon                        *)
(******************************************************)

lemma step_epsilon[simp]: "step (epsilon vs) a = {}"
by(simp add:epsilon_def step_def)

lemma steps_epsilon: "((p,q) : steps (epsilon vs) w) = (w=[] \<and> p=q)"
by (induct "w") auto

lemma accepts_epsilon[simp]: "accepts (epsilon vs) w = (w = [])"
apply (simp add: steps_epsilon accepts_def)
apply (simp add: epsilon_def)
done

(******************************************************)
(*                       atom                         *)
(******************************************************)

lemma fin_atom: "(fin ((atom vs) a) q) = (q = [3])"
by(simp add:atom_def)

lemma start_atom: "start ((atom vs) a) = [2]"
by(simp add:atom_def)

(* Use {x. False} = {}? *)

lemma eps_atom[simp]:
 "eps((atom vs) a) = {}"
by (simp add:atom_def step_def)

lemma in_step_atom_Some[simp]:
 "(p,q) : step (atom a vs)  (Some b) = (p=[2] \<and> q=[3] \<and> b=a)"
by (simp add:atom_def step_def)

lemma False_False_in_steps_atom:
  "([3],[3]) : steps (atom a vs) w = (w = [])"
apply (induct "w")
apply (simp)
apply (simp add: relcomp_unfold)
done

lemma start_fin_in_steps_atom:
  "(start (atom a vs), [3]) : steps (atom a vs) w = (w = [a])"
apply (induct "w")
apply (simp add: start_atom)
apply (simp add: False_False_in_steps_atom relcomp_unfold start_atom)
done

lemma accepts_atom: "accepts (atom a vs) w = (w = [a])"
by (simp add: accepts_def start_fin_in_steps_atom fin_atom)



(******************************************************)
(*                       dot                          *)
(******************************************************)
lemma fin_dot: "(fin (dot vs) q) = (q = [3])"
  by (simp add: dot_def)
 
lemma start_dot: "start (dot vs) = [2]"
  by(simp add:dot_def)

lemma in_step_dot_Some[simp]:
 "(p,q) : step (dot vs) b= (p=[2] \<and> q=[3] \<and> b \<in> vs \<and> b \<noteq> None)"
by (simp add: dot_def step_def)


lemma False_False_in_steps_dot:
 "([3],[3]) : steps (dot vs) w = (w = [])"
  apply (induct "w")
  apply simp
  apply (simp add: relcomp_unfold) 
  by (metis converse_rtranclE in_step_dot_Some list.inject numeral_eq_iff semiring_norm(89))

lemma eps_dot[simp]:
 "eps((dot vs)) = {}"
by (simp add:dot_def step_def)
 

lemma start_fin_in_steps_do:
 "(start (dot vs), [3]) : steps (dot vs) w = (w \<in> ({[a] |a. (Some a) \<in> vs}))"
apply (induct "w")
apply (simp add: start_dot)
apply (simp add: False_False_in_steps_dot relcomp_unfold start_dot) 
apply auto
done

lemma accepts_dot:  "accepts (dot vs) w = (w \<in> ({[a] |a. (Some a) \<in> vs}))"
apply (simp add: accepts_conv_steps fin_dot start_fin_in_steps_do)
by (simp add: NAe.accepts_def fin_dot start_fin_in_steps_do)


(******************************************************)
(*                      or                            *)
(******************************************************)

(***** lift True/False over fin *****)

lemma fin_or_True[iff]:
 "\<And>L R. fin (or L R) (2#p) = fin L p"
by(simp add:or_def)

lemma fin_or_False[iff]:
 "\<And>L R. fin (or L R) (3#p) = fin R p"
by(simp add:or_def)

(***** lift True/False over step *****)

lemma True_in_step_or[iff]:
"\<And>L R. (2#p,q) : step (or L R) a = (\<exists>r. q = 2#r \<and> (p,r) : step L a)"
apply (simp add:or_def step_def)
apply blast
done

lemma False_in_step_or[iff]:
"\<And>L R. (3#p,q) : step (or L R) a = (\<exists>r. q = 3#r \<and> (p,r) : step R a)"
apply (simp add:or_def step_def)
apply blast
done


(***** lift True/False over epsclosure *****)

lemma lemma1a:
 "(tp,tq) : (eps(or L R))\<^sup>* \<Longrightarrow> 
 (\<And>p. tp = 2#p \<Longrightarrow>  \<exists>q. (p,q) : (eps L)\<^sup>* \<and> tq = 2#q)"
apply (induct rule:rtrancl_induct)
apply (blast)
apply (clarify)
apply (simp)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma1b:
 "(tp,tq) : (eps(or L R))\<^sup>* \<Longrightarrow>  
 (\<And>p. tp = 3#p \<Longrightarrow>  \<exists>q. (p,q) : (eps R)\<^sup>* \<and> tq = 3#q)"
apply (induct rule:rtrancl_induct)
apply (blast)
apply (clarify)
apply (simp)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma2a:
 "(p,q) : (eps L)\<^sup>*  \<Longrightarrow>  (2#p, 2#q) : (eps(or L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma2b:
 "(p,q) : (eps R)\<^sup>*  \<Longrightarrow>  (3#p, 3#q) : (eps(or L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma True_epsclosure_or[iff]:
 "(2#p,q) : (eps(or L R))\<^sup>* = (\<exists>r. q = 2#r \<and> (p,r) : (eps L)\<^sup>*)"
by (blast dest: lemma1a lemma2a)

lemma False_epsclosure_or[iff]:
 "(3#p,q) : (eps(or L R))\<^sup>* = (\<exists>r. q = 3#r \<and> (p,r) : (eps R)\<^sup>*)"
by (blast dest: lemma1b lemma2b)

(***** lift True/False over steps *****)

lemma lift_True_over_steps_or[iff]:
 "\<And>p. (2#p,q):steps (or L R) w = (\<exists>r. q = 2 # r \<and> (p,r):steps L w)"
apply (induct "w")
apply auto
apply force
done

lemma lift_False_over_steps_or[iff]:
 "\<And>p. (3#p,q):steps (or L R) w = (\<exists>r. q = 3#r \<and> (p,r):steps R w)"
apply (induct "w")
apply auto
apply (force)
done

(***** Epsilon closure of start state *****)

lemma unfold_rtrancl2:
 "R\<^sup>* = Id \<union> (R O R\<^sup>*)"
apply (rule set_eqI)
apply (simp)
apply (rule iffI)
apply (erule rtrancl_induct)
apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
apply (blast intro: converse_rtrancl_into_rtrancl)
done

lemma in_unfold_rtrancl2:
 "(p,q) : R\<^sup>* = (q = p | (\<exists>r. (p,r) : R \<and> (r,q) : R\<^sup>*))"
apply (rule unfold_rtrancl2[THEN equalityE])
apply (blast)
done

lemmas [iff] = in_unfold_rtrancl2[where ?p = "start(or L R)"] for L R

lemma start_eps_or[iff]:
 "\<And>L R. (start(or L R),q) : eps(or L R) = 
       (q = 2#start L | q = 3#start R)"
by (simp add:or_def step_def)

lemma not_start_step_or_Some[iff]:
 "\<And>L R. (start(or L R),q) \<notin> step (or L R) (Some a)"
by (simp add:or_def step_def)

lemma steps_or:
 "(start(or L R), q) : steps (or L R) w = 
 ( (w = [] \<and> q = start(or L R)) | 
   (\<exists>p.  q = 2  # p \<and> (start L,p) : steps L w | 
         q = 3 # p \<and> (start R,p) : steps R w) )"
apply (case_tac "w")
apply (simp)
apply (blast)
apply (simp)
apply (blast)
done

lemma start_or_not_final[iff]:
 "\<And>L R. \<not> fin (or L R) (start(or L R))"
by (simp add:or_def)

lemma accepts_or:
 "accepts (or L R) w = (accepts L w | accepts R w)"
apply (simp add:accepts_def steps_or)
apply auto
done
(******************************************************)
(*                     inter                          *)
(******************************************************)

lemma fin_inter[iff]:
 "\<And>L R q. fin (inter L R) q = (\<exists>m n. q = m # n \<and> fin  L (take m n) \<and> fin R (drop m n))"
  apply (simp add:inter_def) 
  apply (case_tac q) 
  apply auto 
  done
 
lemma start_inter[iff]:
  "\<And>L R. start(inter L R) = [length (start L)] @ start L @ start R"
  by (simp add:inter_def)


lemma step_inter[iff]:
"\<And>L R. (p,q) : step (inter L R) a = (\<exists>r1 r2. q = [length r1] @ r1 @ r2 
                                      \<and> (take (hd p) (tl p), r1) \<in> step L a 
                                      \<and> (drop (hd p) (tl p),r2) \<in> step R a)"
  apply (simp add:inter_def step_def) 
  done



lemma inter_eps_left[simp]:"\<And>L R p. (p, q) \<in> eps (inter L R) \<Longrightarrow> ((take (hd p) (tl p), take (hd q) (tl q)) \<in> eps L)"
   by fastforce

lemma inter_eps_right[simp]:"\<And>L R p. (p, q) \<in> eps (inter L R) \<Longrightarrow> ((drop (hd p) (tl p), drop (hd q) (tl q)) \<in> eps R)"
  by fastforce

lemma eps_L_inter:"(n#p, q) \<in> (eps (inter L R))\<^sup>* \<Longrightarrow>  (take n p, take (hd q) (tl q))\<in> (eps L)\<^sup>*"
  apply(induct rule:rtrancl_induct)
  apply simp
  apply (simp)
  apply fastforce
  done

lemma eps_L_inter1:"(p, q) \<in> (eps (inter L R))\<^sup>* \<Longrightarrow>  (take (hd p) (tl p), take (hd q) (tl q))\<in> (eps L)\<^sup>*"
  apply(induct rule:rtrancl_induct)
  apply simp
  apply (simp)
  apply fastforce
  done

lemma eps_R_inter1:"(p, q) \<in> (eps (inter L R))\<^sup>* \<Longrightarrow> (drop (hd p) (tl p), drop (hd q) (tl q)) \<in> (eps R)\<^sup>*"
  apply(induct rule:rtrancl_induct)
  apply simp
  apply (simp)
  apply fastforce
  done

lemma eps_R_inter:"(n#p, q) \<in> (eps (inter L R))\<^sup>* \<Longrightarrow>  ((drop n p, drop (hd q) (tl q)) \<in> (eps R)\<^sup>*)"
  apply(induct rule:rtrancl_induct)
  apply simp
  apply (simp)
  apply fastforce
  done 


   
lemma step_from_left: "\<And>p. (n#p, q) \<in> steps (inter L R) w \<Longrightarrow> ((take n p, take (hd q) (tl q)) \<in> steps L w)"
  apply(induction w)
  apply simp
  apply (simp add: eps_L_inter eps_R_inter)
  apply simp
  apply clarify
proof -
  fix a w p x y z xa ya za r1 r2
  assume a1:"(\<And>p. (n # p, q) \<in> NAe.steps (RegExp2NAe.inter L R) w \<Longrightarrow>
             (take n p, take (hd q) (tl q)) \<in> NAe.steps L w)"
  assume a2:"(n # p, xa) \<in> (eps (RegExp2NAe.inter L R))\<^sup>*"
  assume a3:"([length r1] @ r1 @ r2, q) \<in> NAe.steps (RegExp2NAe.inter L R) w"
  assume a4:"(take (hd xa) (tl xa), r1) \<in> step L (Some a)"
  assume a5:"(drop (hd xa) (tl xa), r2) \<in> step R (Some a)"
  show "(take n p, take (hd q) (tl q))
       \<in> (eps L)\<^sup>* O step L (Some a) O NAe.steps L w "
  proof -
    from a2 have c1:"(take n p, take (hd xa) (tl xa)) \<in> (eps L)\<^sup>*" 
      by (simp add: eps_L_inter)
    from c1 a4 have c2:"(take n p, r1) \<in> (eps L)\<^sup>* O step L (Some a) "  
      by blast
    from a1 a3 have c3:"(r1, take (hd q) (tl q)) \<in> NAe.steps L w"  sorry
    from c2 c3 show ?thesis apply auto done
  qed
qed


lemma step_from_right: "\<And>p. (n#p, q) \<in> steps (inter L R) w \<Longrightarrow> ((drop n p, drop (hd q) (tl q)) \<in> steps R w)"
  apply(induct w)
  apply simp
  using eps_R_inter apply blast
  apply simp 
  apply clarify
proof -
  fix a w p x y z xa ya za r1 r2
  assume a1:"(\<And>p. (n # p, q) \<in> NAe.steps (RegExp2NAe.inter L R) w \<Longrightarrow>
             (drop n p, drop (hd q) (tl q)) \<in> NAe.steps R w)"
  assume a2:"(n # p, xa) \<in> (eps (RegExp2NAe.inter L R))\<^sup>*"
  assume a3:"([length r1] @ r1 @ r2, q) \<in> NAe.steps (RegExp2NAe.inter L R) w"
  assume a4:"(take (hd xa) (tl xa), r1) \<in> step L (Some a)"
  assume a5:"(drop (hd xa) (tl xa), r2) \<in> step R (Some a)"
  show "(drop n p, drop (hd q) (tl q))
       \<in> (eps R)\<^sup>* O step R (Some a) O NAe.steps R w"
  proof -
    from a2 have c1:"(drop n p, drop (hd xa) (tl xa)) \<in> (eps R)\<^sup>*"  
      using eps_R_inter by blast
    from c1 a5 have c2:"(drop n p, r2) \<in> (eps R)\<^sup>* O step R (Some a)"  
      by blast
    from a1 a3 have c3:"(r2, drop (hd q) (tl q)) \<in> NAe.steps R w"
      sorry
    from c2 c3 show ?thesis by auto
  qed
qed

lemma step_from_left_right: "\<And>p. (n#p, q) \<in> steps (inter L R) w \<Longrightarrow> ((take n p, take (hd q) (tl q)) \<in> steps L w \<and> (drop n p, drop (hd q) (tl q)) \<in> steps R w)"
  by (simp add: step_from_left step_from_right)

(** From the start  **)
lemma start_step_inter[iff]:
 "\<And>L R r1 r2. (start(inter L R),q) : step(inter L R) a = 
         (\<exists> r1 r2. q = length r1 # r1 @ r2 \<and> (start L,r1) : step L a \<and> (start R, r2) \<in> step R a )"
 apply (simp add:inter_def step_def)  
done

lemma steps_inter:"\<And>L R. (start (inter L R) ,q) \<in> steps (inter L R) w  \<Longrightarrow> 
    ((start L,take (hd q) (tl q)) \<in> steps L w \<and> (start R, (drop (hd q) (tl q))) \<in> steps R w)"
  apply(induct w)
  apply simp 
  apply (metis append_eq_conv_conj eps_L_inter1 eps_R_inter list.sel(1) list.sel(3))
  apply simp 
  by (metis NAe.steps.simps(2) append_eq_conv_conj step_from_left_right)

lemma accepts_inter:
 "accepts (inter L R) w = (accepts L w \<and> accepts R w)"
  apply(simp add:accepts_def steps_inter)
  apply(case_tac w)
  apply simp 
  sorry

(******************************************************)
(*                      conc                          *)
(******************************************************)

(** True/False in fin **)

lemma in_conc_True[iff]:
 "\<And>L R. fin (conc L R) (2#p) = False"
by (simp add:conc_def)

lemma fin_conc_False[iff]:
 "\<And>L R. fin (conc L R) (3#p) = fin R p"
by (simp add:conc_def)

(** True/False in step **)

lemma True_step_conc[iff]:
 "\<And>L R. (2#p,q) : step (conc L R) a = 
       ((\<exists>r. q=2#r \<and> (p,r): step L a) | 
        (fin L p \<and> a=None \<and> q=3#start R))"
by (simp add:conc_def step_def) (blast)

lemma False_step_conc[iff]:
 "\<And>L R. (3#p,q) : step (conc L R) a = 
       (\<exists>r. q = 3#r \<and> (p,r) : step R a)"
by (simp add:conc_def step_def) (blast)

(** False in epsclosure **)

lemma lemma1b':
 "(tp,tq) : (eps(conc L R))\<^sup>* \<Longrightarrow>  
  (\<And>p. tp = 3#p \<Longrightarrow>  \<exists>q. (p,q) : (eps R)\<^sup>* \<and> tq = 3#q)"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma2b':
 "(p,q) : (eps R)\<^sup>* \<Longrightarrow>  (3#p, 3#q) : (eps(conc L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma False_epsclosure_conc[iff]:
 "((3 # p, q) : (eps (conc L R))\<^sup>*) = 
 (\<exists>r. q = 3 # r \<and> (p, r) : (eps R)\<^sup>*)"
apply (rule iffI)
apply (blast dest: lemma1b')
apply (blast dest: lemma2b')
done

(** False in steps **)

lemma False_steps_conc[iff]:
 "\<And>p. (3#p,q): steps (conc L R) w = (\<exists>r. q=3#r \<and> (p,r): steps R w)"
apply (induct "w")
apply (simp)
apply (simp)
apply (fast)  (*MUCH faster than blast*)
done

(** True in epsclosure **)

lemma True_True_eps_concI:
 "(p,q): (eps L)\<^sup>* \<Longrightarrow>  (2#p,2#q) : (eps(conc L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma True_True_steps_concI:
 "\<And>p. (p,q) : steps L w \<Longrightarrow>  (2#p,2#q) : steps (conc L R) w"
apply (induct "w")
apply (simp add: True_True_eps_concI)
apply (simp)
apply (blast intro: True_True_eps_concI)
done

lemma lemma1a':
 "(tp,tq) : (eps(conc L R))\<^sup>* \<Longrightarrow>  
 (\<And>p. tp = 2#p \<Longrightarrow>  
  (\<exists>q. tq = 2#q \<and> (p,q) : (eps L)\<^sup>*) | 
  (\<exists>q r. tq = 3#q \<and> (p,r):(eps L)\<^sup>* \<and> fin L r \<and> (start R,q) : (eps R)\<^sup>*))"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma2a':
 "(p, q) : (eps L)\<^sup>* \<Longrightarrow>  (2#p, 2#q) : (eps(conc L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lem:
 "\<And>L R. (p,q) : step R None \<Longrightarrow>  (3#p, 3#q) : step (conc L R) None"
by(simp add: conc_def step_def)

lemma lemma2b'':
 "(p,q) : (eps R)\<^sup>* \<Longrightarrow>  (3#p, 3#q) : (eps(conc L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (drule lem)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma True_False_eps_concI:
 "\<And>L R. fin L p \<Longrightarrow>  (2#p, 3#start R) : eps(conc L R)"
by(simp add: conc_def step_def)

lemma True_epsclosure_conc[iff]:
 "((2#p,q) \<in> (eps(conc L R))\<^sup>*) = 
 ((\<exists>r. (p,r) \<in> (eps L)\<^sup>* \<and> q = 2#r) \<or>
  (\<exists>r. (p,r) \<in> (eps L)\<^sup>* \<and> fin L r \<and>
        (\<exists>s. (start R, s) \<in> (eps R)\<^sup>* \<and> q = 3#s)))"
apply (rule iffI)
 apply (blast dest: lemma1a')
apply (erule disjE)
 apply (blast intro: lemma2a')
apply (clarify)
apply (rule rtrancl_trans)
apply (erule lemma2a')
apply (rule converse_rtrancl_into_rtrancl)
apply (erule True_False_eps_concI)
apply (erule lemma2b'')
done

(** True in steps **)

lemma True_steps_concD[rule_format]:
 "\<forall>p. (2#p,q) : steps (conc L R) w \<longrightarrow> 
     ((\<exists>r. (p,r) : steps L w \<and> q = 2#r)  \<or>
      (\<exists>u v. w = u@v \<and> (\<exists>r. (p,r) \<in> steps L u \<and> fin L r \<and>
              (\<exists>s. (start R,s) \<in> steps R v \<and> q = 3#s))))"
apply (induct "w")
apply (simp)
apply (simp)
apply (clarify del: disjCI)
apply (erule disjE)
apply (clarify del: disjCI)
apply (erule disjE)
apply (clarify del: disjCI)
apply (erule allE, erule impE, assumption)
apply (erule disjE)
apply (blast)
apply (rule disjI2)
apply (clarify)
apply (simp)
apply (rule_tac x = "a#u" in exI)
apply (simp)
apply (blast)
apply (blast)
apply (rule disjI2)
apply (clarify)
apply (simp)
apply (rule_tac x = "[]" in exI)
apply (simp)
apply (blast)
done

lemma True_steps_conc:
 "(2#p,q) \<in> steps (conc L R) w = 
 ((\<exists>r. (p,r) \<in> steps L w \<and> q = 2#r)  | 
  (\<exists>u v. w = u@v \<and> (\<exists>r. (p,r) : steps L u \<and> fin L r \<and> 
          (\<exists>s. (start R,s) : steps R v \<and> q = 3#s))))"
by (blast dest: True_steps_concD
    intro: True_True_steps_concI in_steps_epsclosure)

(** starting from the start **)

lemma start_conc:
  "\<And>L R. start(conc L R) = 2#start L"
by (simp add: conc_def)

lemma final_conc:
 "\<And>L R. fin(conc L R) p = (\<exists>s. p = 3#s \<and> fin R s)"
by (simp add:conc_def split: list.split)

lemma accepts_conc:
 "accepts (conc L R) w = (\<exists>u v. w = u@v \<and> accepts L u \<and> accepts R v)"
  apply (simp add: accepts_def True_steps_conc final_conc start_conc)
  by fastforce

(******************************************************)
(*                       star                         *)
(******************************************************)

lemma True_in_eps_star[iff]:
 "\<And>A. (2#p,q) \<in> eps(star A) = 
     ( (\<exists>r. q = 2#r \<and> (p,r) \<in> eps A) \<or> (fin A p \<and> q = 2#start A) )"
by (simp add:star_def step_def) (blast)

lemma True_True_step_starI:
  "\<And>A. (p,q) : step A a \<Longrightarrow>  (2#p, 2#q) : step (star A) a"
by (simp add:star_def step_def)

lemma True_True_eps_starI:
  "(p,r) : (eps A)\<^sup>* \<Longrightarrow>  (2#p, 2#r) : (eps(star A))\<^sup>*"
apply (induct rule: rtrancl_induct)
apply (blast)
apply (blast intro: True_True_step_starI rtrancl_into_rtrancl)
done

lemma True_start_eps_starI:
 "\<And>A. fin A p \<Longrightarrow>  (2#p,2#start A) : eps(star A)"
by (simp add:star_def step_def)

lemma lem':
 "(tp,s) : (eps(star A))\<^sup>* \<Longrightarrow>  (\<forall>p. tp = 2#p \<longrightarrow>
 (\<exists>r. ((p,r) \<in> (eps A)\<^sup>* \<or>
        (\<exists>q. (p,q) \<in> (eps A)\<^sup>* \<and> fin A q \<and> (start A,r) : (eps A)\<^sup>*)) \<and> 
       s = 2#r))"
apply (induct rule: rtrancl_induct)
apply (simp)
apply (clarify)
apply (simp)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma True_eps_star[iff]:
 "((2#p,s) \<in> (eps(star A))\<^sup>*) = 
 (\<exists>r. ((p,r) \<in> (eps A)\<^sup>* \<or>
        (\<exists>q. (p,q) : (eps A)\<^sup>* \<and> fin A q \<and> (start A,r) : (eps A)\<^sup>*)) \<and>
       s = 2#r)"
apply (rule iffI)
apply (drule lem')
apply (blast)
(* Why can't blast do the rest? *)
apply (clarify)
apply (erule disjE)
apply (erule True_True_eps_starI)
apply (clarify)
apply (rule rtrancl_trans)
apply (erule True_True_eps_starI)
apply (rule rtrancl_trans)
apply (rule r_into_rtrancl)
apply (erule True_start_eps_starI)
apply (erule True_True_eps_starI)
done

(** True in step Some **)

lemma True_step_star[iff]:
 "\<And>A. (2#p,r) \<in> step (star A) (Some a) =
     (\<exists>q. (p,q) \<in> step A (Some a) \<and> r=2#q)"
by (simp add:star_def step_def) (blast)


(** True in steps **)

(* reverse list induction! Complicates matters for conc? *)
lemma True_start_steps_starD[rule_format]:
 "\<forall>rr. (2#start A,rr) \<in> steps (star A) w \<longrightarrow>
 (\<exists>us v. w = concat us @ v \<and>
             (\<forall>u\<in>set us. accepts A u) \<and>
             (\<exists>r. (start A,r) \<in> steps A v \<and> rr = 2#r))"
apply (induct w rule: rev_induct)
apply (simp)
apply (clarify)
apply (rule_tac x = "[]" in exI)
apply (erule disjE)
apply (simp)
apply (clarify)
apply (simp)
apply (simp add: O_assoc[symmetric] epsclosure_steps)
apply (clarify)
apply (erule allE, erule impE, assumption)
apply (clarify)
apply (erule disjE)
apply (rule_tac x = "us" in exI)
apply (rule_tac x = "v@[x]" in exI)
apply (simp add: O_assoc[symmetric] epsclosure_steps)
apply (blast)
apply (clarify)
apply (rule_tac x = "us@[v@[x]]" in exI)
apply (rule_tac x = "[]" in exI)
apply (simp add: accepts_def)
apply (blast)
done

lemma True_True_steps_starI:
  "\<And>p. (p,q) : steps A w \<Longrightarrow>  (2#p,2#q) : steps (star A) w"
apply (induct "w")
apply (simp)
apply (simp)
apply (blast intro: True_True_eps_starI True_True_step_starI)
done

lemma steps_star_cycle:
 "(\<forall>u \<in> set us. accepts A u) \<Longrightarrow> 
 (2#start A,2#start A) \<in> steps (star A) (concat us)"
apply (induct "us")
apply (simp add:accepts_def)
apply (simp add:accepts_def)
by(blast intro: True_True_steps_starI True_start_eps_starI in_epsclosure_steps)

(* Better stated directly with start(star A)? Loop in star A back to start(star A)?*)
lemma True_start_steps_star:
 "(2#start A,rr) : steps (star A) w = 
 (\<exists>us v. w = concat us @ v \<and>
             (\<forall>u\<in>set us. accepts A u) \<and>
             (\<exists>r. (start A,r) \<in> steps A v \<and> rr = 2#r))"
apply (rule iffI)
apply (erule True_start_steps_starD)
apply (clarify)
apply (blast intro: steps_star_cycle True_True_steps_starI)
done

(** the start state **)

lemma start_step_star[iff]:
  "\<And>A. (start(star A),r) : step (star A) a = (a=None \<and> r = 2#start A)"
by (simp add:star_def step_def)

lemmas epsclosure_start_step_star =
  in_unfold_rtrancl2[where ?p = "start (star A)"] for A

lemma start_steps_star:
 "(start(star A),r) : steps (star A) w = 
 ((w=[] \<and> r= start(star A)) | (2#start A,r) : steps (star A) w)"
apply (rule iffI)
apply (case_tac "w")
apply (simp add: epsclosure_start_step_star)
apply (simp)
apply (clarify)
apply (simp add: epsclosure_start_step_star)
apply (blast)
apply (erule disjE)
apply (simp)
apply (blast intro: in_steps_epsclosure)
done

lemma fin_star_True[iff]: "\<And>A. fin (star A) (2#p) = fin A p"
by (simp add:star_def)

lemma fin_star_start[iff]: "\<And>A. fin (star A) (start(star A))"
by (simp add:star_def)

(* too complex! Simpler if loop back to start(star A)? *)
lemma accepts_star:
 "accepts (star A) w = 
 (\<exists>us. (\<forall>u \<in> set(us). accepts A u) \<and> (w = concat us))"
apply(unfold accepts_def)
apply (simp add: start_steps_star True_start_steps_star)
apply (rule iffI)
apply (clarify)
apply (erule disjE)
apply (clarify)
apply (simp)
apply (rule_tac x = "[]" in exI)
apply (simp)
apply (clarify)
apply (rule_tac x = "us@[v]" in exI)
apply (simp add: accepts_def)
apply (blast)
apply (clarify)
apply (rule_tac xs = "us" in rev_exhaust)
apply (simp)
apply (blast)
apply (clarify)
apply (simp add: accepts_def)
apply (blast)
done


(***** Correctness of r2n *****)
lemma accepts_rexp2nae:
 "\<And>w. accepts (rexp2nae r (transform ` v)) w = (w : lang r v)"
apply (induct "r")
apply (simp add: accepts_def)
apply simp
apply (simp add: accepts_atom)
apply (simp add: accepts_or)
apply (simp add: accepts_conc Regular_Set.conc_def)
apply (simp add: accepts_star in_star_iff_concat subset_iff Ball_def)
apply(simp add:accepts_dot)
apply blast
apply (metis Un_iff accepts_epsilon accepts_or lang.simps(8) rexp2nae.simps(8) singleton_iff)
apply (simp add: accepts_conc Regular_Set.conc_def accepts_star in_star_iff_concat subset_iff Ball_def)
   apply(simp add:accepts_inter)
  sorry
 done

end