theory Ex01
 imports Main "~~/src/HOL/Library/Tree" 
 begin

declare Let_def [simp]


section "BST Search and Insertion"

fun isin :: "('a ::linorder) tree => 'a => bool" where
"isin Leaf x = False"|
"isin (Node l a r) x = 
    (if x< a then isin l x else 
    if x > a then isin r x 
    else True)"

fun ins ::"'a::linorder => 'a tree => 'a tree" where 
"ins x Leaf = Node Leaf x Leaf" | 
"ins x (Node l a r) = 
    (if x < a then Node (ins x l) a r else 
    if x > a then Node l a (inx x r) else 
    Node l a r)"


lemma set_tess_isin: "bst t \<Longrightarrow> isin t x = (x \<in> set_tree t)"
apply(induct t)
apply auto
done

lemma set_tess_ins:"set_tree (ins x t) = {x} \<union> set_tree t"
apply(induct t)
apply auto
done

lemma bst_ins: "bst t\<Longrightarrow> bst (ins x t)"
apply(induct t)
apply (auto simp:set_tess_isin)
done




value "2 + (2::nat)"

value "(2::nat)  * (5 + 3)"

value "(3::int) * 4 - 2 * (7 + 1 )"

fun count ::"'a list => 'a => nat" where 
"count [] a = 0"|
"count (x # xs ) a = 
(if x = a then 1 + count xs a else count xs a)"


theorem "count xs a \<le>  length xs" 
    apply(induct xs)
    subgoal 
    apply simp 
    done 
    apply (subst count.simps)
    apply (subst list.size)
    apply simp
    done

lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ []\<rbrakk> \<Longrightarrow> ys = zs"
    apply simp
    done

declare algebra_simps [simp]

lemma "(a+b)*(a-b)=a*a-b*(b::int)"
    by simp
end 