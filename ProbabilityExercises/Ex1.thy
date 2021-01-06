theory Ex1
imports "HOL-Probability.Probability" "HOL-Library.Permutation"
begin

(*
Let @term{{ X\<^sub>n : n \<ge> 1 }} be IID random variables taking integer values. Let S\<^sub>0=0, S\<^sub>n = \<Sum>\<^sup>n\<^sub>i\<^sub>=\<^sub>1 X\<^sub>i.
The range R\<^sub>i of S\<^sub>0, ... , S\<^sub>n is the number of distinct values taken by the sequence.
Show that P(R\<^sub>n = R\<^sub>n\<^sub>-\<^sub>1 + 1) = P( S\<^sub>1 * .. * S\<^sub>n ) 

Challenge here is to write Isabelle that follows the above description of the problem.

Can we? Instead it is much easier to write it in a monadic style?

PMF for S_i

pmf_walk :: nat \<Rightarrow> (int list) pmf
pmf_walk 0 = pmf where 0 has prob 1
pmf_walk n = do {
             w <- pmf_walk (n-1) 
             s <- pmf_step 
             return w+s
}

pmf_range n = do {
              w <- pmf_walk n
              return (length distinct w)
   }

proof 
   w <- pmf_range n
   rn <- pmf_range n
   rm <- pmf_range n-1
   prob (rn = rm + 1) = prob (mult w \<noteq> 0)
       
    

*)

sledgehammer_params[debug=true,timeout=600]

locale walk =
  fixes pmf_step :: "int pmf"
begin



fun pmf_steps :: "nat \<Rightarrow> (int list) pmf" where
"pmf_steps 0 = return_pmf []"
| "pmf_steps (Suc n) = do {
          s  \<leftarrow> pmf_step;
          ss  \<leftarrow> pmf_steps n;
          return_pmf (s#ss)
}"

lemma pmf_zero_steps_one: "pmf_steps 0 { [] } = 1"
  using pmf_steps.simps by auto

lemma pmf_zero_steps_zero:
  assumes "\<forall>x \<in> xs. length x > 0" 
  shows "pmf_steps 0 xs = 0"
  using pmf_steps.simps pmf_zero_steps_one assms emeasure_pmf  by auto

(*

lemma 
  assumes "\<exists>x \<in> xs. length x \<noteq> n"
  shows "pmf_steps n xs = 0"
using assms proof(induct n)
  case 0
  then show ?case using pmf_zero_steps_zero 
next
  case (Suc n)
  then show ?case using pmf_steps.simps 
qed
*)

definition "cons_pmf A B = bind_pmf A  (\<lambda>x. bind_pmf B (\<lambda>xs. return_pmf (x#xs)))"

lemma pmf_cons: "pmf (cons_pmf M N) (a#b) = pmf M a * pmf N b"
  unfolding cons_pmf_def pmf_bind pmf_return
  apply (subst integral_measure_pmf_real[where A="{b}"])
  apply (auto simp: indicator_eq_0_iff)
  apply (subst integral_measure_pmf_real[where A="{a}"])
  apply (auto simp: indicator_eq_0_iff sum_nonneg_eq_0_iff pmf_nonneg)
  done

thm cons_pmf_def

abbreviation mult_list :: "int list \<Rightarrow> int" where
  "mult_list xs \<equiv> fold (*) xs (1::int)"

abbreviation prob where
  "prob \<equiv> measure_pmf.prob"

lemma pmf_steps_Cons:
  fixes xs::"int list"
  assumes "length xs = n" 
  shows "prob (pmf_steps (n+1)) {x#xs} = (prob pmf_step {x})  * (prob (pmf_steps n) {xs})"
proof -
  have "pmf_steps (n+1) =  cons_pmf pmf_step (pmf_steps n)"
    using pmf_steps.simps cons_pmf_def 
    by (metis Suc_eq_plus1)
  hence "pmf (pmf_steps (n+1)) (x#xs) = pmf pmf_step x * pmf (pmf_steps n) xs"
    using pmf_cons by metis
  thm measure_pmf_single
  thus ?thesis using pmf_def map_fun_def measure_def 
    by (metis measure_pmf_single)
  hence "pmf_steps (n+1) {x#xs} =  emeasure (measure_pmf (pmf_step \<bind> (\<lambda>s. pmf_steps n \<bind> (\<lambda>ss. return_pmf (s # ss))))) {x#xs} "
    by auto
qed

thm foldr.simps foldl.simps

lemma fold_fun:
  "g (f x)  (foldr g (list.map f xs) y) = foldr g (list.map f (x#xs)) y"
proof(induct xs)
  case Nil
  then show ?case by auto
next
  case (Cons x' xs')
  then show ?case using foldr.simps by auto
qed

thm perm.induct

lemma foldr_mult_perm:
  fixes xs::"'a :: comm_semiring_1 list"
  assumes "perm xs xs'"
  shows "foldr (*) xs 1 = foldr (*) xs' 1"
  using assms apply(induct rule: perm.inducts,auto)  
  by (simp add: mult.left_commute)



(*
 lemma measure_prob_cong_0:
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> pmf p x = 0"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> pmf p x = 0"
  shows   "measure (measure_pmf p) A = measure (measure_pmf p) B"
proof -
  have "measure_pmf.prob p A = measure_pmf.prob p (A \<inter> set_pmf p)"
    by (simp add: measure_Int_set_pmf)
  also have "A \<inter> set_pmf p = B \<inter> set_pmf p"
    using assms by (auto simp: set_pmf_eq)
  also have "measure_pmf.prob p \<dots> = measure_pmf.prob p B"
    by (simp add: measure_Int_set_pmf)
  finally show ?thesis .
qed
*)
(* Could just define pmf_steps to be this *)
lemma pmf_steps_foldr:
  assumes "length xs = n"
  shows "prob (pmf_steps n) {xs} = foldr (*) (list.map (\<lambda>x. prob pmf_step {x}) xs) 1"
  using assms proof(induct n arbitrary: xs)
  case 0
  then show ?case by auto
next
  case (Suc n')
  then obtain x' and xs' where *:"xs = x'#xs'" using list.distinct  by (metis length_Suc_conv)
  then have "prob (pmf_steps (Suc n')) {x'#xs'} = (prob pmf_step {x'})  * (prob (pmf_steps n') {xs'})" using pmf_steps_Cons Suc by auto
  also have "... = prob pmf_step {x'} * (foldr (*) (list.map (\<lambda>x. prob pmf_step {x}) xs') 1)" using * Suc by auto
  also have "... = (foldr (*) (list.map (\<lambda>x. prob pmf_step {x}) (x'#xs')) 1)" using fold_fun by metis
  finally show ?case using fold.simps * by simp
qed

lemma perm_map:
  assumes "perm xs xs'" 
  shows "perm (map f xs) (map f xs')"
using assms by(induct rule: perm.inducts,auto)

lemma pmf_steps_perm_prob_eq:
  fixes xs::"int list"
  assumes "length xs = n" and "perm xs xs'"
  shows  "prob (pmf_steps n) {xs} = prob (pmf_steps n) {xs'}"
proof -
  have "prob (pmf_steps n) {xs} = foldr (*) (list.map (\<lambda>x. prob pmf_step {x}) xs) 1" using pmf_steps_foldr assms by simp
  also have "... =  foldr (*) (list.map (\<lambda>x. prob pmf_step {x}) xs') 1" 
    using assms perm_map[THEN foldr_mult_perm, where f1="(\<lambda>x. prob pmf_step {x})"] by auto
  finally show ?thesis using pmf_steps_foldr perm_length assms by metis
qed



lemma pmf_steps_rev_prob_eq:
  assumes "length xs = n"
  shows  "prob (pmf_steps n) {xs} = prob (pmf_steps n) {rev xs}"
proof -
  have "perm xs (rev xs)"  by (simp add: perm_rev perm_sym)
  thus ?thesis using pmf_steps_perm_prob_eq assms by auto
qed



(* should be easy as can reverse * and pmf are additive over set - in fact holds for any permutation of list *)
lemma 
  assumes "xss \<noteq> {}" and "\<forall>x \<in> xss. length x = n"
  shows  "prob (pmf_steps n) xss = prob (pmf_steps n) (rev ` xss)"
  using assms pmf_steps_rev_prob_eq sorry
(*
using assms proof(induct n arbitrary: xss)
  case 0
  then show ?case by auto   
next
  case (Suc n)
  then show ?case using pmf_steps.simps 
qed
*)
value "prefixes [1,2,3::int]"

abbreviation sum_list :: "int list \<Rightarrow> int" where
  "sum_list xs \<equiv> fold (+) xs (0::int)"

abbreviation walk_of :: "int list \<Rightarrow> int list" where
 "walk_of xs \<equiv> map sum_list (prefixes xs)"

abbreviation walk_of2 :: "int list \<Rightarrow> int list" where
 "walk_of2 xs \<equiv> map (\<lambda>n. (\<Sum>j\<in>{0..<n}. (xs!j))) [0..<length xs+1]"


value "prefixes [1,2,3::nat]"

thm prefixes_snoc

value "walk_of [-1,-2]"

lemma walk_of_snoc:
  "walk_of (xs@[x]) = (walk_of xs) @ [ last (walk_of xs) + x ]"
proof(induct xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x' xs')
  then show ?case using prefixes_snoc sorry
qed 


lemma "walk_of xs = map (\<lambda>n. (\<Sum>j\<in>{0..<n}. (xs!j))) [0..<length xs+1]"
proof(induct xs rule: rev_induct) 
  case Nil
  then show ?case by auto
next
  case (snoc  x' xs')
  let ?w = "map (\<lambda>n. (\<Sum>j\<in>{0..<n}. (xs'!j))) [0..<length xs'+1]"
  have "walk_of (xs'@[x']) = (walk_of xs') @ [ last (walk_of xs') + x' ]"
    using walk_of_snoc by metis
  also have "... = ?w @ [ last ?w + x' ]" using snoc by simp
  also have "... = map (\<lambda>n. (\<Sum>j\<in>{0..<n}. ((xs'@[x'])!j))) [0..<length (xs'@[x'])+1]" 
    using snoc sorry
  finally show ?case by auto
(*  show  "walk_of (xs'@[x']) =  map (\<lambda>n. (\<Sum>j\<in>{0..<n}. ((xs'@[x'])!j))) [0..<length (xs'@[x'])+1]" sorry*)
qed  

value "walk_of [1,2,4]"


abbreviation range_of :: "int list \<Rightarrow> nat" where
  "range_of xs \<equiv> length (remdups xs)"

abbreviation ranges_of :: "int list \<Rightarrow> nat list" where
  "ranges_of xs \<equiv> drop 1 (map range_of (prefixes xs))"

value "range_of (walk_of [1,2,2])"
value "prefixes (walk_of [1,2,2])"
value "ranges_of (walk_of [1,2,-2])"

abbreviation steps_non_zero :: "int list \<Rightarrow> bool" where
  "steps_non_zero xs \<equiv> (mult_list (drop 1 (walk_of xs)) \<noteq> 0)"

value "steps_non_zero [1,2,-2,-1]"

(*
abbreviation drop_last :: "'a list \<Rightarrow> 'a list" where
  "drop_last xs \<equiv> take ((length xs) - 1) xs" 

value "drop_last [1,2,3]::(nat list)"
*)


abbreviation range_inc :: "int list \<Rightarrow> bool" where
  "range_inc xs \<equiv> (let rn = range_of (walk_of xs) in 
                   let rns = range_of (butlast (walk_of xs)) in
                   rn = rns + 1)"

value "range_of [1,2,-2]"

value "range_inc [1,2,-2,-2]"

value "walk_of [- 2, 0]"

value "range_of (walk_of [- 2, 0])"
value "range_of (walk_of [-2])"

value "steps_non_zero [- 2, 0]"
value "range_inc [- 2, 0]"





lemma butlast_append_last_eq:
  assumes "length xs > 0"
  shows   "(butlast xs)  @ [last xs] = xs"
using assms proof(induct xs)
  case Nil
  then show ?case by auto
next
  case (Cons x' xs')
  then show ?case by auto
qed

lemma  last_remdups:
  assumes "last xs \<in> set (butlast xs)" and "length xs > 0"
  shows "set (remdups xs) = set (remdups (butlast xs))"
  using assms apply(induct xs,simp)  
  by (metis ex1.butlast_append_last_eq remdups.simps(2) rotate1.simps(2) set_remdups set_rotate1)

value "walk_of [-1]"
value "range_inc [- 1]"

lemma range_inc_neq:
  assumes "range_inc xs"
  shows "\<forall>i \<in> { 0..<(length xs)}. last (walk_of xs) \<noteq> (walk_of xs)!i"
proof 
  fix i
  assume as:"i \<in> { 0..<(length xs)}"
  show "last (walk_of xs) \<noteq> (walk_of xs)!i" proof
    assume *: "last (walk_of xs) = (walk_of xs)!i"

    have "range_of (walk_of xs) =  range_of (butlast (walk_of xs))" proof -
      have "length (walk_of xs) = length xs + 1" by auto
      hence "i < length (walk_of xs) - 1" using as by simp
      hence "(walk_of xs)!i \<in> set (butlast (walk_of xs))" using butlast.simps 
        by (metis in_set_conv_nth length_butlast nth_butlast)
      hence "last (walk_of xs) \<in> set (butlast (walk_of xs)) \<and> 0 < length (walk_of xs)" using * by simp
      hence "set (remdups  (walk_of xs)) = set (remdups (butlast (walk_of xs)))"  using * as last_remdups by metis
      hence "length (remdups  (walk_of xs)) = length (remdups (butlast (walk_of xs)))"
        by (metis card'_code(1) set_remdups)
      thus ?thesis by simp
    qed      
    thus False using assms by auto
  qed
qed

value "walk_of [-1]"

lemma xx:
  assumes "i \<in> { 1..length xs}"
  shows "(walk_of xs)!i = xs!(i-1) + (walk_of xs)!(i-1)"
  using assms proof(induct xs)
case Nil
  then show ?case by auto
next
  case (Cons x' xs')
  then show ?case sledgehammer
qed

lemma range_inc_neq2:
  assumes "range_inc xs" and "i \<in> { 0..<(length xs)}" and "last (walk_of xs) \<noteq> (walk_of xs)!i"
  shows "(\<Sum> j \<in> {i..length xs}. (xs!j)) \<noteq> 0"
proof - 
  have "(walk_of xs)!i = 
  
  using assms sledgehammer

(*}
  thus ?thesis using list_all_simps

  case Nil
  then show ?case by auto
next
  case (Cons x' xs')

  have "last_of (walk_of (x'#xs')) \<noteq> x'" sorry
  moreover have "list_all (\<lambda>s. last_of (walk_of (x'#xs')) \<noteq> s) (drop_last (walk_of (xs')))" sorry 
  ultimately have "list_all (\<lambda>s. last_of (walk_of (x'#xs')) \<noteq> s) (x'#(drop_last (walk_of (xs'))))" by auto

  thus ?case 
(*"list_all (\<lambda>s. last_of (walk_of (x'#xs')) \<noteq> s) (drop_last (walk_of (x'#xs')))"*)
  

(*  have "list_all (\<lambda>s. last_of (walk_of xs) \<noteq> s) (drop_last (walk_of xs)) =
            (last_of (walk_of (x'xxs) \<noteq> x') \<and> list_all (\<lambda>s. last_of (walk_of xs') \<noteq> s) (drop_last (walk_of xs'))"

  have "range_inc xs' \<Longrightarrow>  list_all (\<lambda>s. last_of (walk_of xs') \<noteq> s) (drop_last (walk_of xs'))"
  have "length (walk_of xs') > 0" by auto
  then obtain ls where "ls = last_of (walk_of xs')" using last_of.simps by simp
  
  then show ?case *)
qed
*)

lemma 
  shows "prob (pmf_steps n) { xs . length xs = n \<and> range_inc xs } = prob (pmf_steps n) { xs . length xs = n \<and> steps_non_zero xs }"
proof -
  fix xs
  assume "length xs = n" and "range_inc xs"
  have "list_all (\<lambda>s. last_of (walk_of xs) \<noteq> s) (drop_last (walk_of xs))"
(*
lemma "steps_non_zero xs = range_inc xs"


lemma "{xs . steps_non_zero xs } = { xs. range_inc xs }"
proof -
  have "{xs . steps_non_zero xs } \<subseteq> { xs. range_inc xs }" 
  proof -    
    fix xs 
    assume "steps_non_zero xs"
    have "range_inc xs" sorry
  *)  
    
(*
  

fun pmf_walk :: "nat \<Rightarrow> (int list) pmf" where
"pmf_walk 0 = return_pmf [0]"
| "pmf_walk n = do { 
          w \<leftarrow> pmf_walk (n-1);
          case w of 
               (w#ws) \<Rightarrow> do { 
                              s \<leftarrow> pmf_step;
                              return_pmf ((s+w)#w#ws)
                        }
              | _ \<Rightarrow> return_pmf [0]
}" 




fun pmf_lhs :: "nat \<Rightarrow> bool pmf" where
"pmf_lhs 0 = return_pmf True"
|  "pmf_lhs n = do { 
         w \<leftarrow> pmf_walk n;
         s0 \<leftarrow> return_pmf (((mult_list w) = (0::int)));
         s1 \<leftarrow> return_pmf ((range_of w) = ((range_of (tl w)) + (1::int)));
         return_pmf (s0 =  s1)
}"
*)


